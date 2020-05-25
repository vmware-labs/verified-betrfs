include "BucketGeneratorModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"

module BucketGeneratorImpl {
  import opened BucketImpl
  import BucketGeneratorModel
  import BucketIteratorModel
  import opened Lexicographic_Byte_Order_Impl
  import opened ValueMessage
  import opened NativeTypes
  import UI

  class Generator {
    // For BasicGenerator
    var bucket: MutBucket?;
    var it: Iterator;

    // For ComposeGenerator
    var top: Generator?;
    var bot: Generator?;
    var next: BucketIteratorModel.IteratorOutput;

    ghost var Repr: set<object>;
    ghost var ReadOnlyRepr: set<object>;
    ghost var Height: nat;

    constructor() { }

    // Question: Why is Inv marked opaque, and what's up with the reveal_Inv_for lemma?
    //
    // Answer: Typically, we mark the Inv() protected. This is because we want to
    // access Inv within the module, but the user of a class doesn't need to care
    // what's in Inv (except for the one ensures clause `this in this.Repr`).
    // This is crucial for keeping verification times reasonable.
    // 
    // This case is a bit different because the object is recursive: that is, the object
    // is a user of itself. In other words, many of the methods in this class need
    // to open up this.Inv() but not top.Inv() or bot.Inv(). Therefore, `protected`
    // doesn't cut it: we need the more fine-grained reveal lemma we use here.

    predicate {:opaque} Inv()
    reads this, this.Repr, this.ReadOnlyRepr
    decreases Height, 1
    ensures Inv() ==> this in this.Repr
    {
      Inv1()
    }

    predicate Inv1()
    reads this, this.Repr, this.ReadOnlyRepr
    decreases Height, 0
    {
      && (bucket != null ==> (
        && bucket in ReadOnlyRepr
        && Repr == {this}
        && ReadOnlyRepr == bucket.Repr
        && this !in bucket.Repr
        && bucket.Inv()
        && bucket.WFIter(it)
      ))
      && (bucket == null ==> (
        && top != null
        && bot != null
        && top in Repr
        && bot in Repr
        && Repr == {this} + top.Repr + bot.Repr
        && ReadOnlyRepr == top.ReadOnlyRepr + bot.ReadOnlyRepr
        && top.Repr !! bot.Repr
        && top.Repr !! bot.ReadOnlyRepr
        && bot.Repr !! top.ReadOnlyRepr
        && this !in top.Repr
        && this !in bot.Repr
        && this !in top.ReadOnlyRepr
        && this !in bot.ReadOnlyRepr
        && top.Height < this.Height
        && bot.Height < this.Height
        && top.Inv()
        && bot.Inv()
      ))
    }

    static lemma reveal_Inv_for(bg: Generator)
    ensures bg.Inv() == bg.Inv1()
    {
      bg.reveal_Inv();
    }

    protected function I() : BucketGeneratorModel.Generator
    requires Inv()
    reads this, this.Repr, this.ReadOnlyRepr
    decreases Height
    ensures BucketGeneratorModel.WF(I())
    {
      reveal_Inv_for(this);

      if bucket != null then (
        BucketGeneratorModel.BasicGenerator(bucket.I(), IIterator(it))
      ) else (
        BucketGeneratorModel.ComposeGenerator(top.I(), bot.I(), next)
      )
    }

    method GenLeft() returns (res : BucketIteratorModel.IteratorOutput)
    requires Inv()
    ensures res == BucketGeneratorModel.GenLeft(I())
    {
      reveal_Inv_for(this);

      if bucket != null {
        res := bucket.GetNext(it);
      } else {
        res := next;
      }
    }

    method GenPop()
    requires Inv()
    requires BucketGeneratorModel.GenLeft(I()).Next?
    modifies Repr
    ensures Inv()
    ensures I() == BucketGeneratorModel.GenPop(old(I()))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures ReadOnlyRepr == old(ReadOnlyRepr)

    decreases Height
    {
      reveal_Inv_for(this);

      BucketGeneratorModel.reveal_BasicGenPop();
      BucketGeneratorModel.reveal_MergeGenPop();
      BucketGeneratorModel.reveal_GenPop();
      if bucket != null {
        it := bucket.IterInc(it);
      } else {
        var top_next := top.GenLeft();
        var bot_next := bot.GenLeft();
        var c;
        if (top_next.Next? && bot_next.Next?) {
          c := cmp(top_next.key, bot_next.key);
        }

        if top_next.Next? && bot_next.Next? && c == 0 {
          top.GenPop();
          bot.GenPop();
          next := BucketIteratorModel.Next(top_next.key,
              Merge(top_next.msg, bot_next.msg));
        } else if top_next.Next? && (bot_next.Next? ==> c < 0) {
          top.GenPop();
          next := top_next;
        } else if bot_next.Next? {
          bot.GenPop();
          next := bot_next;
        } else {
          next := BucketIteratorModel.Done;
        }

        Repr := {this} + top.Repr + bot.Repr;
        ReadOnlyRepr := top.ReadOnlyRepr + bot.ReadOnlyRepr;
        Height := top.Height + bot.Height + 1;
      }

      assert Inv1();
      reveal_Inv_for(this);
    }

    static method GenCompose(top: Generator, bot: Generator)
    returns (g: Generator)
    requires top.Inv()
    requires bot.Inv()
    requires top.Repr !! bot.Repr
    requires top.Repr !! bot.ReadOnlyRepr
    requires bot.Repr !! top.ReadOnlyRepr
    modifies top.Repr
    modifies bot.Repr
    ensures g.Inv()
    ensures forall o | o in g.Repr :: fresh(o) || o in old(top.Repr) || o in old(bot.Repr)
    ensures top.ReadOnlyRepr == old(top.ReadOnlyRepr)
    ensures bot.ReadOnlyRepr == old(bot.ReadOnlyRepr)
    ensures g.ReadOnlyRepr == top.ReadOnlyRepr + bot.ReadOnlyRepr
    ensures g.I() == BucketGeneratorModel.GenCompose(old(top.I()), old(bot.I()))
    {
      g := new Generator();
      g.bucket := null;
      g.top := top;
      g.bot := bot;

      var top_next := top.GenLeft();
      var bot_next := bot.GenLeft();
      var c;
      if (top_next.Next? && bot_next.Next?) {
        c := cmp(top_next.key, bot_next.key);
      }

      if top_next.Next? && bot_next.Next? && c == 0 {
        top.GenPop();
        bot.GenPop();
        g.next := BucketIteratorModel.Next(top_next.key,
            Merge(top_next.msg, bot_next.msg));
      } else if top_next.Next? && (bot_next.Next? ==> c < 0) {
        top.GenPop();
        g.next := top_next;
      } else if bot_next.Next? {
        bot.GenPop();
        g.next := bot_next;
      } else {
        g.next := BucketIteratorModel.Done;
      }

      g.Repr := {g} + g.top.Repr + g.bot.Repr;
      g.ReadOnlyRepr := g.top.ReadOnlyRepr + g.bot.ReadOnlyRepr;
      g.Height := g.top.Height + g.bot.Height + 1;

      assert g.Inv1();
      reveal_Inv_for(g);
      BucketGeneratorModel.reveal_GenCompose();
    }

    static method GenFromBucketWithLowerBound(bucket: MutBucket, start: UI.RangeStart)
    returns (g: Generator)
    requires bucket.Inv()
    ensures g.Inv()
    ensures fresh(g.Repr)
    ensures g.ReadOnlyRepr == bucket.Repr
    ensures g.I() == BucketGeneratorModel.GenFromBucketWithLowerBound(bucket.I(), start)
    {
      g := new Generator();
      g.bucket := bucket;

      match start {
        case SExclusive(key) => {
          g.it := bucket.IterFindFirstGt(key);
        }
        case SInclusive(key) => {
          g.it := bucket.IterFindFirstGte(key);
        }
        case NegativeInf => {
          g.it := bucket.IterStart();
        }
      }

      g.Repr := {g};
      g.ReadOnlyRepr := bucket.Repr;

      assert g.Inv1();
      reveal_Inv_for(g);
      BucketGeneratorModel.reveal_GenFromBucketWithLowerBound();
    }

    static method GenFromBucketStackWithLowerBound(buckets: seq<MutBucket>, start: UI.RangeStart)
    returns (g: Generator)
    requires forall i | 0 <= i < |buckets| :: buckets[i].Inv()
    requires |buckets| >= 1
    requires |buckets| < 0x1_0000_0000_0000_0000
    decreases |buckets|
    ensures g.Inv()
    ensures fresh(g.Repr)
    ensures g.ReadOnlyRepr == MutBucket.ReprSeq(buckets)
    ensures g.I() == BucketGeneratorModel.GenFromBucketStackWithLowerBound(
        MutBucket.ISeq(buckets), start)
    {
      MutBucket.AllocatedReprSeq(buckets);

      if |buckets| as uint64 == 1 {
        g := GenFromBucketWithLowerBound(buckets[0 as uint64], start);

        MutBucket.ReprSeq1Eq(buckets);
      } else {
        var mid := |buckets| as uint64 / 2;

        MutBucket.AllocatedReprSeq(buckets[..mid]);
        MutBucket.AllocatedReprSeq(buckets[mid..]);

        var g1 := GenFromBucketStackWithLowerBound(buckets[..mid], start);
        var g2 := GenFromBucketStackWithLowerBound(buckets[mid..], start);
        g := GenCompose(g1, g2);

        assert buckets[..mid] + buckets[mid..] == buckets;
        MutBucket.ReprSeqAdditive(buckets[..mid], buckets[mid..]);
        MutBucket.ISeqAdditive(buckets[..mid], buckets[mid..]);
      }

      BucketGeneratorModel.reveal_GenFromBucketStackWithLowerBound();
    }

  }
}
