include "../PivotBetree/BucketGenerator.i.dfy"
include "MutableBucket.i.dfy"

module ImplBucketGenerator {
  import opened MutableBucket
  import ModelBucketGenerator = BucketGenerator
  import ModelBucketIterator = BucketIterator
  import opened Lexicographic_Byte_Order
  import opened ValueMessage

  class BucketGenerator {
    // For BasicGenerator
    var bucket: MutBucket?;
    var it: Iterator;

    // For ComposeGenerator
    var top: BucketGenerator?;
    var bot: BucketGenerator?;
    var next: ModelBucketIterator.IteratorOutput;

    ghost var Repr: set<object>;
    ghost var ReadOnlyRepr: set<object>;
    ghost var Height: nat;

    constructor() { assume false; }

    protected predicate Inv()
    reads this, this.Repr, this.ReadOnlyRepr
    decreases Height
    ensures Inv() ==> this in this.Repr
    {
      && (bucket != null ==> (
        && bucket in Repr
        && Repr == {this}
        && ReadOnlyRepr == bucket.Repr
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

    protected function I() : ModelBucketGenerator.Generator
    requires Inv()
    reads this, this.Repr, this.ReadOnlyRepr
    decreases Height
    ensures ModelBucketGenerator.WF(I())
    {
      if bucket != null then (
        ModelBucketGenerator.BasicGenerator(bucket.I(), IIterator(it))
      ) else (
        ModelBucketGenerator.ComposeGenerator(top.I(), bot.I(), next)
      )
    }

    method GenLeft() returns (res : ModelBucketIterator.IteratorOutput)
    requires Inv()
    ensures res == ModelBucketGenerator.GenLeft(I())
    {
      if bucket != null {
        res := bucket.GetNext(it);
      } else {
        res := next;
      }
    }

    method GenPop()
    requires Inv()
    requires ModelBucketGenerator.GenLeft(I()).Next?
    modifies Repr
    ensures Inv()
    ensures I() == ModelBucketGenerator.GenPop(old(I()))
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures ReadOnlyRepr == old(ReadOnlyRepr)

    decreases Height
    {
      ModelBucketGenerator.reveal_BasicGenPop();
      ModelBucketGenerator.reveal_MergeGenPop();
      ModelBucketGenerator.reveal_GenPop();
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
          next := ModelBucketIterator.Next(top_next.key,
              Merge(top_next.msg, bot_next.msg));
        } else if top_next.Next? && (bot_next.Next? ==> c < 0) {
          top.GenPop();
          next := top_next;
        } else if bot_next.Next? {
          bot.GenPop();
          next := bot_next;
        } else {
          next := ModelBucketIterator.Done;
        }

        Repr := {this} + top.Repr + bot.Repr;
        ReadOnlyRepr := top.ReadOnlyRepr + bot.ReadOnlyRepr;
        Height := top.Height + bot.Height + 1;
      }
    }
  }
}
