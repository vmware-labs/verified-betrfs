include "BucketGeneratorModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"

module BucketGeneratorImpl {
  import opened BucketImpl
  import BucketGeneratorModel
  import BucketIteratorModel
  import opened Lexicographic_Byte_Order_Impl
  import opened ValueMessage
  import opened NativeTypes
  import opened LinearSequence_s
  import opened LinearSequence_i
  import UI
  import opened BucketsLib
  import opened Lexicographic_Byte_Order
  import opened Options

  linear datatype Generator = 
    | Basic(
        linear biter: BucketIter,
        ghost height: nat)
    | Compose(
        linear top: Generator,
        linear bot: Generator, 
        next: BucketIteratorModel.IteratorOutput,
        ghost height: nat)
  {
    predicate {:opaque} Inv()
    decreases height, 1
    {
      Inv1()
    }

    predicate Inv1()
    decreases height, 0
    {
      && (this.Basic? ==> (
        && WFBucket(biter.bucket)
        && biter.WFIter()
      ))
      && (this.Compose? ==> (
        && top.height < this.height
        && bot.height < this.height
        && top.Inv()
        && bot.Inv()
      ))
    }

    linear method Free()
    requires Inv()
    {
      reveal_Inv_for(this);
      linear match this {
      case Basic(biter, height) =>
        biter.Free();
      case Compose(top, bot, next, height) =>
        top.Free();
        bot.Free();
      }
    }

    static lemma reveal_Inv_for(bg: Generator)
    ensures bg.Inv() == bg.Inv1()
    {
      bg.reveal_Inv();
    }

    protected function I() : BucketGeneratorModel.Generator
    requires Inv()
    decreases height
    ensures BucketGeneratorModel.WF(I())
    {
      reveal_Inv_for(this);

      if this.Basic? then (
        BucketGeneratorModel.BasicGenerator(biter.bucket, IIterator(biter.it))
      ) else (
        BucketGeneratorModel.ComposeGenerator(top.I(), bot.I(), next)
      )
    }

    predicate WM()
    {
      match this {
        case Basic(biter, _) => 
          BucketWellMarshalled(biter.bucket)
        case Compose(top, bot, _, _) => 
          && top.WM()
          && bot.WM()
      }
    }

    // predicate WF()
    // {
    //   && (BasicGenerator? ==> (
    //     && WFBucket(bucket)
    //     && WFIter(g.bucket, g.it)
    //   ))
    //   && (ComposeGenerator? ==> (
    //     && WF(g.top)
    //     && WF(g.bot)
    //   ))
    // }

    predicate {:opaque} Monotonic()
    {
      this.Compose? ==> (
        && (next.Next? && top.GenLeft().Next? ==> lt(next.key, top.GenLeft().key))
        && (next.Next? && bot.GenLeft().Next? ==> lt(next.key, bot.GenLeft().key))
        && (next.Done? ==> top.GenLeft().Done?)
        && (next.Done? ==> bot.GenLeft().Done?)
        && top.Monotonic()
        && bot.Monotonic()
      )
    }

    function {:opaque} BucketOf() : Bucket
    ensures BucketWellMarshalled(BucketOf())
    {
      match this {
        case Basic(biter, _) =>
          if biter.it.next.Done? then B(map[])
          else B(map k | k in biter.bucket.b && lte(biter.it.next.key, k) :: biter.bucket.b[k])
        case Compose(top, bot, next, _) =>
          if next.Done? then B(map[])
          else B(BucketsLib.Compose(top.BucketOf(), bot.BucketOf()).b[next.key := next.msg])
      }
    }    

    shared function method GenLeft() : (res : BucketIteratorModel.IteratorOutput)
    requires Inv()
    requires WM()
    requires Monotonic()
    {
      reveal_Inv_for(this);

      if this.Basic? then
        biter.GetNext()
      else
        next
    }

    lemma GenLeftIsMinimum()
    requires WM()
    requires Inv()
    requires Monotonic()
    ensures GenLeft().Done? ==> BucketOf().b == map[]
    ensures GenLeft().Next? ==> BucketsLib.minimumKey(BucketOf().b.Keys) == Some(GenLeft().key)
    ensures GenLeft().Next? ==> BucketOf().b[GenLeft().key] == GenLeft().msg
    {
      reveal_Inv_for(this);
      reveal_BucketOf();
      if GenLeft().Next? {
        if Compose? {
          reveal_Compose();
          assert top.Monotonic() by { reveal_Monotonic(); }
          assert bot.Monotonic() by { reveal_Monotonic(); }
          top.GenLeftIsMinimum();
          bot.GenLeftIsMinimum();
          assert GenLeft().key in BucketOf().b;
          assert forall k | k in BucketOf().b :: lte(GenLeft().key, k) by {
            reveal_Monotonic();
          }
          assert minimumKey(BucketOf().b.Keys) == Some(GenLeft().key);
        } else {
          assert GenLeft().key in BucketOf().b;
          assert forall k | k in BucketOf().b :: lte(GenLeft().key, k);
          assert minimumKey(BucketOf().b.Keys) == Some(GenLeft().key);
        }
      }
    }

    linear inout method GenPop()
    requires old_self.Inv()
    requires BucketGeneratorModel.GenLeft(old_self.I()).Next?
    ensures self.Inv()
    ensures self.I() == BucketGeneratorModel.GenPop(old_self.I()) // doesn't believe in this anymore
    decreases old_self.height
    {
      reveal_Inv_for(self);

      BucketGeneratorModel.reveal_BasicGenPop();
      BucketGeneratorModel.reveal_MergeGenPop();
      BucketGeneratorModel.reveal_GenPop();
      if self.Basic? {
        inout self.biter.IterInc();
      } else {
        var top_next := self.top.GenLeft();
        var bot_next := self.bot.GenLeft();
        var c;
        if (top_next.Next? && bot_next.Next?) {
          c := cmp(top_next.key, bot_next.key);
        }

        if top_next.Next? && bot_next.Next? && c == 0 {
          inout self.top.GenPop();
          inout self.bot.GenPop();
          inout self.next := BucketIteratorModel.Next(top_next.key,
              Merge(top_next.msg, bot_next.msg));
        } else if top_next.Next? && (bot_next.Next? ==> c < 0) {
          inout self.top.GenPop();
          inout self.next := top_next;
        } else if bot_next.Next? {
          inout self.bot.GenPop();
          inout self.next := bot_next;
        } else {
          inout self.next := BucketIteratorModel.Done;
        }
        inout ghost self.height := self.top.height + self.bot.height + 1;
      }

      assert self.Inv1();
      reveal_Inv_for(self);
    }

    static method GenCompose(linear top: Generator, linear bot: Generator)
    returns (linear g: Generator)
    requires top.Inv()
    requires bot.Inv()
    ensures g.Inv()
    ensures g.I() == BucketGeneratorModel.GenCompose(top.I(), bot.I())
    {
      var top_next := top.GenLeft();
      var bot_next := bot.GenLeft();
      var c;
      if (top_next.Next? && bot_next.Next?) {
        c := cmp(top_next.key, bot_next.key);
      }

      // next and height is placeholder value for now
      g := Compose(top, bot, top_next, 0);

      if top_next.Next? && bot_next.Next? && c == 0 {
        inout g.top.GenPop();
        inout g.bot.GenPop();
        inout g.next := BucketIteratorModel.Next(top_next.key,
            Merge(top_next.msg, bot_next.msg));
      } else if top_next.Next? && (bot_next.Next? ==> c < 0) {
        inout g.top.GenPop();
        inout g.next := top_next;
      } else if bot_next.Next? {
        inout g.bot.GenPop();
        inout g.next := bot_next;
      } else {
        inout g.next := BucketIteratorModel.Done; 
      }

      inout ghost g.height := g.top.height + g.bot.height + 1;
      assert g.Inv1();
      reveal_Inv_for(g);
      BucketGeneratorModel.reveal_GenCompose();
    }

    static method GenFromBucketWithLowerBound(shared bucket: MutBucket, start: UI.RangeStart)
    returns (linear g: Generator)
    requires bucket.Inv()
    ensures g.Basic?
    ensures g.biter.bucket == bucket.I()
    ensures g.Inv()
    ensures g.I() == BucketGeneratorModel.GenFromBucketWithLowerBound(bucket.I(), start)
    {
      linear var biter;

      match start {
        case SExclusive(key) => {
          biter := BucketIter.IterFindFirstGt(bucket, key);
        }
        case SInclusive(key) => {
          biter := BucketIter.IterFindFirstGte(bucket, key);
        }
        case NegativeInf => {
          biter := BucketIter.IterStart(bucket);
        }
      }

      g := Basic(biter, 1);
      assert g.Inv1();
      reveal_Inv_for(g);
      BucketGeneratorModel.reveal_GenFromBucketWithLowerBound();
    }
  }
}
