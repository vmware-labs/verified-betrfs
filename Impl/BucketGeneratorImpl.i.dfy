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
  import opened Maps
  import Keyspace = Lexicographic_Byte_Order

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

    // lemma lemmaDecreaserDecreases()
    // requires WF()
    // ensures GenLeft().Next? ==> decreaser(GenPop()) < decreaser()
    // {
    //   reveal_GenPop();
    //   reveal_MergeGenPop();
    //   reveal_BasicGenPop();
    //   reveal_decreaser();
    //   if g.ComposeGenerator? {
    //     lemmaDecreaserDecreases(g.top);
    //     lemmaDecreaserDecreases(g.bot);
    //   }
    // }

    // function {:opaque} decreaser() : nat
    // requires WF()
    // {
    //   match this {
    //     case Basic(biter, _) => (
    //       biter.it.decreaser
    //     )
    //     case Compose(top, bot, next, _) => (
    //       top.decreaser() + bot.decreaser() + (if next.Next? then 1 else 0)
    //     )
    //   }
    // }

    shared function method GenLeft() : (res : BucketIteratorModel.IteratorOutput)
    requires Inv()
    requires WM()
    {
      reveal_Inv_for(this);

      var res := if this.Basic? then
        biter.GetNext()
      else
        next;
      
      res
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

    predicate YieldsSortedBucket(b: Bucket)
    {
      && Inv()
      && WM()
      && Monotonic()
      && BucketOf().b == b.b
    }

    linear inout method GenPop()
    requires old_self.Inv()
    requires old_self.WM()
    requires old_self.Monotonic()

    requires BucketGeneratorModel.GenLeft(old_self.I()).Next?
    requires old_self.GenLeft().Next?
    ensures self.Inv()
    ensures |old_self.BucketOf().b.Keys| >= 1
    ensures self.YieldsSortedBucket(
      B(MapRemove1(old_self.BucketOf().b, Keyspace.minimum(old_self.BucketOf().b.Keys))))
    decreases old_self.height
    {
      reveal_Inv_for(self);

      reveal_BucketOf();
      self.GenLeftIsMinimum();

      if self.Basic? {
        inout self.biter.IterInc();

        BucketIteratorModel.IterIncKeyGreater(old_self.biter.bucket, IIterator(old_self.biter.it));

        ghost var b1 := self.BucketOf().b;
        ghost var b2 := MapRemove1(old_self.BucketOf().b, minimum(old_self.BucketOf().b.Keys));
        forall k | k in b1 ensures k in b2 && b1[k] == b2[k]
        {
        }
        forall k | k in b2 ensures k in b1
        {
          BucketIteratorModel.noKeyBetweenIterAndIterInc(old_self.biter.bucket, IIterator(old_self.biter.it), k);
        }
        assert b1 == b2;

        assert self.Monotonic() by { reveal_Monotonic(); }
      } else {
        assert self.top.Monotonic() by { reveal_Monotonic(); }
        assert self.bot.Monotonic() by { reveal_Monotonic(); }

        var top_next := self.top.GenLeft();
        var bot_next := self.bot.GenLeft();

        old_self.top.GenLeftIsMinimum();
        old_self.bot.GenLeftIsMinimum();

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

        if (top_next.Next?) {
          assert top_next.key in old_self.top.BucketOf().b.Keys;
        }
        if (bot_next.Next?) {
          assert bot_next.key in old_self.bot.BucketOf().b.Keys;
        }

        assert (self.next.Next? && self.top.GenLeft().Next? ==> lt(self.next.key, self.top.GenLeft().key));
        assert (self.next.Next? && self.bot.GenLeft().Next? ==> lt(self.next.key, self.bot.GenLeft().key));
        // assert  (self.next.Done? ==> self.top.GenLeft().Done?);
        // assert  (self.next.Done? ==> self.bot.GenLeft().Done?);

        // assert self.Monotonic() by {
        //   assert && self.top.Monotonic()
        //     && self.bot.Monotonic();
        //   reveal_Monotonic();
        // }

        assume false;
        // assert GenPop(g).ComposeGenerator?;
        // calc {
        //   BucketOf(GenPop(g)).b;
        //   {
        //     assert
        //       && (g.next.Next? && top_next.Next? ==> lt(g.next.key, top_next.key))
        //       && (g.next.Next? && bot_next.Next? ==> lt(g.next.key, bot_next.key)) by {
        //       reveal_Monotonic();
        //     }
        //   }
        //   MapRemove1(BucketOf(g).b, minimum(BucketOf(g).b.Keys));
        // }
        // assert self.YieldsSortedBucket(B(MapRemove1(old_self.BucketOf().b, minimum(old_self.BucketOf().b.Keys))));
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
