// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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

// begin generated export
  export Spec
    provides *
    reveals Generator.Inv1, Generator
  export extends Spec
// end generated export

  linear datatype Generator = Basic(linear biter: BucketIter, ghost height: nat)
    | Compose(linear top: Generator, linear bot: Generator, 
      next: BucketIteratorModel.IteratorOutput, ghost height: nat)
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

    function I() : BucketGeneratorModel.Generator
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

    shared method GenLeft() returns (res : BucketIteratorModel.IteratorOutput)
    requires Inv()
    ensures res == BucketGeneratorModel.GenLeft(I())
    {
      reveal_Inv_for(this);

      if this.Basic? {
        res := biter.GetNext();
      } else {
        res := next;
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
