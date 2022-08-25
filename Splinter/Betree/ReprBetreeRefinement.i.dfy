// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "ReprBetree.i.dfy"

module ReprBetreeRefinement
{
  import opened ReprBetree
  import LinkedBetreeMod

  function I(v: Variables) : (out: LinkedBetreeMod.Variables)
    requires v.WF()
    ensures out.WF()
  {
    v.betree
  }

  // The representation of v.betree == v.repr
  predicate ValidRepr(v: Variables) 
    requires v.betree.linked.Acyclic()
  {
    v.repr == v.betree.linked.Representation()
  }

  predicate Inv(v: Variables) {
    && v.WF()
    && ValidRepr(v)
  }

  lemma InvInit(v: Variables, gcBetree: GCStampedBetree) 
    requires Init(v, gcBetree)
    ensures Inv(v)
  {}

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel) 
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        assert Inv(v');
      }
      case PutStep() => {
        assert Inv(v');
      }
      case QueryEndLsnStep() => {
        assert Inv(v');
      }
      case FreezeAsStep() => {
        assert Inv(v');
      }
      case InternalGrowStep(_) => {
        // TODO(tony)
        assume false;
        assert Inv(v');
      }
      case InternalSplitStep(_, _, _, _) => {
        // TODO(tony): Something is very wrong here, assert false passes.
        assume false;
        assert Inv(v');
      }
      case InternalFlushStep(_, _, _, _, _) => {
        // TODO(tony): Something is very wrong here, assert false passes.
        assume false;
        assert Inv(v');
      }
      case InternalFlushMemtableStep(_) => {
        // TODO(tony): Something is very wrong here, assert false passes.
        assume false;
        assert Inv(v');
      }
      case InternalCompactStep(_, _, _, _) => {
        // TODO(tony): Something is very wrong here, assert false passes.
        assume false;
        assert Inv(v');
      }
      case InternalMapReserveStep() => {
        assert Inv(v');
      }
      case InternalMapFreeStep() => {
        assert Inv(v');
      }
      case InternalNoOpStep() => {
        assert Inv(v');
      }
    }
  }

  lemma InitRefines(v: Variables, gcBetree: GCStampedBetree)
    requires Init(v, gcBetree)
    ensures Inv(v)
    ensures LinkedBetreeMod.Init(I(v), gcBetree.I())
  {}

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures LinkedBetreeMod.Next(I(v), I(v'), lbl.I())
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    assert LinkedBetreeMod.NextStep(I(v), I(v'), lbl.I(), step.I());
  }
}
