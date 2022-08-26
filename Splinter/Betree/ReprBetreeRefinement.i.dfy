// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "LinkedBetreeRefinement.i.dfy"
include "ReprBetree.i.dfy"
include "../../lib/Base/Sets.i.dfy"

module ReprBetreeRefinement
{
  import opened ReprBetree
  import LinkedBetreeMod
  import LinkedBetreeRefinement
  import GenericDisk
  import Sets

  type Ranking = GenericDisk.Ranking

  function I(v: Variables) : (out: LinkedBetreeMod.Variables) {
    v.betree
  }

  // The representation of v.betree == v.repr
  predicate ValidRepr(v: Variables) 
    requires v.betree.linked.Acyclic()
  {
    v.repr == v.betree.linked.Representation()
  }

  predicate Inv(v: Variables) {
    // Note: ValidRepr and DiskIsTightWrtRepresentation together 
    // gives us diskView.entries.Keys == v.repr
    && v.WF()
    && LinkedBetreeRefinement.Inv(v.betree)
    && ValidRepr(v)                                    // v.repr == Representation
    && v.betree.linked.DiskIsTightWrtRepresentation()  // diskView == Representation
  }

  //******** PROVE INVARIANTS ********//

  lemma InvInit(v: Variables, gcBetree: GCStampedBetree) 
    requires Init(v, gcBetree)
    requires LinkedBetreeRefinement.InvLinkedBetree(gcBetree.I().value)
    ensures Inv(v)
  {
    LinkedBetreeRefinement.InitRefines(I(v), gcBetree.I());
  }

  lemma FreshDiskEntriesPreserveReachability(small: LinkedBetree, big: LinkedBetree, addrs: set<Address>, ranking: Ranking) 
    requires small.Acyclic()
    requires big.Acyclic()
    requires big.diskView.entries.Keys == small.diskView.entries.Keys + addrs
    requires small.diskView.IsSubDisk(big.diskView)
    requires small.root == big.root
    requires small.ValidRanking(ranking)
    requires big.ValidRanking(ranking)
    ensures small.ReachableAddrsUsingRanking(ranking) == big.ReachableAddrsUsingRanking(ranking)
    decreases small.GetRank(ranking)
  {
    if small.HasRoot() {
      var numChildren := |small.Root().children|;
      forall i | 0 <= i < numChildren 
      ensures small.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) == big.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking)
      {
        LinkedBetreeRefinement.ChildIdxAcyclic(small, i);
        LinkedBetreeRefinement.ChildIdxAcyclic(big, i);
        FreshDiskEntriesPreserveReachability(small.ChildAtIdx(i), big.ChildAtIdx(i), addrs, ranking);
      }
      var smallSubAddrs := seq(numChildren, i requires 0 <= i < numChildren => small.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      var bigSubAddrs := seq(numChildren, i requires 0 <= i < numChildren => big.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      assert smallSubAddrs == bigSubAddrs;  // trigger
    }
  }

  lemma GrowStepMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    requires v'.betree.linked.Acyclic()
    ensures ValidRepr(v')
  {
    var linked := v.betree.linked;
    var linked' := v'.betree.linked;
    var oldRanking := LinkedBetreeRefinement.BuildTightRanking(linked, linked.TheRanking());
    var newRanking := LinkedBetreeRefinement.InsertGrowReplacementNewRanking(linked, oldRanking, step.newRootAddr);
    if v.betree.linked.HasRoot() {
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked, linked.TheRanking(), oldRanking);
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked, oldRanking, newRanking);
      var numChildren := |linked'.Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked'.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking));
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      LinkedBetreeRefinement.ChildIdxAcyclic(linked', 0);
      FreshDiskEntriesPreserveReachability(linked, linked'.ChildAtIdx(0), {step.newRootAddr}, newRanking);
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked', linked'.TheRanking(), newRanking);
      assert v'.repr == v'.betree.linked.Representation();
    }
  }

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
        LinkedBetreeRefinement.InvNextInternalGrowStep(I(v), I(v'), lbl.I(), step.I());
        GrowStepMaintainsRepr(v, v', lbl, step);
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


  //******** PROVE REFINEMENT ********//

  lemma InitRefines(v: Variables, gcBetree: GCStampedBetree)
    requires Init(v, gcBetree)
    requires LinkedBetreeRefinement.InvLinkedBetree(gcBetree.I().value)
    ensures Inv(v)
    ensures LinkedBetreeMod.Init(I(v), gcBetree.I())
  {
    InvInit(v, gcBetree);
    LinkedBetreeRefinement.InitRefines(I(v), gcBetree.I());
  }

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
