// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "LinkedBetreeRefinement.i.dfy"
include "ReprBetree.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "../../lib/Base/Sets.i.dfy"

module ReprBetreeRefinement
{
  import opened ReprBetree
  import opened Buffers
  import LinkedBetreeMod
  import LinkedBetreeRefinement
  import GenericDisk
  import Sets
  import Maps

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

  lemma ReachabilityInAgreeingDisks(t1: LinkedBetree, t2: LinkedBetree, ranking: Ranking) 
    requires t1.Acyclic()
    requires t2.Acyclic()
    requires t1.diskView.AgreesWithDisk(t2.diskView)
    requires t1.root == t2.root
    requires t1.ValidRanking(ranking)
    requires t2.ValidRanking(ranking)
    ensures t1.ReachableAddrsUsingRanking(ranking) == t2.ReachableAddrsUsingRanking(ranking)
    decreases t1.GetRank(ranking)
  {
    if t1.HasRoot() {
      var numChildren := |t1.Root().children|;
      forall i | 0 <= i < numChildren 
      ensures t1.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) == t2.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking)
      {
        LinkedBetreeRefinement.ChildIdxAcyclic(t1, i);
        LinkedBetreeRefinement.ChildIdxAcyclic(t2, i);
        ReachabilityInAgreeingDisks(t1.ChildAtIdx(i), t2.ChildAtIdx(i), ranking);
      }
      var t1SubAddrs := seq(numChildren, i requires 0 <= i < numChildren => t1.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      var t2SubAddrs := seq(numChildren, i requires 0 <= i < numChildren => t2.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      assert t1SubAddrs == t2SubAddrs;  // trigger
    }
  }

  lemma InternalGrowMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
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
      ReachabilityInAgreeingDisks(linked, linked'.ChildAtIdx(0), newRanking);
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked', linked'.TheRanking(), newRanking);
      assert v'.repr == v'.betree.linked.Representation();
    }
  }

  lemma ReachableAddressesHaveLowerRank(linked: LinkedBetree, topAddr: Address, topRank: nat, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires LinkedBetreeRefinement.RankingIsTight(linked.diskView, ranking)
    requires topAddr in linked.diskView.entries
    requires topAddr in ranking
    requires ranking[topAddr] == topRank
    requires linked.HasRoot()
    requires ranking[linked.root.value] < topRank;
    ensures forall addr | addr in linked.ReachableAddrsUsingRanking(ranking)
      :: addr in ranking && ranking[addr] < topRank
    decreases linked.GetRank(ranking)
  {
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    forall i | 0 <= i < numChildren 
    ensures forall addr | addr in linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking)
      :: addr in ranking && ranking[addr] < topRank
    {
      if linked.ChildAtIdx(i).HasRoot() {
        ReachableAddressesHaveLowerRank(linked.ChildAtIdx(i), topAddr, topRank, ranking);
      }
    }
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
  }

  lemma InternalFlushMemtableDeletesOldRoot(linked: LinkedBetree, linked':LinkedBetree, newBuffer: Buffer, newRootAddr:Address)
    requires linked.Acyclic()
    requires linked'.Acyclic()
    requires linked.HasRoot()
    requires linked.diskView.IsFresh({newRootAddr})
    requires linked' == LinkedBetreeMod.InsertInternalFlushMemtableReplacement(linked, newBuffer, newRootAddr).BuildTightTree()
    ensures linked.root.value !in linked'.diskView.entries
  {
    var oldRootAddr := linked.root.value;
    var oldRanking := LinkedBetreeRefinement.BuildTightRanking(linked, linked.TheRanking());
    var newRanking := oldRanking[newRootAddr := oldRanking[linked.root.value]];
    var untightLinked := LinkedBetreeMod.InsertInternalFlushMemtableReplacement(linked, newBuffer, newRootAddr);
    var numChildren := |untightLinked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => untightLinked.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking));
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    forall i | 0 <= i < numChildren 
    ensures oldRootAddr !in subTreeAddrs[i]
    {
      if untightLinked.ChildAtIdx(i).HasRoot() {
        if oldRootAddr in untightLinked.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking) {
          ReachableAddressesHaveLowerRank(untightLinked.ChildAtIdx(i), oldRootAddr, newRanking[oldRootAddr], newRanking);
          assert false;
        }
      }
    }
    LinkedBetreeRefinement.ReachableAddrIgnoresRanking(untightLinked, untightLinked.TheRanking(), newRanking);
  }

  lemma InternalFlushMemtableMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushMemtableStep?
    requires v'.betree.linked.Acyclic()
    ensures ValidRepr(v')
  {
    var linked := v.betree.linked;
    var linked' := v'.betree.linked;
    if linked.HasRoot() { 
      var oldRootAddr := linked.root.value;
      var oldRanking := LinkedBetreeRefinement.BuildTightRanking(linked, linked.TheRanking());
      var newRanking := oldRanking[step.newRootAddr := oldRanking[linked.root.value]];
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked', linked'.TheRanking(), newRanking);
      LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked, linked.TheRanking(), newRanking);
      calc {
        linked'.Representation();
        linked'.ReachableAddrsUsingRanking(newRanking);
          {
            var numChildren := |linked'.Root().children|;
            assert numChildren == |linked.Root().children|;
            var subTreeAddrs' := seq(numChildren, i requires 0 <= i < numChildren => linked'.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking));
            var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking));
            forall i | 0 <= i < numChildren 
            ensures subTreeAddrs'[i] ==  subTreeAddrs[i] {
              LinkedBetreeRefinement.ChildIdxAcyclic(linked, i);
              LinkedBetreeRefinement.ChildIdxAcyclic(linked', i);
              ReachabilityInAgreeingDisks(linked.ChildAtIdx(i), linked'.ChildAtIdx(i), newRanking);
            }
            Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
            Sets.UnionSeqOfSetsSoundness(subTreeAddrs');
            InternalFlushMemtableDeletesOldRoot(linked, linked', Buffer(v.betree.memtable.mapp), step.newRootAddr);
          }
        linked.ReachableAddrsUsingRanking(linked.TheRanking()) + {step.newRootAddr} - {oldRootAddr};
        v'.repr;
      }
    }
  }

  lemma ChildReachebleAddrsIsSubset(linked: LinkedBetree, ranking: Ranking, idx: nat) 
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(ranking) <= linked.ReachableAddrsUsingRanking(ranking)
  {
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    // trigger
    assert subTreeAddrs[idx] == linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(ranking); 
  }

  lemma BuildTightRepresentationContainsDiskView(linked: LinkedBetree, ranking: Ranking) 
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTree().Acyclic()
    ensures forall addr | addr in linked.BuildTightTree().diskView.entries 
      :: addr in linked.BuildTightTree().Representation()
    decreases linked.GetRank(ranking)
  {
    LinkedBetreeRefinement.BuildTightMaintainsRankingValidity(linked, ranking);
    forall addr | addr in linked.BuildTightTree().diskView.entries 
    ensures addr in linked.BuildTightTree().Representation()
    {
      if addr != linked.BuildTightTree().root.value {
        /* This proof is rather involved.
          - We have addr in linked.Representation(), and addr != linked.root.
          - Then, suppose addr in linked.ChildAtIdx(i).Representation().
          - Then addr in linked.ChildAtIdx(i).BuildTightTree().diskView.entries.
          - Then addr in linked.ChildAtIdx(i).BuildTightTree().Representation(), by induction.
          - Then addr in linked.BuildTightTree().ChildAtIdx(i).Representation(), since above is a subdisk.
            This is via lemma BuildTightRepresentationContainsDiskView.
          - Then addr in linked.BuildTightTree().Representation(), 
            via lemma ChildReachebleAddrsIsSubset */ 
        LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked, linked.TheRanking(), ranking);
        var numChildren := |linked.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        var idx :| 0 <= idx < numChildren && addr in subTreeAddrs[idx];
        LinkedBetreeRefinement.ChildIdxAcyclic(linked, idx);
        LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked.ChildAtIdx(idx), ranking, linked.ChildAtIdx(idx).TheRanking());
        BuildTightRepresentationContainsDiskView(linked.ChildAtIdx(idx), ranking);  // apply induction hypothesis
        LinkedBetreeRefinement.BuildTightMaintainsRankingValidity(linked.ChildAtIdx(idx), ranking);
        LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked.ChildAtIdx(idx).BuildTightTree(), ranking, linked.ChildAtIdx(idx).BuildTightTree().TheRanking());
        assert linked.BuildTightTree().ChildAtIdx(idx).ValidRanking(ranking);  // trigger
        ReachabilityInAgreeingDisks(linked.BuildTightTree().ChildAtIdx(idx), linked.ChildAtIdx(idx).BuildTightTree(), ranking);
        ChildReachebleAddrsIsSubset(linked.BuildTightTree(), ranking, idx);  
        LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked.BuildTightTree(), ranking, linked.BuildTightTree().TheRanking());
      }
    }
  }

  lemma BuildTightGivesTightWrtRepresentation(linked: LinkedBetree)
    requires linked.Acyclic()
    ensures linked.BuildTightTree().Acyclic()
    ensures linked.BuildTightTree().DiskIsTightWrtRepresentation();
  {
    LinkedBetreeRefinement.BuildTightMaintainsRankingValidity(linked, linked.TheRanking());
    BuildTightRepresentationContainsDiskView(linked, linked.TheRanking());
  }

  lemma InternalFlushMemtableMaintainsTightDisk(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushMemtableStep?
    requires v'.betree.linked.Acyclic()
    ensures v'.betree.linked.DiskIsTightWrtRepresentation()
  {
    var newBuffer := Buffer(v.betree.memtable.mapp);
    var untightLinked :=  LinkedBetreeMod.InsertInternalFlushMemtableReplacement(v.betree.linked, newBuffer, step.newRootAddr);
    if v.betree.linked.HasRoot() {
      BuildTightGivesTightWrtRepresentation(untightLinked);
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
        InternalGrowMaintainsRepr(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalSplitStep(_, _, _, _) => {
        // TODO(tony)
        assume false;
        assert Inv(v');
      }
      case InternalFlushStep(_, _, _, _, _) => {
        // TODO(tony)
        assume false;
        assert Inv(v');
      }
      case InternalFlushMemtableStep(_) => {
        LinkedBetreeRefinement.InvNextInternalFlushMemtableStep(I(v), I(v'), lbl.I(), step.I());
        InternalFlushMemtableMaintainsRepr(v, v', lbl, step);
        InternalFlushMemtableMaintainsTightDisk(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalCompactStep(_, _, _, _) => {
        // TODO(tony)
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
