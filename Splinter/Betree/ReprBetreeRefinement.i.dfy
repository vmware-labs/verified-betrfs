// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "LinkedBetreeRefinement.i.dfy"
include "ReprBetree.i.dfy"
include "../Disk/GenericDisk.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../../lib/Base/Sets.i.dfy"
include "../../lib/Base/Sequences.i.dfy"

module ReprBetreeRefinement
{
  import opened ReprBetree
  import opened Buffers
  import opened BoundedPivotsLib
  import LinkedBetreeMod
  import LinkedBetreeRefinement
  import GenericDisk
  import Sets
  import opened Sequences

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

  lemma ReachableAddrsInAgreeingDisks(t1: LinkedBetree, t2: LinkedBetree, ranking: Ranking) 
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
        ReachableAddrsInAgreeingDisks(t1.ChildAtIdx(i), t2.ChildAtIdx(i), ranking);
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
      ReachableAddrsInAgreeingDisks(linked, linked'.ChildAtIdx(0), newRanking);
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
              ReachableAddrsInAgreeingDisks(linked.ChildAtIdx(i), linked'.ChildAtIdx(i), newRanking);
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

  lemma {:timeLimitMultiplier 2} BuildTightRepresentationContainsDiskView(linked: LinkedBetree, ranking: Ranking) 
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
        ReachableAddrsInAgreeingDisks(linked.BuildTightTree().ChildAtIdx(idx), linked.ChildAtIdx(idx).BuildTightTree(), ranking);
        ChildReachebleAddrsIsSubset(linked.BuildTightTree(), ranking, idx);  
        LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linked.BuildTightTree(), ranking, linked.BuildTightTree().TheRanking());
      }
    }
  }

  // Theorem: linked.BuildTightTree().diskView.entries.Keys == linked.BuildTightTree().Representation
  lemma BuildTightGivesTightWrtRepresentation(linked: LinkedBetree)
    requires linked.Acyclic()
    ensures linked.BuildTightTree().Acyclic()
    ensures linked.BuildTightTree().DiskIsTightWrtRepresentation();
    // i.e. linked.BuildTightTree().diskView.entries.Keys == Representation()
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

  lemma SubstituteDeletesTarget(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    ensures path.Target().root.value !in path.Substitute(replacement, pathAddrs).BuildTightTree().diskView.entries
  {
    assume false;
  }

  lemma ChildAtIdxCommutesWithBuildTight(linked: LinkedBetree, idx: nat, ranking: Ranking) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    requires linked.ValidRanking(ranking)

    ensures linked.ChildAtIdx(idx).BuildTightTree().WF()
    ensures linked.ChildAtIdx(idx).BuildTightTree().ValidRanking(ranking)
    ensures linked.BuildTightTree().WF()
    ensures linked.ChildAtIdx(idx).BuildTightTree().ReachableAddrsUsingRanking(ranking)
        == linked.BuildTightTree().ChildAtIdx(idx).ReachableAddrsUsingRanking(ranking)
  {
    // By ReachableAddrsInAgreeingDisks
    assume false;
  }

  lemma ReachableAddrsIgnoresBuildTight(linked: LinkedBetree, ranking: Ranking)
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTree().WF()
    ensures linked.BuildTightTree().ValidRanking(ranking)
    ensures linked.BuildTightTree().ReachableAddrsUsingRanking(ranking)
      == linked.ReachableAddrsUsingRanking(ranking)
  {
    assume false;
  }

  lemma RepresentationIgnoresBuildTight(linked: LinkedBetree)
    requires linked.Acyclic()
    ensures linked.BuildTightTree().Acyclic()
    ensures linked.BuildTightTree().Representation()
      == linked.Representation()
  {
    assume false;
  }

  lemma SubpathValidRanking(path: Path, replacement: LinkedBetree, ranking: Ranking, pathAddrs: PathAddrs)
    requires path.Valid()
    requires 0 < path.depth
    requires path.CanSubstitute(replacement, pathAddrs);
    requires path.Substitute(replacement, pathAddrs).WF()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    ensures path.Subpath().Substitute(replacement, pathAddrs[1..]).WF()
    ensures path.Subpath().Substitute(replacement, pathAddrs[1..]).ValidRanking(ranking)
  {
    assume false;
  }

  lemma ReachableAddrsOnSubpathRoute(path: Path, replacement: LinkedBetree, ranking: Ranking, routeIdx: nat, pathAddrs: PathAddrs)
    requires path.Valid()
    requires 0 < path.depth
    requires routeIdx == Route(path.linked.Root().pivotTable, path.key)
    requires path.CanSubstitute(replacement, pathAddrs);
    requires path.Substitute(replacement, pathAddrs).WF()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    ensures path.Subpath().Substitute(replacement, pathAddrs[1..]).WF()
    ensures path.Subpath().Substitute(replacement, pathAddrs[1..]).ValidRanking(ranking);
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).ReachableAddrsUsingRanking(ranking)
      == path.Subpath().Substitute(replacement, pathAddrs[1..]).ReachableAddrsUsingRanking(ranking)
  {
    assume false;
    // path.Substitute(replacement, pathAddrs).ChildAtIdx(subIdx).ReachableAddrsUsingRanking(ranking);
    // path.Subpath().Substitute(replacement, pathAddrs[1..]).ReachableAddrsUsingRanking(ranking);
  }

  lemma ReachableAddrsNotOnSubpathRoute(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, idx: nat) 
    requires path.Valid()
    requires 0 < path.depth
    requires 0 <= idx < |path.linked.Root().children|
    requires idx != Route(path.linked.Root().pivotTable, path.key)
    requires path.CanSubstitute(replacement, pathAddrs);
    ensures path.linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).Acyclic()  // prereq
    ensures path.linked.ChildAtIdx(idx).Representation() ==
            path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).Representation()
  { 
    assume false;
  }

  lemma RootRepresentationContainsSubpathRepresentation(path: Path) 
    requires path.Valid()
    requires path.linked.Acyclic()
    requires 0 < path.depth
    ensures path.Subpath().linked.Acyclic()
    ensures path.Subpath().linked.Representation() <= path.linked.Representation();
  {
    assume false;
  }

  lemma ParentRepresentationContainsChildRepresentation(linked:LinkedBetree, idx: nat)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures linked.ChildAtIdx(idx).Representation() <= linked.Representation()
  {
    assume false;
    // assert addr in path.linked.ChildAtIdx(idx).Representation();
    // assert addr in path.linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(path.linked.ChildAtIdx(idx).TheRanking());
    // LinkedBetreeRefinement.ReachableAddrIgnoresRanking(path.linked.ChildAtIdx(idx), path.linked.ChildAtIdx(idx).TheRanking(), path.linked.TheRanking());
    // assert addr in path.linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(path.linked.TheRanking());


    // assert addr in path.linked.ReachableAddrsUsingRanking(path.linked.TheRanking());
    // assert addr in path.linked.Representation();
  }

  lemma SubtreeRepresentationsAreDisjoint(linked: LinkedBetree, i: nat, j: nat) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(i)
    requires linked.Root().ValidChildIndex(j)
    requires i != j
    ensures linked.ChildAtIdx(i).Acyclic()  // prereq
    ensures linked.ChildAtIdx(j).Acyclic()  // prereq
    ensures linked.ChildAtIdx(i).Representation() !! linked.ChildAtIdx(j).Representation()
  {
    assume false;
  }

  lemma AddrsOnPathIsRootOrInRouteSubtree(path: Path, subIdx: nat)
    requires path.Valid()
    requires subIdx == Route(path.linked.Root().pivotTable, path.key)
    ensures path.linked.ChildAtIdx(subIdx).Acyclic()
    ensures path.AddrsOnPath() <= 
      {path.linked.root.value} + path.linked.ChildAtIdx(subIdx).Representation()
  {
    assume false;
  }

  lemma AddrInChildRepresentationImpliesNotRoot(linked: LinkedBetree, idx: nat, addr: Address)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    requires linked.ChildAtIdx(idx).Acyclic()
    requires addr in linked.ChildAtIdx(idx).Representation()
    ensures addr != linked.root.value
  {
    assume false;
    // assert addr in path.linked.ChildAtIdx(idx).Representation();
    //       assert addr in path.linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(path.linked.ChildAtIdx(idx).TheRanking());
    //       LinkedBetreeRefinement.ChildIdxAcyclic(path.linked, idx);
    //       LinkedBetreeRefinement.ReachableAddrIgnoresRanking(path.linked.ChildAtIdx(idx), path.linked.TheRanking(), path.linked.ChildAtIdx(idx).TheRanking());
    //       // assert addr in path.linked.ChildAtIdx(idx).ReachableAddrsUsingRanking(path.linked.TheRanking());
    //       assume addr != path.linked.root.value;   // this must be true because addr in path.linked.ChildAtIdx(idx).Representation();
  }

  lemma AddrInSubstituteSubtreeCannotBeOldRoot(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, subIdx:nat, addr: Address)
    requires path.Valid()
    requires 0 < path.depth
    requires subIdx == Route(path.linked.Root().pivotTable, path.key)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).WF()
    requires path.Substitute(replacement, pathAddrs).ChildAtIdx(subIdx).Acyclic()
    requires addr in path.Substitute(replacement, pathAddrs).ChildAtIdx(subIdx).Representation()
    ensures addr != path.linked.root.value
  {
    assume false;
  }

  lemma SubstitutedBranchRepresentation(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, replacementAddr: Address, subTreeAddrs: seq<set<Address>>, subIdx: nat, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires subIdx == Route(path.linked.Root().pivotTable, path.key);
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).Acyclic()

    // establish subTreeAddrs
    requires 
      && var node := path.linked.Root();
      && var numChildren := |path.Substitute(replacement, pathAddrs).Root().children|;
      && subTreeAddrs == seq(numChildren, i requires 0 <= i < numChildren => path.Substitute(replacement, pathAddrs).ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

    // Induction hypothesis
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).Representation()
            == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()  
    ensures path.Subpath().linked.Acyclic()
    ensures subTreeAddrs[subIdx] 
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()
  {
    ChildAtIdxCommutesWithBuildTight(path.Substitute(replacement, pathAddrs), subIdx, ranking);
    ReachableAddrsIgnoresBuildTight(path.Substitute(replacement, pathAddrs).ChildAtIdx(subIdx), ranking);
    SubpathValidRanking(path, replacement, ranking, pathAddrs);
    ReachableAddrsIgnoresBuildTight(path.Subpath().Substitute(replacement, pathAddrs[1..]), ranking);
    ReachableAddrsOnSubpathRoute(path, replacement, ranking, subIdx, pathAddrs);
    LinkedBetreeRefinement.ReachableAddrIgnoresRanking(path.Subpath().Substitute(replacement, pathAddrs[1..]), path.Subpath().Substitute(replacement, pathAddrs[1..]).TheRanking(), ranking);
  }

  // Tony: this lemma is sprawling massive...
  lemma ReprAfterSubstituteCompactReplacement(path: Path, compactedBuffers: BufferStack, replacement: LinkedBetree, replacementRanking: Ranking, pathAddrs: PathAddrs, replacementAddr: Address)
    requires path.Valid()
    requires path.Target().Root().buffers.Equivalent(compactedBuffers)
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires replacement == LinkedBetreeMod.InsertCompactReplacement(path.Target(), compactedBuffers, replacementAddr)
    requires replacement.ValidRanking(replacementRanking)

    //RankingAfterSubstitution requirements
    requires path.linked.root.value in replacementRanking
    requires SeqHasUniqueElems(pathAddrs)
    requires Set(pathAddrs) !! replacementRanking.Keys
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))

    requires path.CanSubstitute(replacement, pathAddrs)
    ensures path.Substitute(replacement, pathAddrs).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
            == path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
    decreases path.depth
  {
    var ranking := LinkedBetreeRefinement.RankingAfterSubstitution(replacement, replacementRanking, path, pathAddrs);
    LinkedBetreeRefinement.BuildTightMaintainsRankingValidity(path.Substitute(replacement, pathAddrs), ranking);
    if path.depth == 0 {
      ReprAfterSubstituteCompactReplacementBaseCase(path, compactedBuffers, replacement, pathAddrs, replacementAddr, ranking);
    } else {
      ReprAfterSubstituteCompactReplacement(path.Subpath(), compactedBuffers, replacement, replacementRanking, pathAddrs[1..], replacementAddr);
      // Induction hypothesis:
      // assert path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      //       == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath();
      var node := path.linked.Root();
      var subIdx := Route(node.pivotTable, path.key);
      var numChildren := |path.Substitute(replacement, pathAddrs).BuildTightTree().Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.Substitute(replacement, pathAddrs).BuildTightTree().ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      ReprAfterSubstituteCompactReplacementInduction1(path, replacement, pathAddrs, replacementAddr);
      ReprAfterSubstituteCompactReplacementInduction2(path, compactedBuffers, replacement, pathAddrs, replacementAddr, ranking);
    }
  }

  // This juicy lemma requires a lot of juice
  lemma {:timeLimitMultiplier 2} ReprAfterSubstituteCompactReplacementInduction1(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, replacementAddr: Address)
    requires path.Valid()
    requires 0 < path.depth
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Acyclic()

    // Induction hypothesis
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath();
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation() 
        <= path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
  {
    var linkedAftSubst := path.Substitute(replacement, pathAddrs);
    forall addr | addr in linkedAftSubst.BuildTightTree().Representation() 
    ensures addr in path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
    {
      RepresentationIgnoresBuildTight(linkedAftSubst);
      if addr != linkedAftSubst.root.value {
        // Here, addr is in one of the children subtrees of the new root. In this case, it
        // is either in one of the unchanged subtrees, or the one that is swapped in 
        // during substitution.
        var ranking := linkedAftSubst.TheRanking();
        var numChildren := |linkedAftSubst.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linkedAftSubst.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        var idx :| 0 <= idx < numChildren && addr in subTreeAddrs[idx];
        LinkedBetreeRefinement.ChildIdxAcyclic(linkedAftSubst, idx);
        var subIdx := Route(path.linked.Root().pivotTable, path.key);
        if idx == subIdx {  
          // If addr is in the subtree that is swapped in during substitution
          RepresentationIgnoresBuildTight(path.Subpath().Substitute(replacement, pathAddrs[1..]));
          SubstitutedBranchRepresentation(path, replacement, pathAddrs, replacementAddr, subTreeAddrs, subIdx, ranking);
          RootRepresentationContainsSubpathRepresentation(path);
          assert addr !in path.AddrsOnPath() by {  // trigger
            LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linkedAftSubst.ChildAtIdx(subIdx), linkedAftSubst.ChildAtIdx(subIdx).TheRanking(), ranking);
            AddrInSubstituteSubtreeCannotBeOldRoot(path, replacement, pathAddrs, subIdx, addr);
            assert addr != path.linked.root.value;
          }
        } else {  
          // Else addr is in one of the original subtrees
          // First, prove that addr in path.linked.Representation();
          LinkedBetreeRefinement.ReachableAddrIgnoresRanking(linkedAftSubst.ChildAtIdx(idx), linkedAftSubst.ChildAtIdx(idx).TheRanking(), ranking);
          ReachableAddrsNotOnSubpathRoute(path, replacement, pathAddrs, idx);
          ParentRepresentationContainsChildRepresentation(path.linked, idx);

          // Next, Prove that addr not in path.AddrsOnPath();
          AddrInChildRepresentationImpliesNotRoot(path.linked, idx, addr);
          AddrsOnPathIsRootOrInRouteSubtree(path, subIdx);
          SubtreeRepresentationsAreDisjoint(path.linked, idx, subIdx);
        }
      }
    }
  }

  lemma ReprAfterSubstituteCompactReplacementInduction2(path: Path, compactedBuffers: BufferStack, replacement: LinkedBetree, pathAddrs: PathAddrs, replacementAddr: Address, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires path.Target().Root().buffers.Equivalent(compactedBuffers)
    requires path.Target().diskView.IsFresh({replacementAddr})
    // requires replacement == LinkedBetreeMod.InsertCompactReplacement(path.Target(), compactedBuffers, replacementAddr)  // don't need this now!
    requires path.CanSubstitute(replacement, pathAddrs)

    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()

    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Acyclic()

    // Induction hypothesis
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath();

    ensures path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
      <= path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
  {
    assume false;
  }

  lemma ReprAfterSubstituteCompactReplacementBaseCase(path: Path, compactedBuffers: BufferStack, replacement: LinkedBetree, pathAddrs: PathAddrs, replacementAddr: Address, ranking: Ranking)
    requires path.Valid()
    requires path.depth == 0  // base case
    requires path.Target().Root().buffers.Equivalent(compactedBuffers)
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires replacement == LinkedBetreeMod.InsertCompactReplacement(path.Target(), compactedBuffers, replacementAddr)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
            == path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
  {
    var numChildren := |replacement.BuildTightTree().Root().children|;
    var subTreeAddrs' := seq(numChildren, i requires 0 <= i < numChildren => replacement.BuildTightTree().ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    forall i | 0 <= i < numChildren 
    ensures subTreeAddrs'[i] ==  subTreeAddrs[i] {
      LinkedBetreeRefinement.ChildIdxAcyclic(path.linked, i);
      LinkedBetreeRefinement.ChildIdxAcyclic(replacement.BuildTightTree(), i);
      ReachableAddrsInAgreeingDisks(path.linked.ChildAtIdx(i), replacement.BuildTightTree().ChildAtIdx(i), ranking);
    }
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs');
    SubstituteDeletesTarget(path, replacement, pathAddrs);
    LinkedBetreeRefinement.ReachableAddrIgnoresRanking(path.linked, ranking, path.linked.TheRanking());
    LinkedBetreeRefinement.ReachableAddrIgnoresRanking(replacement.BuildTightTree(), ranking, replacement.BuildTightTree().TheRanking());
  }

  lemma InternalCompactMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v'.betree.linked.Acyclic()
    ensures ValidRepr(v')
  {
    var linked := v.betree.linked;
    var linked' := v'.betree.linked;
    var newAddrs := Set(step.pathAddrs) + {step.targetAddr};
    var discardAddrs := step.path.AddrsOnPath();
    var replacement := LinkedBetreeMod.InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    LinkedBetreeRefinement.ValidRankingAllTheWayDown(linked.TheRanking(), step.path);
    var replacementRanking := LinkedBetreeRefinement.RankingAfterInsertCompactReplacement(step.path.Target(), step.compactedBuffers, linked.TheRanking(), step.targetAddr);
    if linked.HasRoot() {
      calc {
        v'.betree.linked.Representation();
        step.path.Substitute(
            replacement,
            step.pathAddrs
          ).BuildTightTree().Representation();
        
          { 
            assume Set(step.pathAddrs) !! replacementRanking.Keys;  // TODO: framing argument?
            ReprAfterSubstituteCompactReplacement(step.path, step.compactedBuffers, replacement, replacementRanking, step.pathAddrs, step.targetAddr); 
          }

        linked.ReachableAddrsUsingRanking(linked.TheRanking()) + newAddrs - discardAddrs;
        v.repr + newAddrs - discardAddrs;
        v'.repr;
      }
      assert ValidRepr(v');
    }
  }

  lemma InternalCompactMaintainsTightDisk(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v'.betree.linked.Acyclic()
    ensures v'.betree.linked.DiskIsTightWrtRepresentation()
  {
    var untightLinked := LinkedBetreeMod.InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    if v.betree.linked.HasRoot() {
      // var newRanking := RankingAfterInsertCompactReplacement(step.path.Target(), step.compactedBuffers, linked.TheRanking(), step.targetAddr);
      // TODO
      assume untightLinked.Acyclic();
      BuildTightGivesTightWrtRepresentation(untightLinked);
      assume false;
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
        LinkedBetreeRefinement.InvNextInternalCompactStep(I(v), I(v'), lbl.I(), step.I());
        InternalCompactMaintainsRepr(v, v', lbl, step);
        InternalCompactMaintainsTightDisk(v, v', lbl, step);
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
