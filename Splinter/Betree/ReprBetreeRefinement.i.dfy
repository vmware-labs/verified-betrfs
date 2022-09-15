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
  import LB = LinkedBetreeMod
  import LBR = LinkedBetreeRefinement
  import GenericDisk
  import Sets
  import opened Sequences

  type Ranking = GenericDisk.Ranking

  function I(v: Variables) : (out: LB.Variables) {
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
    && LBR.Inv(v.betree)
    && ValidRepr(v)                                    // v.repr == Representation
    && v.betree.linked.DiskIsTightWrtRepresentation()  // diskView == Representation
  }

  //******** PROVE INVARIANTS ********//

  predicate PathAddrsFresh(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs)
  {
    && SeqHasUniqueElems(pathAddrs)
    && path.linked.diskView.IsFresh(Set(pathAddrs))
    && replacement.diskView.IsFresh(Set(pathAddrs))
  }

  lemma InvInit(v: Variables, gcBetree: GCStampedBetree) 
    requires Init(v, gcBetree)
    requires LBR.InvLinkedBetree(gcBetree.I().value)
    ensures Inv(v)
  {
    LBR.InitRefines(I(v), gcBetree.I());
  }

  // Theorem: If t1.root = t2.root and their disks agree, then t1 and t2 have the same Representation
  lemma ReachableAddrsInAgreeingDisks(t1: LinkedBetree, t2: LinkedBetree, ranking: Ranking) 
    requires t1.WF()
    requires t2.WF()
    requires t1.ValidRanking(ranking)
    requires t2.ValidRanking(ranking)
    requires t1.diskView.AgreesWithDisk(t2.diskView)
    requires t1.root == t2.root
    ensures t1.ReachableAddrsUsingRanking(ranking) == t2.ReachableAddrsUsingRanking(ranking)
    decreases t1.GetRank(ranking)
  {
    if t1.HasRoot() {
      var numChildren := |t1.Root().children|;
      forall i | 0 <= i < numChildren 
      ensures t1.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking) == t2.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking)
      {
        LBR.ChildAtIdxAcyclic(t1, i);
        LBR.ChildAtIdxAcyclic(t2, i);
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
    var oldRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
    var newRanking := LBR.InsertGrowReplacementNewRanking(linked, oldRanking, step.newRootAddr);
    if v.betree.linked.HasRoot() {
      LBR.ReachableAddrsIgnoresRanking(linked, linked.TheRanking(), oldRanking);
      LBR.ReachableAddrsIgnoresRanking(linked, oldRanking, newRanking);
      var numChildren := |linked'.Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked'.ChildAtIdx(i).ReachableAddrsUsingRanking(newRanking));
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      ReachableAddrsInAgreeingDisks(linked, linked'.ChildAtIdx(0), newRanking);
      LBR.ReachableAddrsIgnoresRanking(linked', linked'.TheRanking(), newRanking);
      assert v'.repr == v'.betree.linked.Representation();
    }
  }

  // Theorem: All reachable addresses must have a lower smaller ranking than the root
  lemma ReachableAddressesHaveLowerRank(linked: LinkedBetree, topAddr: Address, topRank: nat, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires LBR.RankingIsTight(linked.diskView, ranking)
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

  // Theorem: A wrapper around ReachableAddressesHaveLowerRank
  lemma ChildrenRepresentationHaveLowerRank(linked: LinkedBetree, idx: nat, ranking: Ranking) 
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    requires LBR.RankingIsTight(linked.diskView, ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures forall addr | addr in linked.ChildAtIdx(idx).Representation()
      :: addr in ranking && ranking[addr] < ranking[linked.root.value]
  {
    LBR.ChildAtIdxAcyclic(linked, idx);
    var subRoot := linked.ChildAtIdx(idx);
    forall addr | addr in subRoot.Representation()
    ensures addr in ranking && ranking[addr] < ranking[linked.root.value]
    {
      var r1 := subRoot.TheRanking();
      LBR.ReachableAddrsIgnoresRanking(subRoot, r1, ranking);
      if addr != subRoot.root.value {
        var numChildren := |subRoot.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => subRoot.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        var i :| 0 <= i < numChildren && addr in subTreeAddrs[i];
        var topAddr := linked.root.value;
        ReachableAddressesHaveLowerRank(subRoot, topAddr, ranking[topAddr], ranking);
      }
    }
  }

  // Theorem: The root node is not in the representation of any child subtree
  lemma RootNotInChildrenRepresentation(linked: LinkedBetree, idx: nat)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures linked.root.value !in linked.ChildAtIdx(idx).Representation()
  {
    LBR.ChildAtIdxAcyclic(linked, idx);
    assert linked.ChildAtIdx(idx).Acyclic();
    if linked.root.value in linked.ChildAtIdx(idx).Representation() {
      var tightRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
      ChildrenRepresentationHaveLowerRank(linked, idx, tightRanking);
      assert false;
    }
  }

  lemma InternalFlushMemtableDeletesOldRoot(linked: LinkedBetree, linked':LinkedBetree, newBuffer: Buffer, newRootAddr:Address)
    requires linked.Acyclic()
    requires linked'.Acyclic()
    requires linked.HasRoot()
    requires linked.diskView.IsFresh({newRootAddr})
    requires linked' == LB.InsertInternalFlushMemtableReplacement(linked, newBuffer, newRootAddr).BuildTightTree()
    ensures linked.root.value !in linked'.diskView.entries
  {
    var oldRootAddr := linked.root.value;
    var oldRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
    var newRanking := oldRanking[newRootAddr := oldRanking[linked.root.value]];
    var untightLinked := LB.InsertInternalFlushMemtableReplacement(linked, newBuffer, newRootAddr);
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
    LBR.ReachableAddrsIgnoresRanking(untightLinked, untightLinked.TheRanking(), newRanking);
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
      var oldRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
      var newRanking := oldRanking[step.newRootAddr := oldRanking[linked.root.value]];
      LBR.ReachableAddrsIgnoresRanking(linked', linked'.TheRanking(), newRanking);
      LBR.ReachableAddrsIgnoresRanking(linked, linked.TheRanking(), newRanking);
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
    LBR.BuildTightMaintainsRankingValidity(linked, ranking);
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
        LBR.ReachableAddrsIgnoresRanking(linked, linked.TheRanking(), ranking);
        var numChildren := |linked.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        var idx :| 0 <= idx < numChildren && addr in subTreeAddrs[idx];
        LBR.ChildAtIdxAcyclic(linked, idx);
        LBR.ReachableAddrsIgnoresRanking(linked.ChildAtIdx(idx), ranking, linked.ChildAtIdx(idx).TheRanking());
        BuildTightRepresentationContainsDiskView(linked.ChildAtIdx(idx), ranking);  // apply induction hypothesis
        LBR.BuildTightMaintainsRankingValidity(linked.ChildAtIdx(idx), ranking);
        LBR.ReachableAddrsIgnoresRanking(linked.ChildAtIdx(idx).BuildTightTree(), ranking, linked.ChildAtIdx(idx).BuildTightTree().TheRanking());
        assert linked.BuildTightTree().ChildAtIdx(idx).ValidRanking(ranking);  // trigger
        ReachableAddrsInAgreeingDisks(linked.BuildTightTree().ChildAtIdx(idx), linked.ChildAtIdx(idx).BuildTightTree(), ranking);
        ChildReachebleAddrsIsSubset(linked.BuildTightTree(), ranking, idx);  
        LBR.ReachableAddrsIgnoresRanking(linked.BuildTightTree(), ranking, linked.BuildTightTree().TheRanking());
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
    LBR.BuildTightMaintainsRankingValidity(linked, linked.TheRanking());
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
    var untightLinked :=  LB.InsertInternalFlushMemtableReplacement(v.betree.linked, newBuffer, step.newRootAddr);
    if v.betree.linked.HasRoot() {
      BuildTightGivesTightWrtRepresentation(untightLinked);
    }
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
    LBR.BuildTightPreservesWF(linked, ranking);
    LBR.BuildTightPreservesWF(linked.ChildAtIdx(idx), ranking);
    assert linked.ChildAtIdx(idx).BuildTightTree().ValidRanking(ranking);  // trigger
    assert linked.BuildTightTree().ChildAtIdx(idx).ValidRanking(ranking);  // trigger
    ReachableAddrsInAgreeingDisks(linked.ChildAtIdx(idx).BuildTightTree(), linked.BuildTightTree().ChildAtIdx(idx), ranking);
  }

  // Theorem: BuildTight does not change reachable set
  lemma ReachableAddrsIgnoresBuildTight(linked: LinkedBetree, ranking: Ranking)
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTree().WF()
    ensures linked.BuildTightTree().ValidRanking(ranking)
    ensures linked.BuildTightTree().ReachableAddrsUsingRanking(ranking)
      == linked.ReachableAddrsUsingRanking(ranking)
  {
    LBR.BuildTightMaintainsRankingValidity(linked, ranking);
    ReachableAddrsInAgreeingDisks(linked, linked.BuildTightTree(), ranking);
  }

  // Wrapper around ReachableAddrsIgnoresBuildTight
  lemma RepresentationIgnoresBuildTight(linked: LinkedBetree)
    requires linked.Acyclic()
    ensures linked.BuildTightTree().Acyclic()
    ensures linked.BuildTightTree().Representation()
      == linked.Representation()
  {
    var ranking := linked.TheRanking();
    LBR.BuildTightMaintainsRankingValidity(linked, ranking);
    LBR.ReachableAddrsIgnoresRanking(linked.BuildTightTree(), linked.BuildTightTree().TheRanking(), ranking);
    ReachableAddrsIgnoresBuildTight(linked, ranking);
  }

  // Theorem: The set of reachable addrs on path.Subpath().Substitute(..) is the same as
  // that on path.Substitute(..).ChildAtIdx(routeIdx)
  lemma ReachableAddrsOnSubpathRoute(path: Path, replacement: LinkedBetree, routeIdx: nat, pathAddrs: PathAddrs, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires routeIdx == Route(path.linked.Root().pivotTable, path.key)
    requires path.CanSubstitute(replacement, pathAddrs);
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    // Requirements of SubstitutePreservesWF and ReplacementAcyclicImpliesSubstituteAcyclic
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)

    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).Acyclic()  // prereq
    ensures path.Subpath().Substitute(replacement, pathAddrs[1..]).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).Representation()
      == path.Subpath().Substitute(replacement, pathAddrs[1..]).Representation()
  {
    // First dispatch of the prereqs
    LBR.ChildAtIdxAcyclic(path.Substitute(replacement, pathAddrs), routeIdx);
    ReplacementAcyclicImpliesSubstituteAcyclic(path.Subpath(), replacement, pathAddrs[1..], ranking);
    LBR.SubstitutePreservesWF(replacement, path.Subpath(), pathAddrs[1..], path.Subpath().Substitute(replacement, pathAddrs[1..]));
    
    // Now prove the actual goal
    var r1 := path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).TheRanking();
    var r2 := path.Subpath().Substitute(replacement, pathAddrs[1..]).TheRanking();
    var node := path.linked.Root();
    var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]);
    var newChildren := node.children[Route(node.pivotTable, path.key) := subtree.root];
    var newNode := LB.BetreeNode(node.buffers, node.pivotTable, newChildren);
    var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
    var newLinked := LB.LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView);
    var newLinkedChild := LB.LinkedBetree(subtree.root, newDiskView);
    ReachableAddrsInAgreeingDisks(newLinkedChild, subtree, r1);
    LBR.ReachableAddrsIgnoresRanking(path.Subpath().Substitute(replacement, pathAddrs[1..]), r1, r2);
  }

  // Theorem: Substitution does not change representation of subtrees not on the substitution path
  lemma ReachableAddrsNotOnSubpathRoute(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, idx: nat, ranking: Ranking) 
    requires path.Valid()
    requires 0 < path.depth
    requires 0 <= idx < |path.linked.Root().children|
    requires idx != Route(path.linked.Root().pivotTable, path.key)
    requires path.CanSubstitute(replacement, pathAddrs);
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    // RankingAfterSubstitution requirements
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)
    requires Set(pathAddrs) !! ranking.Keys
    requires PathAddrsFresh(path, replacement, pathAddrs)

    ensures path.linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).Acyclic()  // prereq
    ensures path.linked.ChildAtIdx(idx).Representation() ==
            path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).Representation()
  { 
    // Dispatch the prereqs
    LBR.ChildAtIdxAcyclic(path.linked, idx);
    LBR.ChildAtIdxAcyclic(path.Substitute(replacement, pathAddrs), idx);

    // Now prove the main goal
    var r1 := path.linked.ChildAtIdx(idx).TheRanking();
    var r2 := LBR.RankingAfterSubstitution(replacement, ranking, path, pathAddrs);
    var node := path.linked.Root();
    path.CanSubstituteSubpath(replacement, pathAddrs);
    var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]);
    var newChildren := node.children[Route(node.pivotTable, path.key) := subtree.root];
    var newNode := LB.BetreeNode(node.buffers, node.pivotTable, newChildren);
    var newDiskView := subtree.diskView.ModifyDisk(pathAddrs[0], newNode);
    var newLinked := LB.LinkedBetree(GenericDisk.Pointer.Some(pathAddrs[0]), newDiskView);
    LBR.ReachableAddrsIgnoresRanking(path.linked.ChildAtIdx(idx), r1, r2);
    LBR.ReachableAddrsIgnoresRanking(path.Substitute(replacement, pathAddrs).ChildAtIdx(idx), path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).TheRanking(), r2);
    // SubstitutePreservesWF gives us path.linked.diskView.AgreesWithDisk(newLinked.diskView)
    LBR.SubstitutePreservesWF(replacement, path, pathAddrs, newLinked);
    ReachableAddrsInAgreeingDisks(path.linked.ChildAtIdx(idx), newLinked.ChildAtIdx(idx), r2);
  }

  // Theorem: Representation includes subpath representation
  lemma RootRepresentationContainsSubpathRepresentation(path: Path) 
    requires path.Valid()
    requires path.linked.Acyclic()
    requires 0 < path.depth
    ensures path.Subpath().linked.Acyclic()
    ensures path.Subpath().linked.Representation() <= path.linked.Representation();
  {
    var r1 := path.linked.TheRanking();
    var r2 := path.Subpath().linked.TheRanking();
    var routeIdx := Route(path.linked.Root().pivotTable, path.key);
    var numChildren := |path.linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
    LBR.ReachableAddrsIgnoresRanking(path.linked.ChildAtIdx(routeIdx), r1, r2);
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    forall addr | addr in path.Subpath().linked.Representation()
    ensures addr in path.linked.Representation()
    {
      assert addr in subTreeAddrs[routeIdx];  // trigger
    }
  }

  // Theorem path.linked.Representation() includes path.Target().Representation()
  lemma RootRepresentationContainsTargetRepresentation(path: Path)
    requires path.Valid()
    ensures path.Target().Acyclic()
    ensures path.Target().Representation() <= path.linked.Representation()
    decreases path.depth
  {
    if 0 < path.depth {
      RootRepresentationContainsTargetRepresentation(path.Subpath());
      RootRepresentationContainsSubpathRepresentation(path);
    }
  }

  // Theorem: Representation contains child representation
  lemma ParentRepresentationContainsChildRepresentation(linked:LinkedBetree, idx: nat)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic()  // prereq
    ensures linked.ChildAtIdx(idx).Representation() <= linked.Representation()
  {
    LBR.ChildAtIdxAcyclic(linked, idx);
    var r1 := linked.TheRanking();
    var r2 :=linked.ChildAtIdx(idx).TheRanking();
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
    LBR.ReachableAddrsIgnoresRanking(linked.ChildAtIdx(idx), r1, r2);
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    forall addr | addr in linked.ChildAtIdx(idx).Representation()
    ensures addr in linked.Representation()
    {
      assert addr in subTreeAddrs[idx];  // trigger
    }
  }

  // Theorem: Subtree representations have null intersections
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
    // Dispatch the prereqs
    LBR.ChildAtIdxAcyclic(linked, i);
    LBR.ChildAtIdxAcyclic(linked, j);

    // TODO(tony): We don't actually know that our tree is not a DAG?
    // Copy on write will introduce DAGs into the disk, but the representation of 
    // should any pair of children of any node should not have overlaps, I think.
    /* 
      Update: This should be an invariant. Something like
      "for every node in the tree, any pair of its children have disjoint representations."
      It needs to be for every node in the tree and not just the root node, because there are 
      cases when we need this property for subpaths, e.g. in SubstituteDeletesAddrsOnPath
      when making a recursive call.
    */ 
    assume false;

    // Now prove the actual goal
    forall addr | addr in linked.ChildAtIdx(i).Representation() 
    ensures addr !in linked.ChildAtIdx(j).Representation()
    {}
  }

  // Theorem: path.AddrsOnPath() is either the current root, or in the subtree of path.Subpath
  lemma AddrsOnPathIsRootOrInRouteSubtree(path: Path, routeIdx: nat)
    requires path.Valid()
    requires routeIdx == Route(path.linked.Root().pivotTable, path.key)
    ensures path.linked.ChildAtIdx(routeIdx).Acyclic()
    ensures path.AddrsOnPath() <= {path.linked.root.value} + path.linked.ChildAtIdx(routeIdx).Representation()
    decreases path.depth
  {
    LBR.ChildAtIdxAcyclic(path.linked, routeIdx);
    if 0 < path.depth {
      var subRouteIdx := Route(path.Subpath().linked.Root().pivotTable, path.Subpath().key);
      AddrsOnPathIsRootOrInRouteSubtree(path.Subpath(), subRouteIdx);
      ParentRepresentationContainsChildRepresentation(path.Subpath().linked, subRouteIdx);
    }
  }

  // Theorem: Any address in a subtree's representation cannot be the root of the parent tree
  // Contrapositive of AddrInChildRepresentationImpliesNotRoot
  lemma AddrInChildRepresentationImpliesNotRoot(linked: LinkedBetree, idx: nat, addr: Address)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    requires linked.ChildAtIdx(idx).Acyclic()
    requires addr in linked.ChildAtIdx(idx).Representation()
    ensures addr != linked.root.value
  {
    RootNotInChildrenRepresentation(linked, idx);
  }

  // Theorem: Contrapositive of AddrInChildRepresentationImpliesNotRoot
  lemma RootAddrNotInChildRepresentation(linked: LinkedBetree, idx: nat)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    requires linked.ChildAtIdx(idx).Acyclic()
    ensures linked.root.value !in linked.ChildAtIdx(idx).Representation()
  {
    forall addr | addr in linked.ChildAtIdx(idx).Representation() 
    ensures addr != linked.root.value
    {
      AddrInChildRepresentationImpliesNotRoot(linked, idx, addr);
    }
  }

  // Theorem: Substituting an acyclic subtree into an acyclic tree produces an acyclic tree
  lemma ReplacementAcyclicImpliesSubstituteAcyclic(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, ranking: Ranking)
    requires path.Valid()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires replacement.ValidRanking(ranking)
    requires path.linked.root.value in ranking
    // Framing 
    requires SeqHasUniqueElems(pathAddrs)
    requires path.linked.diskView.IsSubDisk(replacement.diskView)
    requires PathAddrsFresh(path, replacement, pathAddrs)
    ensures path.Substitute(replacement, pathAddrs).Acyclic()
  {
    var tightRanking := LBR.BuildTightRanking(replacement, ranking);
    var newRanking := LBR.RankingAfterSubstitution(replacement, tightRanking, path, pathAddrs);
  }

  // Theorem: path.Addrs on path must be included in the root's representation
  lemma RepresentationContainsAddrsOnPath(path: Path) 
    requires path.Valid()
    ensures path.AddrsOnPath() <= path.linked.Representation()
    decreases path.depth
  {
    if 0 < path.depth {
      RepresentationContainsAddrsOnPath(path.Subpath());
      RootRepresentationContainsSubpathRepresentation(path);
    }
  }

  // Theorem: Rewriting ReachableAddrsUsingRanking as Representation
  lemma ParentRepresentationAsUnionOfChildren(linked: LinkedBetree) 
    requires linked.HasRoot()
    requires linked.Acyclic()
    ensures 
      && var n := |linked.Root().children|;
      && (forall i | 0 <= i < n :: linked.ChildAtIdx(i).Acyclic())
      && linked.Representation() == {linked.root.value} + Sets.UnionSeqOfSets(seq(n, i requires 0 <= i < n => linked.ChildAtIdx(i).Representation()))
  {
    var ranking := linked.TheRanking();
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    forall idx | 0 <= idx < numChildren 
    ensures  
      && linked.ChildAtIdx(idx).Acyclic()
      && subTreeAddrs[idx] == linked.ChildAtIdx(idx).Representation()
    {
      LBR.ChildAtIdxAcyclic(linked, idx);
      LBR.ReachableAddrsIgnoresRanking(linked.ChildAtIdx(idx), linked.ChildAtIdx(idx).TheRanking(), ranking);
    }
    var subTreeAddrsRepr := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).Representation());
    assert subTreeAddrs == subTreeAddrsRepr;  // trigger
  }

  // Theorem: the old path root is deleted from the representation after substitution
  lemma SubstituteDeletesOldRoot(path: Path, oldRoot: Address, replacement: LinkedBetree, pathAddrs: PathAddrs, ranking: Ranking) 
    requires path.Valid()
    requires replacement.Acyclic()
    requires oldRoot !in replacement.Representation()
    requires oldRoot !in pathAddrs
    // oldRoot is not in any subtree of path.linked
    requires forall i | 0 <= i < |path.linked.Root().children|
      :: path.linked.ChildAtIdx(i).Acyclic() && oldRoot !in path.linked.ChildAtIdx(i).Representation()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires replacement.ValidRanking(ranking)
    requires path.linked.root.value in ranking
    requires Set(pathAddrs) !! ranking.Keys

    ensures oldRoot !in path.Substitute(replacement, pathAddrs).Representation()
    decreases path.depth
  {
    if 0 < path.depth {
      path.CanSubstituteSubpath(replacement, pathAddrs);
      ReplacementAcyclicImpliesSubstituteAcyclic(path.Subpath(), replacement, pathAddrs[1..], ranking);

      var subpath := path.Subpath();
      var routeIdx := Route(path.linked.Root().pivotTable, path.key);
      forall i | 0 <= i < |subpath.linked.Root().children|
      ensures subpath.linked.ChildAtIdx(i).Acyclic() && oldRoot !in subpath.linked.ChildAtIdx(i).Representation()
      { 
        LBR.ChildAtIdxAcyclic(subpath.linked, i);
        // Prove that oldRoot !in subpath.linked.Representation()
        assert oldRoot !in path.linked.ChildAtIdx(routeIdx).Representation();  // trigger
        // Prove that oldRoot !in subpath.linked.ChildAtIdx(i).Representation();
        ParentRepresentationContainsChildRepresentation(subpath.linked, i);
      }
      SubstituteDeletesOldRoot(subpath, oldRoot, replacement, pathAddrs[1..], ranking);
      var numChildren := |path.Substitute(replacement, pathAddrs).Root().children|;
      forall idx | 0 <= idx < numChildren
      ensures oldRoot !in path.Substitute(replacement, pathAddrs).ChildAtIdx(idx).Representation()
      {
        if idx == routeIdx {
          ReachableAddrsOnSubpathRoute(path, replacement, routeIdx, pathAddrs, ranking);
        } else {
          ReachableAddrsNotOnSubpathRoute(path, replacement, pathAddrs, idx, ranking);
        }
      }
      ParentRepresentationAsUnionOfChildren(path.Substitute(replacement, pathAddrs));
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.Substitute(replacement, pathAddrs).ChildAtIdx(i).Representation());
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    }
  }

  // Theorem: Any address in the representation after substitution could not have been on
  // on the substitution path
  lemma {:timeLimitMultiplier 3} SubstituteDeletesAddrsOnPath(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, addr: Address, ranking: Ranking)
    requires path.Valid()
    requires replacement.Acyclic()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.AddrsOnPath() !! replacement.Representation()
    requires Set(pathAddrs) !! ranking.Keys  // required by ReachableAddrsNotOnSubpathRoute
    requires addr in path.Substitute(replacement, pathAddrs).Representation()
    
    // Requirements of ReplacementAcyclicImpliesSubstituteAcyclic
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)

    ensures addr !in path.AddrsOnPath()
    decreases path.depth
  { 
    if 0 < path.depth {
      var linkedAftSubst := path.Substitute(replacement, pathAddrs);
      var r1 := linkedAftSubst.TheRanking();
      var numChildren := |linkedAftSubst.Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linkedAftSubst.ChildAtIdx(i).ReachableAddrsUsingRanking(r1));
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      if addr == linkedAftSubst.root.value {
        // If addr is root after substitution
        RepresentationContainsAddrsOnPath(path);
      } else {
        // Else, addr must be in a subtree after substitution
        var idx :| 0 <= idx < numChildren && addr in subTreeAddrs[idx];
        var routeIdx := Route(path.linked.Root().pivotTable, path.key);
        if idx == routeIdx {
          // If addr is in the new subtree
          ReplacementAcyclicImpliesSubstituteAcyclic(path.Subpath(), replacement, pathAddrs[1..], ranking);
          LBR.ChildAtIdxAcyclic(linkedAftSubst, routeIdx);
          LBR.ReachableAddrsIgnoresRanking(
              linkedAftSubst.ChildAtIdx(routeIdx), 
              linkedAftSubst.ChildAtIdx(routeIdx).TheRanking(), r1);
          ReachableAddrsOnSubpathRoute(path, replacement, routeIdx, pathAddrs, ranking);
          SubstituteDeletesAddrsOnPath(path.Subpath(), replacement, pathAddrs[1..], addr, ranking);
          forall i | 0 <= i < |path.linked.Root().children|
          ensures path.linked.ChildAtIdx(i).Acyclic() && path.linked.root.value !in path.linked.ChildAtIdx(i).Representation()
          {
            RootNotInChildrenRepresentation(path.linked, i);
          }
          SubstituteDeletesOldRoot(path, path.linked.root.value, replacement, pathAddrs, ranking);
        } else {
          // Else, addr is in an old legacy subtree, hence it is not in the substitution path
          LBR.ChildAtIdxAcyclic(linkedAftSubst, idx);
          LBR.ReachableAddrsIgnoresRanking(linkedAftSubst.ChildAtIdx(idx), linkedAftSubst.ChildAtIdx(idx).TheRanking(), r1);
          ReachableAddrsNotOnSubpathRoute(path, replacement, pathAddrs, idx, ranking); 
          SubtreeRepresentationsAreDisjoint(path.linked, idx, routeIdx);
          AddrsOnPathIsRootOrInRouteSubtree(path, routeIdx);
          forall i | 0 <= i < |path.linked.Root().children|
          ensures path.linked.ChildAtIdx(i).Acyclic() && path.linked.root.value !in path.linked.ChildAtIdx(i).Representation()
          {
            RootNotInChildrenRepresentation(path.linked, i);
          }
          SubstituteDeletesOldRoot(path, path.linked.root.value, replacement, pathAddrs, ranking);
        }
      }      
    }
  }

  // Theorem: pathAddrs is a subset of path.Substitute(replacement, pathAddrs)
  lemma RepresentationAfterSubstituteContainsPathAddrs(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, ranking: Ranking)
    requires path.Valid()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires replacement.ValidRanking(ranking)
    requires path.linked.root.value in ranking
    // Framing 
    requires path.linked.diskView.IsSubDisk(replacement.diskView)
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()  // prereq
    ensures Set(pathAddrs) <= path.Substitute(replacement, pathAddrs).Representation()
    decreases path.depth
  {
    if 0 < path.depth {
      ReplacementAcyclicImpliesSubstituteAcyclic(path.Subpath(), replacement, pathAddrs[1..], ranking);
      RepresentationAfterSubstituteContainsPathAddrs(path.Subpath(), replacement, pathAddrs[1..], ranking);
      var routeIdx := Route(path.linked.Root().pivotTable, path.key);
      ReachableAddrsOnSubpathRoute(path, replacement, routeIdx, pathAddrs, ranking);
      ParentRepresentationContainsChildRepresentation(path.Substitute(replacement, pathAddrs), routeIdx);
    }
  }

  // Theorem: Representation of path.Substitute(..) includes that of replacement
  lemma RepresentationAfterSubstituteContainsReplacement(path: Path, replacement: LinkedBetree, pathAddrs: PathAddrs, ranking: Ranking)
    requires path.Valid()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires replacement.Acyclic()
    // Requirements of ReplacementAcyclicImpliesSubstituteAcyclic
    requires replacement.ValidRanking(ranking)
    requires path.linked.root.value in ranking
    requires path.linked.diskView.IsSubDisk(replacement.diskView)
    requires PathAddrsFresh(path, replacement, pathAddrs)
    ensures path.Substitute(replacement, pathAddrs).Acyclic()  // prereq
    ensures replacement.Representation() <= path.Substitute(replacement, pathAddrs).Representation()
    decreases path.depth
  {
    ReplacementAcyclicImpliesSubstituteAcyclic(path, replacement, pathAddrs, ranking);
    if 0 < path.depth {
      RepresentationAfterSubstituteContainsReplacement(path.Subpath(), replacement, pathAddrs[1..], ranking);
      var routeIdx := Route(path.linked.Root().pivotTable, path.key);
      ReachableAddrsOnSubpathRoute(path, replacement, routeIdx, pathAddrs, ranking);
      ParentRepresentationContainsChildRepresentation(path.Substitute(replacement, pathAddrs), routeIdx);
    }
  }

  // Theorem: Child at Route(path.linked.Root().pivotTable, path.key) is same as path.Subpath()
  lemma SubpathEquivToChildAtRouteIdx(path: Path)
    requires path.Valid()
    requires 0 < path.depth
    ensures 
      && var routeIdx := Route(path.linked.Root().pivotTable, path.key);
      && path.linked.ChildAtIdx(routeIdx) == path.Subpath().linked
  {}

  // Theorem: path.AddrsOnPath() are valid diskview entries
  lemma AddrsOnPathInDiskView(path: Path) 
    requires path.Valid()
    ensures path.AddrsOnPath() <= path.linked.diskView.entries.Keys
    decreases path.depth
  {
    if 0 < path.depth {
      AddrsOnPathInDiskView(path.Subpath());
    }
  }

  // Theorem: Change in representation after switching out the root of the tree
  lemma RepresentationAfterSwitchingRoot(linked: LinkedBetree, linked': LinkedBetree, replacementAddr: Address, ranking: Ranking)
    requires linked.WF() && linked'.WF()
    requires linked.ValidRanking(ranking) && linked'.ValidRanking(ranking)
    requires linked.HasRoot() && linked'.HasRoot()
    requires linked'.root.value == replacementAddr
    requires linked'.Root().children == linked.Root().children
    requires linked'.diskView.AgreesWithDisk(linked.diskView)
    requires linked.diskView.IsFresh({replacementAddr})  // Framing
    ensures linked'.Representation() == linked.Representation() + {replacementAddr} - {linked.root.value}
  {
    var numChildren := |linked.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    var subTreeAddrs' := seq(numChildren, i requires 0 <= i < numChildren => linked'.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    forall i | 0 <= i < numChildren 
    ensures 
      && subTreeAddrs'[i] == subTreeAddrs[i] 
      && linked.root.value !in subTreeAddrs[i]
    {
      ReachableAddrsInAgreeingDisks(linked.ChildAtIdx(i), linked'.ChildAtIdx(i), ranking);
      LBR.ChildAtIdxAcyclic(linked, i);
      RootAddrNotInChildRepresentation(linked, i);
      LBR.ReachableAddrsIgnoresRanking(linked.ChildAtIdx(i), linked.ChildAtIdx(i).TheRanking(), ranking);
    }
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs');
    LBR.ReachableAddrsIgnoresRanking(linked, ranking, linked.TheRanking());
    LBR.ReachableAddrsIgnoresRanking(linked', ranking, linked'.TheRanking());
  }

  // Expands path.Substitute().ChildAtIdx(routeIdx).Representation into its components
  lemma SubstitutedBranchRepresentation(path: Path, replacement: LinkedBetree, 
    pathAddrs: PathAddrs, replacementAddr: Address, routeIdx: nat, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires routeIdx == Route(path.linked.Root().pivotTable, path.key);
    requires replacement.Acyclic()
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).Acyclic()
    // Requirements of // Requirements of SubstitutePreservesWF and ReplacementAcyclicImpliesSubstituteAcyclic. 
    // Would be the result of some lemma such as RankingAfterInsertCompactReplacement
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)

    // Induction hypothesis of ReprAfterSubstituteCompactReplacement
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).Representation()
            == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()  
    ensures path.Subpath().linked.Acyclic()
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).Acyclic()
    ensures path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).Representation()
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()
  {    
    LBR.ChildAtIdxAcyclic(path.Substitute(replacement, pathAddrs), routeIdx);    
    LBR.ChildAtIdxAcyclic(path.Substitute(replacement, pathAddrs), routeIdx);
    ReachableAddrsOnSubpathRoute(path, replacement, routeIdx, pathAddrs, ranking); 
  }

  // Tony: this lemma is sprawling massive...
  lemma {:timeLimitMultiplier 2} ReprAfterSubstituteCompactReplacement(path: Path, compactedBuffers: BufferStack, replacement: LinkedBetree, replacementRanking: Ranking, pathAddrs: PathAddrs, replacementAddr: Address)
    requires path.Valid()
    requires path.Target().Root().buffers.Equivalent(compactedBuffers)
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires replacement == LB.InsertCompactReplacement(path.Target(), compactedBuffers, replacementAddr)
    requires replacement.ValidRanking(replacementRanking)
    requires replacement.Acyclic()
    requires path.AddrsOnPath() !! replacement.Representation()

    //RankingAfterSubstitution requirements
    requires path.linked.root.value in replacementRanking
    requires Set(pathAddrs) !! replacementRanking.Keys
    requires PathAddrsFresh(path, replacement, pathAddrs)

    requires path.CanSubstitute(replacement, pathAddrs)
    ensures path.Substitute(replacement, pathAddrs).Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
            == path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
    decreases path.depth
  {
    var ranking := LBR.RankingAfterSubstitution(replacement, replacementRanking, path, pathAddrs);
    LBR.BuildTightMaintainsRankingValidity(path.Substitute(replacement, pathAddrs), ranking);
    if path.depth == 0 {
      RepresentationAfterSwitchingRoot(path.linked, replacement.BuildTightTree(), replacementAddr, ranking);
    } else {
      ReprAfterSubstituteCompactReplacement(path.Subpath(), compactedBuffers, replacement, replacementRanking, pathAddrs[1..], replacementAddr);
      // Induction hypothesis:
      // assert path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      //       == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath();
      var node := path.linked.Root();
      var routeIdx := Route(node.pivotTable, path.key);
      var numChildren := |path.Substitute(replacement, pathAddrs).BuildTightTree().Root().children|;
      var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.Substitute(replacement, pathAddrs).BuildTightTree().ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
      Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
      var tightRanking := LBR.BuildTightRanking(path.linked, path.linked.TheRanking());
      LBR.ValidRankingAllTheWayDown(tightRanking, path);
      ReprAfterSubstituteCompactReplacementInduction1(path, replacement, pathAddrs, replacementAddr, replacementRanking);
      ReprAfterSubstituteCompactReplacementInduction2(path, replacement, pathAddrs, replacementAddr, replacementRanking);
    }
  }

  // This juicy lemma requires a lot of juice
  lemma {:timeLimitMultiplier 2} ReprAfterSubstituteCompactReplacementInduction1(path: Path, replacement: LinkedBetree, 
      pathAddrs: PathAddrs, replacementAddr: Address, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Acyclic()
    requires replacement.Acyclic()
    requires path.AddrsOnPath() !! replacement.Representation()
    // Requirements of Ranking. Would be the result of some lemma such as RankingAfterInsertCompactReplacement
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)
    requires Set(pathAddrs) !! ranking.Keys

    // Induction hypothesis
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()
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
        var numChildren := |linkedAftSubst.Root().children|;
        var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => linkedAftSubst.ChildAtIdx(i).ReachableAddrsUsingRanking(linkedAftSubst.TheRanking()));
        Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
        var idx :| 0 <= idx < numChildren && addr in subTreeAddrs[idx];
        LBR.ChildAtIdxAcyclic(linkedAftSubst, idx);
        var routeIdx := Route(path.linked.Root().pivotTable, path.key);
        if idx == routeIdx {  
          // If addr is in the subtree that is swapped in during substitution
          RepresentationIgnoresBuildTight(path.Subpath().Substitute(replacement, pathAddrs[1..]));
          SubstitutedBranchRepresentation(path, replacement, pathAddrs, replacementAddr, routeIdx, ranking);
          LBR.ReachableAddrsIgnoresRanking(path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx), path.Substitute(replacement, pathAddrs).ChildAtIdx(routeIdx).TheRanking(), linkedAftSubst.TheRanking());
          RootRepresentationContainsSubpathRepresentation(path);
          assert addr !in path.AddrsOnPath() by {  // trigger
            LBR.ReachableAddrsIgnoresRanking(linkedAftSubst.ChildAtIdx(routeIdx), linkedAftSubst.ChildAtIdx(routeIdx).TheRanking(), linkedAftSubst.TheRanking());
            SubstituteDeletesAddrsOnPath(path, replacement, pathAddrs, addr, ranking);
            assert addr != path.linked.root.value;
          }
        } else {  
          // Else addr is in one of the original subtrees
          // First, prove that addr in path.linked.Representation();
          LBR.ReachableAddrsIgnoresRanking(linkedAftSubst.ChildAtIdx(idx), linkedAftSubst.ChildAtIdx(idx).TheRanking(), linkedAftSubst.TheRanking());
          ReachableAddrsNotOnSubpathRoute(path, replacement, pathAddrs, idx, ranking);
          ParentRepresentationContainsChildRepresentation(path.linked, idx);

          // Next, Prove that addr not in path.AddrsOnPath();
          AddrInChildRepresentationImpliesNotRoot(path.linked, idx, addr);
          AddrsOnPathIsRootOrInRouteSubtree(path, routeIdx);
          SubtreeRepresentationsAreDisjoint(path.linked, idx, routeIdx);
        }
      } else {
        AddrsOnPathInDiskView(path);
      }
    }
  }

  // This juicy lemma requires a lot of juice
  lemma {:timeLimitMultiplier 2} ReprAfterSubstituteCompactReplacementInduction2(path: Path, replacement: LinkedBetree, 
    pathAddrs: PathAddrs, replacementAddr: Address, ranking: Ranking)
    requires path.Valid()
    requires 0 < path.depth
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires PathAddrsFresh(path, replacement, pathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).Acyclic()
    requires replacement.Acyclic()
    requires replacementAddr in replacement.Representation()
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Acyclic()
    // Requirements of Ranking. Would be the result of some lemma such as RankingAfterInsertCompactReplacement
    requires path.linked.root.value in ranking
    requires replacement.ValidRanking(ranking)
    requires Set(pathAddrs) !! ranking.Keys

    // Induction hypothesis of ReprAfterSubstituteCompactReplacement
    requires path.Subpath().Substitute(replacement, pathAddrs[1..]).BuildTightTree().Representation()
      == path.Subpath().linked.Representation() + Set(pathAddrs[1..]) + {replacementAddr} - path.Subpath().AddrsOnPath()

    ensures path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
      <= path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
  {
    forall addr | addr in path.linked.Representation() + Set(pathAddrs) + {replacementAddr} - path.AddrsOnPath()
    ensures addr in path.Substitute(replacement, pathAddrs).Representation()
    {
      if addr in Set(pathAddrs) {
        RepresentationAfterSubstituteContainsPathAddrs(path, replacement, pathAddrs, ranking);
      } else if addr == replacementAddr {
        RepresentationAfterSubstituteContainsReplacement(path, replacement, pathAddrs, ranking);
      } else if addr in path.linked.Representation() {
        /* This is the tricky case
        addr is not path.linked.root, because root is in path.AddrsOnPath().
        Hence, addr is in one of the children subtrees of path.linked.Root()
        If addr is not on substitution path, the addr in path.Substitute() by ReachableAddrsNotOnSubpathRoute
        Else, addr is in substitution path, and must be in path.Subpath().linked.Representation().
        Then by SubstitutedBranchRepresentation, addr is in subTreeAddrs[routeIdx] of path.Substitute().Repr().
        Then addr is in path.Substitute(..).Representation() by definition of Representation
        */
        var numChildren := |path.linked.Root().children|;
        var oldSubTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.linked.ChildAtIdx(i).ReachableAddrsUsingRanking(path.linked.TheRanking()));
        Sets.UnionSeqOfSetsSoundness(oldSubTreeAddrs);
        var idx :| 0 <= idx < numChildren && addr in oldSubTreeAddrs[idx];
        var routeIdx := Route(path.linked.Root().pivotTable, path.key);
        LBR.ChildAtIdxAcyclic(path.linked, idx);
        LBR.ReachableAddrsIgnoresRanking(path.linked.ChildAtIdx(idx), path.linked.ChildAtIdx(idx).TheRanking(), path.linked.TheRanking());
        if idx != routeIdx {
          ReachableAddrsNotOnSubpathRoute(path, replacement, pathAddrs, idx, ranking); 
          ParentRepresentationContainsChildRepresentation(path.Substitute(replacement, pathAddrs), idx);
        } else {
          // Else addr is on substitution path
          SubpathEquivToChildAtRouteIdx(path);
          RepresentationIgnoresBuildTight(path.Subpath().Substitute(replacement, pathAddrs[1..]));
          SubstitutedBranchRepresentation(path, replacement, pathAddrs, replacementAddr, routeIdx, ranking);
          ParentRepresentationContainsChildRepresentation(path.Substitute(replacement, pathAddrs), routeIdx);
        }
      }
    }
    RepresentationIgnoresBuildTight(path.Substitute(replacement, pathAddrs));
  }

  // Prove step.path.AddrsOnPath() !! replacement.Representation(); 
  lemma InsertCompactReplacementExcludesAddrsOnPath(path: Path, replacement: LinkedBetree, compactedBuffers: BufferStack, replacementAddr: Address)
    requires path.Valid()
    requires path.Target().Root().buffers.Equivalent(compactedBuffers)
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires replacement == LB.InsertCompactReplacement(path.Target(), compactedBuffers, replacementAddr);
    requires replacement.Acyclic()
    ensures path.AddrsOnPath() !! replacement.Representation()
    decreases path.depth
  {
    var ranking := path.linked.TheRanking();
    var replacementRanking := replacement.TheRanking();
    LBR.ValidRankingAllTheWayDown(ranking, path);
    var rootAddr := path.linked.root.value;
    var numChildren := |replacement.Root().children|;
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => replacement.ChildAtIdx(i).ReachableAddrsUsingRanking(replacementRanking));
    if path.depth == 0 {
      // Base case
      forall idx | 0 <= idx < numChildren
      ensures rootAddr !in subTreeAddrs[idx]
      {
        if rootAddr in subTreeAddrs[idx] {
          LBR.ChildAtIdxAcyclic(path.Target(), idx);
          ReachableAddrsInAgreeingDisks(path.Target().ChildAtIdx(idx), replacement.ChildAtIdx(idx), replacementRanking);
          LBR.ReachableAddrsIgnoresRanking(path.linked.ChildAtIdx(idx), path.linked.ChildAtIdx(idx).TheRanking(), replacementRanking);
          RootAddrNotInChildRepresentation(path.linked, idx);
          assert false;
        }
      }
    } else {
      // Recursive case
      InsertCompactReplacementExcludesAddrsOnPath(path.Subpath(), replacement, compactedBuffers, replacementAddr);
      forall idx | 0 <= idx < numChildren
      ensures rootAddr !in subTreeAddrs[idx]
      {
        if rootAddr in subTreeAddrs[idx] {
          LBR.ChildAtIdxAcyclic(path.Target(), idx);
          ReachableAddrsInAgreeingDisks(path.Target().ChildAtIdx(idx), replacement.ChildAtIdx(idx), replacementRanking);
          LBR.ReachableAddrsIgnoresRanking(path.Target().ChildAtIdx(idx), path.Target().ChildAtIdx(idx).TheRanking(), replacementRanking);
          ParentRepresentationContainsChildRepresentation(path.Target(), idx);
          RootRepresentationContainsTargetRepresentation(path.Subpath());
          var routeIdx := Route(path.linked.Root().pivotTable, path.key);
          RootAddrNotInChildRepresentation(path.linked, routeIdx);
          assert false;
        }
      }
    }
    Sets.UnionSeqOfSetsSoundness(subTreeAddrs);
  }

  lemma InternalCompactMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v'.betree.linked.Acyclic()
    ensures ValidRepr(v')
  {
    var linked := v.betree.linked;
    var replacement := LB.InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    var linkedRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
    LBR.ValidRankingAllTheWayDown(linkedRanking, step.path);
    var replacementRanking := LBR.RankingAfterInsertCompactReplacement(step.path.Target(), step.compactedBuffers, linkedRanking, step.targetAddr);
    if linked.HasRoot() {
      InsertCompactReplacementExcludesAddrsOnPath(step.path, replacement, step.compactedBuffers, step.targetAddr);
      ReprAfterSubstituteCompactReplacement(step.path, step.compactedBuffers, replacement, replacementRanking, step.pathAddrs, step.targetAddr); 
    }
  }

  lemma InternalCompactMaintainsTightDisk(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v'.betree.linked.Acyclic()
    ensures v'.betree.linked.DiskIsTightWrtRepresentation()
  {
    if v.betree.linked.HasRoot() {
      var untightLinked' := step.path.Substitute(
            LB.InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr),
            step.pathAddrs
        );
      BuildTightGivesTightWrtRepresentation(untightLinked');
    }
  }

  lemma ReprAfterSubstituteFlushReplacement(
    path: Path, replacement: LinkedBetree, childIdx: nat, replacementAddr: Address, replacementChildAddr: Address, 
    pathAddrs: PathAddrs, replacementRanking: Ranking)
    requires path.Valid()
    requires path.Target().Root().OccupiedChildIndex(childIdx)
    requires replacement == LB.InsertFlushReplacement(path.Target(), childIdx, replacementAddr, replacementChildAddr)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires replacement.Acyclic()
    requires replacement.ValidRanking(replacementRanking)

    // Framing
    requires replacementAddr != replacementChildAddr
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires path.Target().diskView.IsFresh({replacementChildAddr})
    requires path.AddrsOnPath() !! replacement.Representation()

    //RankingAfterSubstitution requirements
    requires path.linked.root.value in replacementRanking
    requires Set(pathAddrs) !! replacementRanking.Keys
    requires PathAddrsFresh(path, replacement, pathAddrs)

    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()  // prereq
    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
            == path.linked.Representation() + Set(pathAddrs) + {replacementAddr, replacementChildAddr} 
              - path.AddrsOnPath() - {path.Target().ChildAtIdx(childIdx).root.value}
    decreases path.depth
  {
    var ranking := LBR.RankingAfterSubstitution(replacement, replacementRanking, path, pathAddrs);
    LBR.BuildTightMaintainsRankingValidity(path.Substitute(replacement, pathAddrs), ranking);
    if path.depth == 0 {
      ReprAfterSubstituteFlushReplacementBaseCase(path, replacement, childIdx, replacementAddr, replacementChildAddr, pathAddrs, ranking);
    } else {
      assume false;
      ReprAfterSubstituteFlushReplacement(path.Subpath(), replacement, childIdx, replacementAddr, replacementChildAddr, pathAddrs[1..], ranking);
    }
  }

  lemma ReprAfterSubstituteFlushReplacementBaseCase(
    path: Path, replacement: LinkedBetree, childIdx: nat, replacementAddr: Address, replacementChildAddr: Address, 
    pathAddrs: PathAddrs, ranking: Ranking)
    requires path.Valid()
    requires path.depth == 0  // base case
    requires path.Target().Root().OccupiedChildIndex(childIdx)
    requires replacement == LB.InsertFlushReplacement(path.Target(), childIdx, replacementAddr, replacementChildAddr)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).Acyclic()
    requires path.Substitute(replacement, pathAddrs).ValidRanking(ranking)
    requires path.Substitute(replacement, pathAddrs).BuildTightTree().Acyclic()
    // Framing
    requires replacementAddr != replacementChildAddr;
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires path.Target().diskView.IsFresh({replacementChildAddr})
    requires path.AddrsOnPath() !! replacement.Representation()

    ensures path.Substitute(replacement, pathAddrs).BuildTightTree().Representation()
            == path.linked.Representation() + Set(pathAddrs) + {replacementAddr, replacementChildAddr} 
               - path.AddrsOnPath() - {path.Target().ChildAtIdx(childIdx).root.value}
  {
    var numChildren := |replacement.Root().children|;
    var subTreeAddrs' := seq(numChildren, i requires 0 <= i < numChildren => replacement.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));
    var subTreeAddrs := seq(numChildren, i requires 0 <= i < numChildren => path.linked.ChildAtIdx(i).ReachableAddrsUsingRanking(ranking));

    forall idx | 
      && 0 <= idx < numChildren 
      && idx != childIdx
    ensures 
      && subTreeAddrs[idx] == subTreeAddrs'[idx]
      && path.linked.ChildAtIdx(childIdx).root.value !in subTreeAddrs[idx]
    {
      ReachableAddrsInAgreeingDisks(path.linked.ChildAtIdx(idx), replacement.ChildAtIdx(idx), ranking);
      assert subTreeAddrs[idx] == subTreeAddrs'[idx];
      // TODO(tony): The following fact should come from the invariant replacement to lemma SubtreeRepresentationsAreDisjoint
      assume path.linked.ChildAtIdx(childIdx).root.value !in subTreeAddrs[idx];
    }

    assert subTreeAddrs'[childIdx] 
        == subTreeAddrs[childIdx] + {replacementChildAddr} - {path.linked.ChildAtIdx(childIdx).root.value}
    by {
      RepresentationAfterSwitchingRoot(path.linked.ChildAtIdx(childIdx), replacement.ChildAtIdx(childIdx), replacementChildAddr, ranking);
      LBR.ReachableAddrsIgnoresRanking(path.linked.ChildAtIdx(childIdx), path.linked.ChildAtIdx(childIdx).TheRanking(), ranking);
      LBR.ReachableAddrsIgnoresRanking(replacement.ChildAtIdx(childIdx), replacement.ChildAtIdx(childIdx).TheRanking(), ranking);
    }
    Sets.SetSeqMath(subTreeAddrs, subTreeAddrs', childIdx, {replacementChildAddr}, {path.linked.ChildAtIdx(childIdx).root.value});
    LBR.ReachableAddrsIgnoresRanking(path.linked, ranking, path.linked.TheRanking());
    LBR.ReachableAddrsIgnoresRanking(replacement, ranking, replacement.TheRanking());
    RepresentationIgnoresBuildTight(path.Substitute(replacement, pathAddrs));
  }

  // Prove step.path.AddrsOnPath() !! replacement.Representation(); 
  lemma InsertFlushReplacementExcludesAddrsOnPath(
    path: Path, replacement: LinkedBetree, childIdx: nat, replacementAddr: Address, replacementChildAddr: Address)
    requires path.Valid()
    requires path.Target().Root().OccupiedChildIndex(childIdx)
    requires replacement == LB.InsertFlushReplacement(path.Target(), childIdx, replacementAddr, replacementChildAddr)
    requires path.Target().diskView.IsFresh({replacementAddr})
    requires replacement.Acyclic()
    ensures path.AddrsOnPath() !! replacement.Representation()
    decreases path.depth
  {
    assume false;
  }

  lemma InternalFlushMaintainsRepr(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    requires v'.betree.linked.Acyclic()
    ensures ValidRepr(v')
  {
    var linked := v.betree.linked;
    var replacement := LB.InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
    var linkedRanking := LBR.BuildTightRanking(linked, linked.TheRanking());
    LBR.ValidRankingAllTheWayDown(step.path.linked.TheRanking(), step.path);
    var replacementRanking := LBR.RankingAfterInsertFlushReplacement(step.path.Target(), linkedRanking, step.childIdx, step.targetAddr, step.targetChildAddr);
    if v.betree.linked.HasRoot() {
      InsertFlushReplacementExcludesAddrsOnPath(step.path, replacement, step.childIdx, step.targetAddr, step.targetChildAddr);
      ReprAfterSubstituteFlushReplacement(step.path, replacement, step.childIdx, step.targetAddr, step.targetChildAddr, step.pathAddrs, replacementRanking);
    }
  }

  lemma InternalFlushMaintainsTightDisk(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    requires v'.betree.linked.Acyclic()
    ensures v'.betree.linked.DiskIsTightWrtRepresentation()
  {
    assume false;
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
        LBR.InvNextInternalGrowStep(I(v), I(v'), lbl.I(), step.I());
        InternalGrowMaintainsRepr(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalSplitStep(_, _, _, _) => {
        // TODO(tony)
        assume false;
        assert Inv(v');
      }
      case InternalFlushStep(_, _, _, _, _) => {
        LBR.InvNextInternalFlushStep(I(v), I(v'), lbl.I(), step.I());
        InternalFlushMaintainsRepr(v, v', lbl, step);
        InternalFlushMaintainsTightDisk(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalFlushMemtableStep(_) => {
        LBR.InvNextInternalFlushMemtableStep(I(v), I(v'), lbl.I(), step.I());
        InternalFlushMemtableMaintainsRepr(v, v', lbl, step);
        InternalFlushMemtableMaintainsTightDisk(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalCompactStep(_, _, _, _) => {
        LBR.InvNextInternalCompactStep(I(v), I(v'), lbl.I(), step.I());
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
    requires LBR.InvLinkedBetree(gcBetree.I().value)
    ensures Inv(v)
    ensures LB.Init(I(v), gcBetree.I())
  {
    InvInit(v, gcBetree);
    LBR.InitRefines(I(v), gcBetree.I());
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures LB.Next(I(v), I(v'), lbl.I())
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    assert LB.NextStep(I(v), I(v'), lbl.I(), step.I());
  }
}
