// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Base/SequencesOfMaps.i.dfy"
include "../../lib/Base/Sets.i.dfy"
include "Domain.i.dfy"

module LinkedBetreeRefinement {
  import opened Options
  import Mathematics
  import opened Sequences  // Set
  import opened Maps  // Set
  import opened Sets
  import opened SequencesOfMaps
  import opened KeyType
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Buffers
  import GenericDisk
  import opened BoundedPivotsLib
  import opened LinkedBetreeMod
  import opened StampedMod
  import PivotBetree
  import DomainMod

  type Ranking = GenericDisk.Ranking

  lemma EmptyLinkedBtreeAcyclic()
    ensures EmptyLinkedBetree().Acyclic()
  {
    assert EmptyLinkedBetree().ValidRanking(map[]);
  }

  function ILbl(lbl: TransitionLabel) : PivotBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => PivotBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => PivotBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => PivotBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => PivotBetree.FreezeAsLabel(
        if stampedBetree.value.WF() && stampedBetree.value.Acyclic()
        then IStampedBetree(stampedBetree)
        else
          EmptyLinkedBtreeAcyclic();
          IStampedBetree(EmptyImage())  // "silly" case, since we never interpret non-(WF+Acyclic) things
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  lemma ChildIdxCommutesWithI(linked: LinkedBetree, idx: nat, r: Ranking) 
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.ValidRanking(r)
    requires linked.Root().ValidChildIndex(idx)
    requires ILinkedBetreeNode(linked, r).ValidChildIndex(idx)
    ensures ILinkedBetreeNode(linked.ChildAtIdx(idx), r) == ILinkedBetreeNode(linked, r).children[idx]
  {}

  lemma ChildIdxAcyclic(linked: LinkedBetree, idx: nat) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic();
  {
    var ranking := linked.TheRanking();  // witness
    assert linked.ChildAtIdx(idx).ValidRanking(ranking);
  }

  lemma ChildKeyAcyclic(linked: LinkedBetree, key: Key) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().KeyInDomain(key)
    ensures linked.ChildForKey(key).Acyclic()
  {
    var ranking := linked.TheRanking();  // witness
    assert linked.ChildForKey(key).ValidRanking(ranking);
  }

  lemma ILinkedWF(linked: LinkedBetree, ranking: Ranking) 
    requires linked.Acyclic()
    requires linked.ValidRanking(ranking)
    ensures ILinkedBetree(linked).WF()
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() {
      forall idx: nat | linked.Root().ValidChildIndex(idx) 
      ensures ILinkedBetree(linked).children[idx].WF()
      {
        ChildIdxAcyclic(linked, idx);
        ILinkedWF(linked.ChildAtIdx(idx), ranking);
        ChildIdxCommutesWithI(linked, idx, linked.TheRanking());
      }
      ILinkedBetreeIgnoresRanking(linked, ranking, linked.TheRanking());
    }
  }

  // wrapper
  function ILinkedBetree(linked: LinkedBetree) : (out: PivotBetree.BetreeNode)
    requires linked.WF()
    requires linked.Acyclic()
    ensures out.WF()
  {
    ILinkedBetreeNode(linked, linked.TheRanking())
  }

  function IChildren(linked: LinkedBetree, ranking: Ranking) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.ValidRanking(ranking)
    decreases linked.GetRank(ranking), 0
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0 <= i < numChildren => ILinkedBetreeNode(linked.ChildAtIdx(i), ranking))
  }

  function ILinkedBetreeNode(linked: LinkedBetree, ranking: Ranking) : (out: PivotBetree.BetreeNode)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures out.WF()
    decreases linked.GetRank(ranking), 1
  {
    if linked.root.None?
    then PivotBetree.Nil
    else
      var node := linked.Root();
      PivotBetree.BetreeNode(node.buffers, node.pivotTable, IChildren(linked, ranking))
  }

  function IPath(path: Path) : (out: PivotBetree.Path)
    requires path.linked.Acyclic()
    requires path.Valid()
  {
    PivotBetree.Path(ILinkedBetree(path.linked), path.key, path.depth)
  }
  
  predicate StepPathRootAcyclic(step: Step) {
    match step {
      case InternalSplitStep(path, _, _) => 
        path.linked.Acyclic()
      case InternalFlushStep(path, _, _, _, _) =>
        path.linked.Acyclic()
      case InternalCompactStep(path, _, _, _) =>
        path.linked.Acyclic()
      case _ => true
    }
  }

  function IStep(step: Step) : (out: PivotBetree.Step) 
    requires step.WF()
    requires StepPathRootAcyclic(step)
    ensures out.WF()
  {
     match step {
      case QueryStep(receipt) => 
        // todo: this is a placeholder
        // PivotBetree.QueryStep(IReceipt(receipt))
        PivotBetree.PutStep()
      case PutStep() => PivotBetree.PutStep()
      case QueryEndLsnStep() => PivotBetree.QueryEndLsnStep()
      case FreezeAsStep() => PivotBetree.FreezeAsStep()
      case InternalGrowStep(_) => PivotBetree.InternalGrowStep()
      case InternalSplitStep(path, childIdx, splitKey) => 
        // todo:
        var out := PivotBetree.InternalSplitStep(IPath(path), childIdx, splitKey);
        assume out.WF();
        out
      case InternalFlushStep(path, childIdx, _, _, _) =>
        var out := PivotBetree.InternalFlushStep(IPath(path), childIdx);
        IPathValid(path);
        TargetCommutesWithI(path);
        out
      case InternalCompactStep(path, compactedBuffers, _, _) =>
        var out := PivotBetree.InternalCompactStep(IPath(path), compactedBuffers);
        IPathValid(path);
        TargetCommutesWithI(path);
        out
    }
  }

  lemma TargetCommutesWithI(path: Path) 
    requires path.Valid()
    requires path.linked.Acyclic()
    ensures path.Target().Acyclic()  //prereq
    ensures IPath(path).Valid()  // prereq
    ensures IPath(path).Target() == ILinkedBetree(path.Target())
    decreases path.depth
  {
    ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
    IPathValid(path);
    if 0 < path.depth {
      TargetCommutesWithI(path.Subpath());
      SubpathCommutesWithIPath(path);
    }
  }

  lemma SubpathCommutesWithIPath(path: Path) 
    requires path.Valid()
    requires 0 < path.depth
    requires path.linked.Acyclic()
    ensures path.Subpath().linked.Acyclic()  // prereq
    ensures IPath(path.Subpath()) == IPath(path).Subpath()
  {
    ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
    ChildKeyCommutesWithI(path.linked, path.key);
  }
  
  lemma ChildKeyCommutesWithI(linked: LinkedBetree, key: Key)
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().KeyInDomain(key)
    ensures linked.ChildForKey(key).Acyclic()  // prereq
    ensures ILinkedBetree(linked.ChildForKey(key)) == ILinkedBetree(linked).Child(key)
  {
    ChildKeyAcyclic(linked, key);
    if linked.ChildForKey(key).HasRoot() {
      calc {
        PivotBetree.BetreeNode(
            linked.ChildForKey(key).Root().buffers, 
            linked.ChildForKey(key).Root().pivotTable, 
            IChildren(linked.ChildForKey(key), linked.ChildForKey(key).TheRanking()));
        {
          IChildrenIgnoresRanking(linked.ChildForKey(key), linked.ChildForKey(key).TheRanking(), linked.TheRanking());
        }
        PivotBetree.BetreeNode(
            linked.ChildForKey(key).Root().buffers, 
            linked.ChildForKey(key).Root().pivotTable, 
            IChildren(linked.ChildForKey(key), linked.TheRanking()));
        PivotBetree.BetreeNode(
            linked.Root().buffers, 
            linked.Root().pivotTable, 
            IChildren(linked, linked.TheRanking())).Child(key);
      }
    } else {
      calc {  // trigger
        PivotBetree.Nil;
        PivotBetree.BetreeNode(linked.Root().buffers, linked.Root().pivotTable, IChildren(linked, linked.TheRanking())).Child(key);
      }
    }
  }

  lemma IPathValid(path: Path) 
    requires path.Valid()
    requires path.linked.Acyclic()
    ensures IPath(path).Valid()
    decreases path.depth
  {
    if 0 < path.depth {
      ValidRankingAllTheWayDown(path.linked.TheRanking(), path);
      IPathValid(path.Subpath());
      SubpathCommutesWithIPath(path);
    }
  }

  lemma IChildrenIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    requires linked.HasRoot()
    ensures IChildren(linked, r1) == IChildren(linked, r2)
    decreases linked.GetRank(r1), 0
  {
    var numChildren := |linked.Root().children|;
    forall i | 0 <= i < numChildren 
    ensures ILinkedBetreeNode(linked.ChildAtIdx(i), r1) == ILinkedBetreeNode(linked.ChildAtIdx(i), r2){
      ILinkedBetreeIgnoresRanking(linked.ChildAtIdx(i), r1, r2);
    }
    assert IChildren(linked, r1) == IChildren(linked, r2);
  }

  lemma ILinkedBetreeIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    ensures ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2)
    decreases linked.GetRank(r1), 1
  {
    if linked.root.None? {
      assert ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2);
    } else {
      IChildrenIgnoresRanking(linked, r1, r2);
      assert IChildren(linked, r1) == IChildren(linked, r2);
      assert ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2);
    }
  }

  function IStampedBetree(stampedBetree: StampedBetree) : (out: PivotBetree.StampedBetree)
    requires stampedBetree.value.WF()
    requires stampedBetree.value.Acyclic()
    ensures out.value.WF()
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : (out: PivotBetree.Variables)
    requires v.WF()
    requires v.linked.Acyclic()
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && v.linked.Acyclic()  // contains v.linked.WF()
  }

  lemma SubstitutePreservesWF(replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs)
    requires replacement.WF()
    requires path.depth == |pathAddrs|
    requires path.Valid()
    requires SeqHasUniqueElems(pathAddrs)
    requires path.CanSubstitute(replacement, pathAddrs)
    ensures path.Substitute(replacement, pathAddrs).WF()
    decreases path.depth
  {
    var res := path.Substitute(replacement, pathAddrs);
    if 0 < path.depth {
      DiskViewDiff(replacement, path.Subpath(), pathAddrs[1..]);
      SubstitutePreservesWF(replacement, path.Subpath(), pathAddrs[1..]);
    }
  }

  predicate FreshRankingExtension(dv: DiskView, r1: Ranking, r2: Ranking) 
  {
    && IsSubMap(r1, r2)
    && forall k | k in r2 && k !in r1 :: k !in dv.entries
  }

  lemma DiskViewDiff(replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs)
    requires replacement.WF()
    requires path.depth == |pathAddrs|
    requires path.Valid()
    requires SeqHasUniqueElems(pathAddrs)
    requires path.linked.diskView.IsSubsetOf(replacement.diskView)
    ensures path.Substitute(replacement, pathAddrs).diskView.entries.Keys == replacement.diskView.entries.Keys + Set(pathAddrs)
    decreases path.depth
  {
    if 0 < path.depth {
      DiskViewDiff(replacement, path.Subpath(), pathAddrs[1..]);
    }
  }

  lemma RankingAfterSubstitution(replacement: LinkedBetree, ranking: Ranking, path: Path, pathAddrs: PathAddrs) 
  returns (newRanking: Ranking)
    requires path.CanSubstitute(replacement, pathAddrs)
    requires path.linked.ValidRanking(ranking)
    requires replacement.ValidRanking(ranking)
    requires SeqHasUniqueElems(pathAddrs)
    requires Set(pathAddrs) !! ranking.Keys
    requires path.linked.diskView.IsFresh(Set(pathAddrs))
    requires replacement.diskView.IsFresh(Set(pathAddrs))
    ensures path.Substitute(replacement, pathAddrs).WF()
    ensures path.Substitute(replacement, pathAddrs).ValidRanking(newRanking)
    ensures FreshRankingExtension(path.linked.diskView, ranking, newRanking)
    ensures newRanking.Keys == ranking.Keys + Sequences.Set(pathAddrs)
    decreases path.depth
  {
    SubstitutePreservesWF(replacement, path, pathAddrs);
    if path.depth == 0 {
      return ranking;
    } else {
      var subtree := path.Subpath().Substitute(replacement, pathAddrs[1..]); 
      var interRanking := RankingAfterSubstitution(replacement, ranking, path.Subpath(), pathAddrs[1..]); // intermediate
      var newNodeAddr := pathAddrs[0];
      var oldRootRank := interRanking[path.linked.root.value];
      var subtreeRank := if subtree.root.None? then 0 else interRanking[subtree.root.value];
      var newNodeRank := oldRootRank + subtreeRank + 1; // need to exceed oldRootRank and subtreeRank
      newRanking := interRanking[newNodeAddr := newNodeRank];

      var linked' := path.Substitute(replacement, pathAddrs);
      forall addr | 
        && addr in newRanking 
        && addr in linked'.diskView.entries 
      ensures linked'.diskView.NodeChildrenRespectsRank(newRanking, addr)
      {
        DiskViewDiff(replacement, path, pathAddrs);
        if addr == newNodeAddr {
          var node := linked'.diskView.entries[addr];
          forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some? 
          ensures node.children[childIdx].value in newRanking
          ensures newRanking[node.children[childIdx].value] < newRanking[addr]
          { 
            var newChildren := node.children[Route(node.pivotTable, path.key) := subtree.root];
            var subtreeSibling := newChildren[childIdx];  // trigger
          }
        }
      }
    }
  }

  lemma RankingAfterInsertCompactReplacement(target: LinkedBetree, compactedBuffers: BufferStack, ranking: Ranking, replacementAddr: Address) 
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires target.HasRoot()
    requires target.diskView.IsFresh({replacementAddr})
    requires target.Root().buffers.Equivalent(compactedBuffers)
    ensures InsertCompactReplacement(target, compactedBuffers, replacementAddr).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + {replacementAddr}
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    newRanking := ranking[replacementAddr := oldTargetRank];
    assert target.diskView.ValidRanking(newRanking);
  }

  lemma RankingAfterInsertFlushReplacement(target: LinkedBetree, ranking: Ranking, childIdx: nat, targetAddr: Address, targetChildAddr: Address) 
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires target.HasRoot()
    requires target.Root().OccupiedChildIndex(childIdx)
    requires target.diskView.IsFresh({targetAddr, targetChildAddr})
    requires targetAddr != targetChildAddr
    ensures InsertFlushReplacement(target, childIdx, targetAddr, targetChildAddr).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + {targetAddr, targetChildAddr}
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    var oldChildRank := ranking[target.Root().children[childIdx].value];
    newRanking := ranking[targetAddr := oldTargetRank][targetChildAddr := oldChildRank];
    assert target.diskView.ValidRanking(newRanking);
  }

  lemma ValidRankingAllTheWayDown(ranking: Ranking, path: Path)
    requires path.Valid()
    requires path.linked.ValidRanking(ranking)
    ensures 0 < path.depth ==> path.Subpath().linked.ValidRanking(ranking)
    ensures path.Target().ValidRanking(ranking)
    decreases path.depth
  {
    if 0 < path.depth {
      ValidRankingAllTheWayDown(ranking, path.Subpath());
    }
  } 

  predicate RankingIsTight(dv: DiskView, ranking: Ranking) {
    ranking.Keys <= dv.entries.Keys
  }

  // Create a valid ranking that is a subset of the diskview. Note that diskview is allowed to
  // have things that are not in the diskview
  lemma BuildTightRanking(linked: LinkedBetree, ranking: Ranking) returns (tightRanking : Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures RankingIsTight(linked.diskView, tightRanking)
    ensures linked.ValidRanking(tightRanking)
  {
    tightRanking := map addr | addr in linked.diskView.entries && addr in ranking :: ranking[addr];
  }

  lemma InsertGrowReplacementNewRanking(linked: LinkedBetree, oldRanking: Ranking, newRootAddr: Address) returns (newRanking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(oldRanking)
    requires RankingIsTight(linked.diskView, oldRanking)
    requires linked.diskView.IsFresh({newRootAddr})
    ensures InsertGrowReplacement(linked, newRootAddr).BuildTightTree().WF()
    ensures InsertGrowReplacement(linked, newRootAddr).BuildTightTree().ValidRanking(newRanking)
    ensures newRanking.Keys == oldRanking.Keys + {newRootAddr}
    ensures IsSubMap(oldRanking, newRanking);
  {
    if linked.HasRoot() {
      var oldRootRank := oldRanking[linked.root.value];
      newRanking := oldRanking[newRootAddr := oldRootRank+1];
    } else {
      var newRootRank := if |oldRanking.Values| == 0 then 1 else SetMax(oldRanking.Values) + 1;
      newRanking := oldRanking[newRootAddr := newRootRank];
    }
    var newRoot := InsertGrowReplacement(linked, newRootAddr);
    assert newRoot.ValidRanking(newRanking);  // trigger
    BuildTightMaintainsRanking(newRoot, newRanking);
    BuildTightPreservesWF(newRoot, newRanking);
    BuildTightIgnoresRanking(newRoot, newRanking, newRoot.TheRanking());   
  }

  lemma InvNextInternalGrowStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    var newRanking := InsertGrowReplacementNewRanking(v.linked, oldRanking, step.newRootAddr);  // witness
  }

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires v.linked.diskView.IsFresh(Set(step.pathAddrs))
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var replacement := InsertCompactReplacement(step.path.Target(), step.compactedBuffers, step.targetAddr);
    var rankingAfterReplacement := RankingAfterInsertCompactReplacement(step.path.Target(), step.compactedBuffers, oldRanking, step.targetAddr);
    var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
    var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
    BuildTightMaintainsRanking(linkedAfterSubstitution, newRanking);
    BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
    BuildTightIgnoresRanking(linkedAfterSubstitution, newRanking, linkedAfterSubstitution.TheRanking());
  }

  lemma InvNextInternalFlushStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalFlushStep?
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    ValidRankingAllTheWayDown(oldRanking, step.path);
    var replacement := InsertFlushReplacement(step.path.Target(), step.childIdx, step.targetAddr, step.targetChildAddr);
    var rankingAfterReplacement := RankingAfterInsertFlushReplacement(step.path.Target(), oldRanking, step.childIdx, step.targetAddr, step.targetChildAddr);
    var newRanking := RankingAfterSubstitution(replacement, rankingAfterReplacement, step.path, step.pathAddrs);
    var linkedAfterSubstitution := step.path.Substitute(replacement, step.pathAddrs);
    BuildTightMaintainsRanking(linkedAfterSubstitution, newRanking);
    BuildTightPreservesWF(linkedAfterSubstitution, newRanking);
    BuildTightIgnoresRanking(linkedAfterSubstitution, newRanking, linkedAfterSubstitution.TheRanking());
  }

  lemma BuildTightIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    ensures linked.BuildTightTreeUsingRanking(r1) == linked.BuildTightTreeUsingRanking(r2)
    decreases linked.GetRank(r1)
  {
    if linked.HasRoot() {
      forall i | 0 <= i < |linked.Root().children|
      ensures linked.ChildAtIdx(i).BuildTightTreeUsingRanking(r1) == linked.ChildAtIdx(i).BuildTightTreeUsingRanking(r2)
      {
        BuildTightIgnoresRanking(linked.ChildAtIdx(i), r1, r2);
      }
      var numChildren := |linked.Root().children|;
      var children1 := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).BuildTightTreeUsingRanking(r1).diskView);
      var children2 := seq(numChildren, i requires 0 <= i < numChildren => linked.ChildAtIdx(i).BuildTightTreeUsingRanking(r2).diskView);
      assert children1 == children2;  // trigger
    }
  }

  lemma BuildTightMaintainsRanking(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()
    ensures linked.BuildTightTreeUsingRanking(ranking).ValidRanking(ranking)
    decreases linked.GetRank(ranking)
  {
    // todo: Dafny always inconclusive on this one. Attempts to fix it has led to a massive
    // explosion that somehow caused everything else to fail, and after 2 hours I gave up
    // and reverted back to this state.
    assume false;

    BuildTightPreservesWF(linked, ranking);
    if linked.HasRoot() {
      forall i | 0 <= i < |linked.Root().children|
      ensures linked.ChildAtIdx(i).BuildTightTreeUsingRanking(ranking).ValidRanking(ranking)
      {
        BuildTightMaintainsRanking(linked.ChildAtIdx(i), ranking);
      }
      assert linked.BuildTightTreeUsingRanking(ranking).ValidRanking(ranking);
    } else {
      assert linked.BuildTightTreeUsingRanking(ranking).ValidRanking(ranking);
    }
  }

  // Children blocks are not lost from the disk after build tight
  lemma BuildTightPreservesChildren(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    ensures forall idx: nat | linked.Root().ValidChildIndex(idx) && linked.Root().children[idx].Some? :: 
       linked.Root().children[idx].value in linked.BuildTightTreeUsingRanking(ranking).diskView.entries
  {
    var linkedTight := linked.BuildTightTreeUsingRanking(ranking);
    var tightChildrenDvs := seq(|linked.Root().children|, i requires 0 <= i < |linked.Root().children| => linked.ChildAtIdx(i).BuildTightTreeUsingRanking(ranking).diskView);
    forall idx: nat | linked.Root().ValidChildIndex(idx) && linked.Root().children[idx].Some?
    ensures linked.Root().children[idx].value in linkedTight.diskView.entries
    {
      var childPtr := linked.Root().children[idx].value;
      assert childPtr in tightChildrenDvs[idx].entries;
    }
  }

  lemma ChildCommutesWithBuiltTightInInterpretation(linked: LinkedBetree, ranking: Ranking, idx: nat) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).WF();  // prereq
    ensures linked.ChildAtIdx(idx).ValidRanking(ranking);  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).HasRoot()  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).Root().ValidChildIndex(idx)  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx).WF()  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx).ValidRanking(ranking)  // prereq
    ensures linked.ChildAtIdx(idx).BuildTightTreeUsingRanking(ranking).WF()  // prereq
    ensures linked.ChildAtIdx(idx).BuildTightTreeUsingRanking(ranking).ValidRanking(ranking)  // prereq 
    ensures ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx), ranking)
      == ILinkedBetreeNode(linked.ChildAtIdx(idx).BuildTightTreeUsingRanking(ranking), ranking)
  {
    
    BuildTightPreservesWF(linked, ranking);
    // BuildTightPreservesValidChildIdx(linked, ranking, idx);
    assert linked.BuildTightTreeUsingRanking(ranking).Root().ValidChildIndex(idx);
    assert linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx).WF();

    assume false;

    // assert ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx), ranking)
      // == ILinkedBetreeNode(linked.ChildAtIdx(idx).BuildTightTreeUsingRanking(ranking), ranking);
  }

  lemma BuildTightPreservesInterpretationIChildren(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()  // prereq
    ensures IChildren(linked, ranking) == IChildren(linked.BuildTightTreeUsingRanking(ranking), ranking)
    decreases linked.GetRank(ranking), 0
  {
    BuildTightPreservesWF(linked, ranking);
    var numChildren := |linked.Root().children|;
    forall i | 0 <= i < numChildren 
    ensures ILinkedBetreeNode(linked.ChildAtIdx(i), ranking) == ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(i), ranking)
    {
      BuildTightPreservesInterpretation(linked.ChildAtIdx(i), ranking);
      ChildCommutesWithBuiltTightInInterpretation(linked, ranking, i);
    }
  }

  lemma BuildTightPreservesInterpretation(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()  // prereq
    ensures ILinkedBetreeNode(linked, ranking) == ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking), ranking)
    decreases linked.GetRank(ranking), 1
  {
    BuildTightPreservesWF(linked, ranking);
    if linked.HasRoot() {
      BuildTightPreservesInterpretationIChildren(linked, ranking);
    }
  }

  lemma BuildTightPreservesChildInterpretation(linked: LinkedBetree, idx: nat, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.BuildTightTree().WF()  // prereq
    ensures linked.BuildTightTree().Root().ValidChildIndex(idx)  // prereq
    ensures ILinkedBetreeNode(linked.ChildAtIdx(idx), ranking) == ILinkedBetreeNode(linked.BuildTightTree().ChildAtIdx(idx), ranking)
  {
    BuildTightPreservesChildInterpretationHelper(linked, idx, ranking);
    BuildTightIgnoresRanking(linked, ranking, linked.TheRanking());
  }

  lemma BuildTightPreservesChildInterpretationHelper(linked: LinkedBetree, idx: nat, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()  // prereq
    ensures linked.BuildTightTreeUsingRanking(ranking).Root().ValidChildIndex(idx)  // prereq
    ensures ILinkedBetreeNode(linked.ChildAtIdx(idx), ranking) == ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx), ranking)
  {
    BuildTightPreservesWF(linked, ranking);
    calc {
      ILinkedBetreeNode(linked.ChildAtIdx(idx), ranking);
        { ChildIdxCommutesWithI(linked, idx, ranking); }
      ILinkedBetreeNode(linked, ranking).children[idx];
        { BuildTightPreservesInterpretation(linked, ranking); }
      ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking), ranking).children[idx];
        { ChildIdxCommutesWithI(linked.BuildTightTreeUsingRanking(ranking), idx, ranking); }
      ILinkedBetreeNode(linked.BuildTightTreeUsingRanking(ranking).ChildAtIdx(idx), ranking);
    }
  }

  lemma BuildTightPreservesWF(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures linked.BuildTightTreeUsingRanking(ranking).WF()
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() {
      forall i | 0 <= i < |linked.Root().children|
      ensures linked.ChildAtIdx(i).BuildTightTreeUsingRanking(ranking).WF()
      {
        BuildTightPreservesWF(linked.ChildAtIdx(i), ranking);
      }
      BuildTightPreservesChildren(linked, ranking);
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
        InvNextInternalGrowStep(v, v', lbl, step);
        assert Inv(v');
      }
      case InternalSplitStep(_, _, _) => {
        assume false;
        assert Inv(v');   // bwoken
      }
      case InternalFlushStep(_, _, _, _, _) => {
        InvNextInternalFlushStep(v, v', lbl, step);
      }
      case InternalCompactStep(_, _, _, _) => {
        InvNextInternalCompactStep(v, v', lbl, step);
      }
    }
  }

  lemma FreshEntryToDiskDoesNotChangeInterpretation(linked: LinkedBetree, linked': LinkedBetree, ranking: Ranking, newAddr: Address, newVal: BetreeNode) 
    requires linked.WF() && linked'.WF()
    requires linked.ValidRanking(ranking)
    requires linked'.ValidRanking(ranking)
    requires linked.diskView.IsFresh({newAddr})
    requires linked'.diskView == linked.diskView.ModifyDisk(newAddr, newVal)
    ensures ILinkedBetreeNode(linked, ranking)
      == ILinkedBetreeNode(LinkedBetree(linked.root, linked'.diskView), ranking)
    decreases linked.GetRank(ranking)
  {
    if linked.root.Some? {
      var numChildren := |linked.Root().children|;
      forall i | 0 <= i < numChildren 
      ensures  ILinkedBetreeNode(linked.ChildAtIdx(i), ranking)
          == ILinkedBetreeNode(LinkedBetree(linked.ChildAtIdx(i).root, linked'.diskView), ranking)
      {
        FreshEntryToDiskDoesNotChangeInterpretation(linked.ChildAtIdx(i), linked', ranking, newAddr, newVal);
      }
    assert ILinkedBetreeNode(linked, ranking)
      == ILinkedBetreeNode(LinkedBetree(linked.root, linked'.diskView), ranking);  // trigger
    }
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures Inv(v)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    ILinkedWF(v.linked, v.linked.TheRanking());
  }


  lemma InternalGrowStepRefines(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires v.linked.Acyclic()
    requires NextStep(v, v', lbl, step)
    requires step.InternalGrowStep?
    ensures Inv(v')  // prereq
    ensures PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step))
  {
    InvNext(v, v', lbl);
    var tr := BuildTightRanking(v.linked, v.linked.TheRanking());
    var growReplacementRanking := InsertGrowReplacementNewRanking(v.linked, tr, step.newRootAddr);
    var r' := v'.linked.TheRanking();
    calc {
      ILinkedBetree(v'.linked).children[0];
      ILinkedBetreeNode(v'.linked, r').children[0];
      ILinkedBetreeNode(v'.linked.ChildAtIdx(0), r');
      {
        ILinkedBetreeIgnoresRanking(v'.linked.ChildAtIdx(0), growReplacementRanking, r');
      }
      ILinkedBetreeNode(
        InsertGrowReplacement(v.linked, step.newRootAddr).BuildTightTree().ChildAtIdx(0), 
        growReplacementRanking);
        {
          BuildTightPreservesChildInterpretation(InsertGrowReplacement(v.linked, step.newRootAddr), 0, growReplacementRanking);
        }
      ILinkedBetreeNode(InsertGrowReplacement(v.linked, step.newRootAddr).ChildAtIdx(0), growReplacementRanking);
        {
          FreshEntryToDiskDoesNotChangeInterpretation(
            v.linked, 
            InsertGrowReplacement(v.linked, step.newRootAddr), 
            growReplacementRanking,
            step.newRootAddr,
            BetreeNode(BufferStack([]), TotalPivotTable(), [v.linked.root])
          );
        }
      ILinkedBetreeNode(v.linked, growReplacementRanking);
      {
        ILinkedBetreeIgnoresRanking(v.linked, v.linked.TheRanking(), growReplacementRanking);
      }
      ILinkedBetree(v.linked);
    }
    assert I(v').root.children == [I(v).root]; 
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);
    var step: Step :| NextStep(v, v', lbl, step);
    match step {
      case QueryStep(receipt) => {
        // ValidReceiptRefines(step.receipt);
        assume false;  // todo
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); 
      }
      case PutStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case QueryEndLsnStep() => {
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case FreezeAsStep() => {
        assume false;  // todo
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step)); 
      }
      case InternalGrowStep(_) => {
        InternalGrowStepRefines(v, v', lbl, step);
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalSplitStep(_, _, _) => {
        assume false;  // todo
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalFlushStep(_, _, _, _, _) => {
        assume false;  // todo
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
      case InternalCompactStep(_, _, _, _) => {
        assume false;  // todo
        assert PivotBetree.NextStep(I(v), I(v'), ILbl(lbl), IStep(step));
      }
    }
  }
}
