// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Base/SequencesOfMaps.i.dfy"
include "../../lib/Base/Sets.i.dfy"
// include "../../lib/Base/Maps.i.dfy"

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

  type Ranking = GenericDisk.Ranking

  function EmptyStampedBetree() : (out: StampedBetree)
    ensures out.value.Acyclic()
  {
    var out := Stamped(LinkedBetree(None, DiskView(map[])), 0);
    assert out.value.Acyclic() by {
      assert out.value.ValidRanking(map[]);
    }
    out
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
        else IStampedBetree(EmptyStampedBetree())  // "silly" case, since we never interpret non-(WF+Acyclic) things
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  // function TheRankOf(linked: LinkedBetree) : nat 
  //   requires linked.HasRoot()
  //   requires linked.Acyclic()
  // {
  //   linked.diskView.TheRanking()[linked.root.value]
  // }

  function IChildren(linked: LinkedBetree, ranking: Ranking) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.ValidRanking(ranking)
    decreases linked.GetRank(ranking), 0
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0<=i<numChildren => ILinkedBetreeNode(linked.ChildAtIdx(i), ranking))
  }

  function ILinkedBetreeNode(linked: LinkedBetree, ranking: Ranking) : PivotBetree.BetreeNode
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    decreases linked.GetRank(ranking), 1
  {
    if linked.root.None?
    then PivotBetree.Nil
    else
      var node := linked.Root();
      PivotBetree.BetreeNode(node.buffers, node.pivotTable, IChildren(linked, ranking))
  }

  lemma ILinkedBetreeIgnoresRanking(linked: LinkedBetree, r1: Ranking, r2: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(r1)
    requires linked.ValidRanking(r2)
    ensures ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2)
  {
    assume false;
  }

  // wrapper
  function ILinkedBetree(linked: LinkedBetree) : PivotBetree.BetreeNode
    requires linked.WF()
    requires linked.Acyclic()
  {
    ILinkedBetreeNode(linked, linked.TheRanking())
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PivotBetree.StampedBetree
    requires stampedBetree.value.WF()
    requires stampedBetree.value.Acyclic()
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : PivotBetree.Variables
    requires v.WF()
    requires v.linked.Acyclic()
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate Inv(v: Variables)
  {
    && v.linked.Acyclic()  // contains v.linked.WF()
  }


  // function GetSubranking(ranking: Ranking, subset:set<Address>) : Ranking
  //   requires subset <= ranking.Keys
  // {
  //   map addr | addr in subset :: ranking[addr]
  // }


//   function ReachableAddresses(linked: LinkedBetree, ranking: Ranking) : (out: set<Address>)
//     requires linked.WF()
//     requires linked.ValidRanking(ranking)
// //    requires linked.ReachableAddressesRespectRanking(ranking) //kill
//     decreases linked.GetRank(ranking)
//   {
//     if linked.HasRoot() then 
//         var s := seq(|linked.Root().children|, (i:nat) requires i<|linked.Root().children| => ReachableAddresses(linked.ChildAtIdx(i), ranking));
//       {linked.root.value} + FoldSets(s)
//     else {}
//   }

  lemma SubstitutePreservesWF(linked: LinkedBetree, replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs)
    requires linked.Acyclic()
    requires replacement.Acyclic()
    requires path.depth == |pathAddrs|
    requires path.Valid(linked)
    requires path.CanSubstitute(linked, replacement, pathAddrs)
    ensures path.Substitute(linked, replacement, pathAddrs).WF()
  {
    assume false;
  }

  predicate FreshRankingExtension(dv: DiskView, r1: Ranking, r2: Ranking) 
  {
    && IsSubMap(r1, r2)
    && forall k | k in r2 && k !in r1 :: k !in dv.entries
  }

  lemma DiskViewDiff(linked: LinkedBetree, replacement: LinkedBetree, path: Path, pathAddrs: PathAddrs)
    requires linked.WF() && replacement.WF()
    requires path.depth == |pathAddrs|
    requires path.Valid(linked)
    requires SeqHasUniqueElems(pathAddrs)
    requires linked.diskView.IsSubsetOf(replacement.diskView)
    ensures path.Substitute(linked, replacement, pathAddrs).diskView.entries.Keys == replacement.diskView.entries.Keys + Set(pathAddrs)
    decreases path.depth
  {
    if 0 < path.depth {
      DiskViewDiff(linked.ChildForKey(path.key), replacement, path.Subpath(), pathAddrs[1..]);
    }
  }

  lemma RankingAfterSubstitution(linked: LinkedBetree, replacement: LinkedBetree, ranking: Ranking, path: Path, pathAddrs: PathAddrs) 
  returns (newRanking: Ranking)
    requires path.CanSubstitute(linked, replacement, pathAddrs)
    requires linked.ValidRanking(ranking)
    requires replacement.ValidRanking(ranking)
    requires SeqHasUniqueElems(pathAddrs)
    requires Set(pathAddrs) !! ranking.Keys
    requires Set(pathAddrs) !! linked.diskView.entries.Keys
    requires Set(pathAddrs) !! replacement.diskView.entries.Keys
    ensures path.Substitute(linked, replacement, pathAddrs).WF()
    ensures path.Substitute(linked, replacement, pathAddrs).ValidRanking(newRanking)
    ensures FreshRankingExtension(linked.diskView, ranking, newRanking)
    ensures newRanking.Keys == ranking.Keys + Sequences.Set(pathAddrs)
    decreases path.depth
  {
    SubstitutePreservesWF(linked, replacement, path, pathAddrs);
    if path.depth == 0 {
      return ranking;
    } else {
      var subtree := path.Subpath().Substitute(linked.ChildForKey(path.key), replacement, pathAddrs[1..]); 
      var interRanking := RankingAfterSubstitution(linked.ChildForKey(path.key), replacement, ranking, path.Subpath(), pathAddrs[1..]); // intermediate
      var newNodeAddr := pathAddrs[0];
      var oldRootRank := interRanking[linked.root.value];
      var subtreeRank := if subtree.root.None? then 0 else interRanking[subtree.root.value];
      var newNodeRank := oldRootRank + subtreeRank + 1; // need to exceed oldRootRank and subtreeRank
      newRanking := interRanking[newNodeAddr := newNodeRank];

      var linked' := path.Substitute(linked, replacement, pathAddrs);
      forall addr | 
        && addr in newRanking 
        && addr in linked'.diskView.entries 
      ensures linked'.diskView.NodeChildrenRespectsRank(newRanking, addr)
      {
        DiskViewDiff(linked, replacement, path, pathAddrs);
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

  lemma RankingAfterReplacement(target: LinkedBetree, replacement: BetreeNode, ranking: Ranking, replacementAddr: Address) 
  returns (newRanking: Ranking)
    requires target.WF()
    requires target.ValidRanking(ranking)
    requires replacement.WF()
    requires target.HasRoot()
    requires IsCompaction(target.Root(), replacement)
    requires target.diskView.IsFresh(replacementAddr)
    ensures InsertCompactReplacement(target, replacement, replacementAddr).ValidRanking(newRanking)
    ensures newRanking.Keys == ranking.Keys + {replacementAddr}
    ensures target.ValidRanking(newRanking)   // newRanking is good for both the old and the new root
  {
    var oldTargetRank := ranking[target.root.value];
    newRanking := ranking[replacementAddr := oldTargetRank];
    assert target.diskView.ValidRanking(newRanking);
  }

  lemma ValidRankingAllTheWayDown(linked: LinkedBetree, ranking: Ranking, path: Path)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires path.Valid(linked)
    ensures path.Target(linked).ValidRanking(ranking)
    decreases path.depth
  {
    if 0 < path.depth {
      ValidRankingAllTheWayDown(linked.ChildForKey(path.key), ranking, path.Subpath());
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

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step)
    requires step.InternalCompactStep?
    requires Set(step.pathAddrs) !! v.linked.diskView.entries.Keys
    ensures v'.linked.Acyclic()
  {
    var oldRanking := BuildTightRanking(v.linked, v.linked.TheRanking());
    ValidRankingAllTheWayDown(v.linked, oldRanking, step.path);
    var replacement := InsertCompactReplacement(step.path.Target(v.linked), step.compactedNode, step.targetAddr);
    var rankingAfterReplacement := RankingAfterReplacement(step.path.Target(v.linked), step.compactedNode, oldRanking, step.targetAddr);
    var newRanking := RankingAfterSubstitution(v.linked, replacement, rankingAfterReplacement, step.path, step.pathAddrs);
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
      case InternalGrowStep() => {
        assume false;
        assert Inv(v');   // bwoken
      }
      case InternalSplitStep(_, _, _) => {
        assume false;
        assert Inv(v');   // bwoken
      }
      case InternalFlushStep(_, _) => {
        assume false;
        assert Inv(v');   // bwoken
      }
      case InternalCompactStep(_, _, _, _) => {
        InvNextInternalCompactStep(v, v', lbl, step);
        assert Inv(v');  
      }
    }
  }

  lemma ChildCommutes(linked: LinkedBetree, idx: nat) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    requires ILinkedBetree(linked).ValidChildIndex(idx)
    ensures |ILinkedBetree(linked).children| == NumBuckets(ILinkedBetree(linked).pivotTable)
    ensures linked.ChildAtIdx(idx).Acyclic()
    ensures ILinkedBetree(linked.ChildAtIdx(idx)) == ILinkedBetree(linked).children[idx]
  {
    // todo
    assume false;
  }

  lemma ChildAcyclic(linked: LinkedBetree, idx: nat) 
    requires linked.Acyclic()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures linked.ChildAtIdx(idx).Acyclic();
  {
    assume false;
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
        ChildAcyclic(linked, idx);
        ILinkedWF(linked.ChildAtIdx(idx), ranking);
        ChildCommutes(linked, idx);
      }
      ILinkedBetreeIgnoresRanking(linked, ranking, linked.TheRanking());
    }
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures Inv(v)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    ILinkedWF(v.linked, v.linked.TheRanking());
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures Inv(v')
    ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  {
    assume false;
  }
}
