// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"
include "../../lib/Base/SequencesOfMaps.i.dfy"
include "../../lib/Base/Sets.i.dfy"

module LinkedBetreeRefinement {
  import opened Options
  import opened Mathematics
  import opened Sequences  // Set
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


  function GetSubranking(ranking: Ranking, subset:set<Address>) : Ranking
    requires subset <= ranking.Keys
  {
    map addr | addr in subset :: ranking[addr]
  }


  function ReachableAddresses(linked: LinkedBetree, ranking: Ranking) : (out: set<Address>)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
//    requires linked.ReachableAddressesRespectRanking(ranking) //kill
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() then 
        var s := seq(|linked.Root().children|, (i:nat) requires i<|linked.Root().children| => ReachableAddresses(linked.ChildAtIdx(i), ranking));
      {linked.root.value} + FoldSets(s)
    else {}
  }

//  lemma ReachableAddressesIsSubsetOfRanking(linked: LinkedBetree, ranking: Ranking) 
//    requires linked.WF()
//    requires linked.ReachableAddressesRespectRanking(ranking)
//    ensures ReachableAddresses(linked, ranking) <= ranking.Keys
//    decreases linked.GetRank(ranking)
//  {
//    var res :=  ReachableAddresses(linked, ranking);
//    if linked.HasRoot() {
//      forall e | e in res 
//      ensures e in ranking.Keys 
//      {
//        if e != linked.root.value {
//          var s := seq(|linked.Root().children|, (i:nat) requires i<|linked.Root().children| => ReachableAddresses(linked.ChildAtIdx(i), ranking));
//          assert e in FoldSets(s);
//          var idx := WhichFold(s, e);
//          assert e in s[idx];
//          ReachableAddressesIsSubsetOfRanking(linked.ChildAtIdx(idx), ranking);
//        }
//      }
//    }
//  }

  // Merge by taking the smaller ranking where possible
  function MergeRanking(r1: Ranking, r2: Ranking) : (out: Ranking) {
    map addr | addr in r1.Keys + r2.Keys :: 
      var out:nat := 
      if addr in r1 then
        if addr in r2 then 
          min(r1[addr], r2[addr])
        else
          r1[addr]
      else
        r2[addr]
      ; out
  }

  lemma MergeRankingSatisfiesBoth(l1: LinkedBetree, l2: LinkedBetree, r1: Ranking, r2: Ranking) 
    requires l1.WF() && l2.WF()
    requires l1.diskView == l2.diskView
    requires l1.ValidRanking(r1) && l2.ValidRanking(r2)
    ensures l1.ValidRanking(MergeRanking(r1, r2))
    ensures l2.ValidRanking(MergeRanking(r1, r2))
  {}

  lemma ReachableAddressesInRanking(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures ReachableAddresses(linked, ranking) <= ranking.Keys
  { // todo
    assume false;
  }

  lemma ReachableMonotonicInChildRelation(linked: LinkedBetree, ranking: Ranking, childIdx: nat)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().OccupiedChildIndex(childIdx)
    ensures ReachableAddresses(linked.ChildAtIdx(childIdx), ranking) <= ReachableAddresses(linked, ranking)
    decreases linked.GetRank(ranking)
  { // todo
    assume false;
  }

  function ChildRankings(linked: LinkedBetree, ranking: Ranking) : (out: seq<Ranking>)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
  {
    if !linked.HasRoot() then [] else
      var length := |linked.Root().children|;
      seq(length, (i:nat) requires i < length =>
        if !linked.Root().OccupiedChildIndex(i) then map[]
        else
          ReachableMonotonicInChildRelation(linked, ranking, i);
          ReachableAddressesInRanking(linked, ranking);
          //ReachableAddressesIsSubsetOfRanking(linked.ChildAtIdx(i), ranking);
          GetSubranking(ranking, ReachableAddresses(linked.ChildAtIdx(i), ranking)))
  }

  lemma ChildRankingsValid(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures forall i | 0<=i<|ChildRankings(linked, ranking)|
      :: linked.diskView.ValidRanking(ChildRankings(linked, ranking)[i])
  { //todo
    assume false;
  }

  lemma FoldRankingsValid(diskView: DiskView, rankings: seq<Ranking>)
    requires diskView.WF()
    requires forall i | 0<=i<|rankings| :: diskView.ValidRanking(rankings[i])
    ensures diskView.ValidRanking(FoldMaps(rankings))
  { //todo
    assume false;
  }

  lemma DescendentInDiskview(linked: LinkedBetree)

  // lemma ConstructSubstitutionRanking(linked: LinkedBetree, linked': LinkedBetree, ranking: Ranking, targetRanking': Ranking, path: Path, pathAddrs: PathAddrs)
  //   returns (newRanking: Ranking)
  //   requires linked.WF() && linked'.WF()
  //   requires path.depth == |pathAddrs|
  //   requires path.IsSubstitution(linked, linked', pathAddrs)  // tony: this seems to allow linked' to have an empty diskview
  //   requires linked.ValidRanking(ranking)
  //   requires path.Target(linked').ValidRanking(targetRanking')  // tony: this then says that the target subtree must in linked'.diskview
  //   ensures linked'.ValidRanking(newRanking)                    // Hence can't prove this because we may have lost all the diskvew entries not in the target subtree
  //   decreases path.depth
  // {
  //   if path.depth == 0 {
  //     newRanking := targetRanking';
  //     assert linked'.ValidRanking(newRanking);
  //   } else {
  //     assert linked.HasRoot();
  //     var subranking
  //       := ConstructSubstitutionRanking(linked.Child(path.key), linked'.Child(path.key), ranking, targetRanking', path.Subpath(), pathAddrs[1..]);
  //     var replacedIdx := Route(linked.Root().pivotTable, path.key);
  //     var childRankings := ChildRankings(linked, ranking)[replacedIdx := subranking];
  //     var descendantRanking := FoldMaps(childRankings);
  //     // FoldRankingsValid(linked.diskView, childRankings);
  //     var rootRank: nat := if |descendantRanking| == 0 then 1 else max(SetMax(descendantRanking.Values), 0) + 1;
  //     newRanking := descendantRanking[linked'.root.value := rootRank];
  //     forall addr | addr in newRanking 
  //     ensures
  //       && addr in linked'.diskView.entries
  //       && linked'.diskView.ValidRankingAtAddr(newRanking, addr)
  //     {
  //       if addr == linked'.root.value {
  //         assert addr in linked'.diskView.entries;
  //       } else {
  //         assume exists i :: 0 <= i < |childRankings| && addr in childRankings[i];  // todo: property of fold
  //         var i :| 0 <= i < |childRankings| && addr in childRankings[i];
  //         if i == replacedIdx {
  //           assert addr in linked'.diskView.entries;
  //         } else {
  //           assert addr in childRankings[i];
  //           ReachableMonotonicInChildRelation(linked, ranking, i);
  //           ReachableAddressesInRanking(linked, ranking);
  //           assert addr in GetSubranking(ranking, ReachableAddresses(linked.ChildAtIdx(i), ranking));
  //           assert addr in ReachableAddresses(linked.ChildAtIdx(i), ranking);
  //           assert linked.Root().children[i] == linked'.Root().children[i];
  //           // assert addr in ReachableAddresses(linked'.ChildAtIdx(i), newRanking);
  //           // TONY: What are the constraints on linked'.diskView? Seems like we don't have any?
  //           // Extreme case: we can have a target with empty diskview and empty targetRanking'?
  //           assert addr in linked.diskView.entries;
  //           assert linked.Root().children[i].value in linked'.diskView.entries;

  //           // argument is that addr's parent (linked.Root().children[i]) is in linked'.diskView.entries. 
  //           // And then the parent is in linked'.diskview.entries. And then because
  //           // linked' is WF, 

  //           assert addr in linked'.diskView.entries;
  //         }
  //       }


  //       assert addr in linked'.diskView.entries;
  //       assume linked'.diskView.ValidRankingAtAddr(newRanking, addr);
  //     }

    


  //     assert linked'.ValidRanking(newRanking);
  //   }
  // }

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step);
    requires step.InternalCompactStep?
    ensures v'.linked.Acyclic();
  {
    // todo
    assume false;
    var oldRanking := v.linked.TheRanking();
    var oldTargetAddr := step.path.Target(v.linked).root.value;
//    assert oldTargetAddr in v.linked.diskView.entries;
    var oldTargetRanking := oldRanking[oldTargetAddr];
    var targetRanking := oldRanking[step.targetAddr := oldTargetRanking];
    // var rootRanking := ConstructSubstitutionRanking(v.linked, v'.linked, step.path, step.pathAddrs);
    // assert v'.linked.diskView.PointersRespectRank(rootRanking);  // witness to acyclicity
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
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.Root().ValidChildIndex(idx)
    ensures ILinkedBetree(linked.ChildAtIdx(idx)) == ILinkedBetree(linked).children[idx]
  {

  }

  lemma ILinkedWF(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures ILinkedBetree(linked).WF()
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() {
      forall idx: nat | linked.Root().ValidChildIndex(idx) 
      ensures ILinkedBetree(linked).children[idx].WF()
      {
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
