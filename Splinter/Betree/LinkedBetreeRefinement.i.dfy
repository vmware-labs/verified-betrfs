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
    ensures out.value.diskView.Acyclic()
  {
    var out := Stamped(LinkedBetree(None, DiskView(map[])), 0);
    assert out.value.diskView.Acyclic() by {
      assert out.value.diskView.PointersRespectRank(map[]);
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
        if stampedBetree.value.WF() && stampedBetree.value.diskView.Acyclic()
        then IStampedBetree(stampedBetree)
        else IStampedBetree(EmptyStampedBetree())  // "silly" case, since we never interpret non-(WF+Acyclic) things
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  function TheRankOf(linked: LinkedBetree) : nat 
    requires linked.HasRoot()
    requires linked.diskView.Acyclic()
  {
    linked.diskView.TheRanking()[linked.root.value]
  }

  function IChildren(linked: LinkedBetree, ranking: Ranking) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
    requires linked.diskView.PointersRespectRank(ranking)
    decreases linked.GetRank(ranking), 0
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0<=i<numChildren => ILinkedBetreeNode(linked.ChildAtIdx(i), ranking))
  }

  function ILinkedBetreeNode(linked: LinkedBetree, ranking: Ranking) : PivotBetree.BetreeNode
    requires linked.WF()
    requires linked.diskView.PointersRespectRank(ranking)
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
    requires linked.diskView.PointersRespectRank(r1)
    requires linked.diskView.PointersRespectRank(r2)
    ensures ILinkedBetreeNode(linked, r1) == ILinkedBetreeNode(linked, r2)
  {
    assume false;
  }

  // wrapper
  function ILinkedBetree(linked: LinkedBetree) : PivotBetree.BetreeNode
    requires linked.WF()
    requires linked.diskView.Acyclic()
  {
    ILinkedBetreeNode(linked, linked.diskView.TheRanking())
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PivotBetree.StampedBetree
    requires stampedBetree.value.WF()
    requires stampedBetree.value.diskView.Acyclic()
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : PivotBetree.Variables
    requires v.WF()
    requires v.linked.diskView.Acyclic()
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate Inv(v: Variables)
  {
    && v.linked.diskView.Acyclic()
  }

  // 
  lemma AcyclicImpliesReachableRespect(linked: LinkedBetree)
    requires linked.WF()
    requires linked.diskView.Acyclic()
    ensures linked.ReachableAddressesRespectRanking(linked.diskView.TheRanking())
    decreases linked.GetRank(linked.diskView.TheRanking())
  {
    if linked.HasRoot() {
      forall childIdx | linked.Root().ValidChildIndex(childIdx) ensures
          linked.ChildAtIdx(childIdx).ReachableAddressesRespectRanking(linked.diskView.TheRanking()) {
        AcyclicImpliesReachableRespect(linked.ChildAtIdx(childIdx));
      }
    }
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
    // requires l1.RankingIsClosed(r1) && l2.RankingIsClosed(r2)
    requires l1.ReachableAddressesRespectRanking(r1)
    requires l2.ReachableAddressesRespectRanking(r2)
    ensures l1.ReachableAddressesRespectRanking(MergeRanking(r1, r2))
    // ensures l2.ReachableAddressesRespectRanking(MergeRanking(r1, r2))
  {
    if !l1.HasRoot() {
      return;
    }
    var merged := MergeRanking(r1, r2);
    var node := l1.Root();
    forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some? 
    ensures && node.children[childIdx].value in merged.Keys
            && merged[node.children[childIdx].value] < merged[l1.root.value]
    {
      var parent := l1.root.value;
      var child := node.children[childIdx].value;
      if merged[parent] == r1[parent] {
        if merged[child] == r1[child] {
          // easy
          assert merged[node.children[childIdx].value] < merged[l1.root.value];
        } else {
          // hard: parent in r1 but child in r2
          assert merged[child] == r2[child];
          assert merged[node.children[childIdx].value] < merged[l1.root.value];
        }
      } else {
        assert parent in r2;
        assert child in r2;  // parent in here means child must be here
        assert merged[parent] == r2[parent];
        if merged[child] == r2[child] {
          assert parent in l2.diskView.entries;
          assert child in l2.diskView.entries;
          assert l2.diskView.NodePointersRespectsRank(r2, parent);



          assert r2[child] < r2[parent];
          assert merged[child] < merged[parent];
        } else {
          // hard: parent in r2, child in r1;
          assert merged[node.children[childIdx].value] < merged[l1.root.value];
        }
      }

      assert node.children[childIdx].value in merged.Keys;
      assert merged[node.children[childIdx].value] < merged[l1.root.value];
    }


    assume false;
    assert forall childIdx | l1.Root().ValidChildIndex(childIdx) ::
        l1.ChildAtIdx(childIdx).ReachableAddressesRespectRanking(merged);

  }

  lemma ReachableAddressesInRanking(linked: LinkedBetree, ranking: Ranking)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    ensures ReachableAddresses(linked, ranking) <= ranking.Keys
  { // todo
  }

  lemma ReachableMonotonicInChildRelation(linked: LinkedBetree, ranking: Ranking, childIdx: nat)
    requires linked.WF()
    requires linked.ValidRanking(ranking)
    requires linked.HasRoot()
    requires linked.Root().OccupiedChildIndex(childIdx)
    ensures ReachableAddresses(linked.ChildAtIdx(childIdx), ranking) <= ReachableAddresses(linked, ranking)
    decreases linked.GetRank(ranking)
  { // todo
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
  }

  lemma FoldRankingsValid(diskView: DiskView, rankings: seq<Ranking>)
    requires diskView.WF()
    requires forall i | 0<=i<|rankings| :: diskView.ValidRanking(rankings[i])
    ensures diskView.ValidRanking(FoldMaps(rankings))
  { //todo
  }

  lemma ConstructSubstitutionRanking(linked: LinkedBetree, linked': LinkedBetree, ranking: Ranking, targetRanking': Ranking, path: Path, pathAddrs: PathAddrs)
    returns (out: Ranking)
    requires path.depth == |pathAddrs|
    requires path.IsSubstitution(linked, linked', pathAddrs)
    requires linked.ReachableAddressesRespectRanking(ranking)
    requires path.Target(linked').ReachableAddressesRespectRanking(targetRanking')
    ensures linked'.ReachableAddressesRespectRanking(out)
    decreases path.depth
  {
    // AcyclicImpliesReachableRespect(linked);
//    assert linked.ReachableAddressesRespectRanking(linked.diskView.TheRanking());
    if path.depth == 0 {
      out := targetRanking';
      assert linked'.ReachableAddressesRespectRanking(out);
    } else {
      assert linked.HasRoot();
      var subranking
        := ConstructSubstitutionRanking(linked.Child(path.key), linked'.Child(path.key), ranking, targetRanking', path.Subpath(), pathAddrs[1..]);
      var length := |linked.Root().children|;
      var replacedIdx := Route(linked.Root().pivotTable, path.key);
      var childRankings := seq(length, (i:nat) requires i < length => 
        if i == replacedIdx then
          subranking
        else 
          //ReachableAddressesIsSubsetOfRanking(linked.ChildAtIdx(i), ranking);
          GetSubranking(ranking, ReachableAddresses(linked.ChildAtIdx(i), ranking)));
      var descendantRanking := FoldMaps(childRankings);
      var rootRank: nat := if |descendantRanking| == 0 then 1 else max(SetMax(descendantRanking.Values), 0) + 1;
      out := descendantRanking[linked'.root.value := rootRank];
      var node := linked'.Root();
      forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some? 
      ensures && node.children[childIdx].value in out.Keys
              && out[node.children[childIdx].value] < out[linked'.root.value]
      {
        
        assert node.children[childIdx].value in childRankings[childIdx];  // trigger
        FoldMapsSubset(childRankings);
        assert out[node.children[childIdx].value] in descendantRanking.Values;  // trigger
      }
      assert linked'.diskView.NodePointersRespectsRank(out, linked'.root.value);


      forall childIdx | linked'.Root().ValidChildIndex(childIdx) 
      ensures linked'.ChildAtIdx(childIdx).ReachableAddressesRespectRanking(out)
      {

      }
    


      assert linked'.ReachableAddressesRespectRanking(out);
    }
  }

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step);
    requires step.InternalCompactStep?
    ensures Inv(v')
  {
    var oldRanking := v.linked.diskView.TheRanking();
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

  lemma ILinkedWF(linked: LinkedBetree, ranking: Ranking) 
    requires linked.WF()
    requires linked.diskView.PointersRespectRank(ranking)
    ensures ILinkedBetree(linked).WF()
    decreases linked.GetRank(ranking)
  {
    if linked.HasRoot() {
      forall idx | linked.Root().ValidChildIndex(idx) 
      ensures ILinkedBetree(linked.ChildAtIdx(idx)).WF() {
        ILinkedWF(linked.ChildAtIdx(idx), ranking);
      }
    }
    ILinkedBetreeIgnoresRanking(linked, ranking, linked.diskView.TheRanking());
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures Inv(v)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    ILinkedWF(v.linked, v.linked.diskView.TheRanking());
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
