// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetree.i.dfy"

module LinkedBetreeRefinement {
  import opened Options
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

  lemma InvNextInternalCompactStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires Inv(v)
    requires NextStep(v, v', lbl, step);
    requires step.InternalCompactStep?
    ensures Inv(v')
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
      case InternalGrowStep() => {
        assert Inv(v');   // bwoken
      }
      case InternalSplitStep(_, _, _) => {
        assert Inv(v');   // bwoken
      }
      case InternalFlushStep(_, _) => {
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
