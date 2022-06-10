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

  function EmptyStampedBetree() : (out: StampedBetree)
    ensures Acyclic(out.value.diskView)
  {
    var out := Stamped(LinkedBetree(None, DiskView(map[])), 0);
    assert Acyclic(out.value.diskView) by {
      assert PointersRespectRank(out.value.diskView, map[]);
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
        if stampedBetree.value.WF() && Acyclic(stampedBetree.value.diskView)
        then IStampedBetree(stampedBetree)
        else IStampedBetree(EmptyStampedBetree())  // "silly" case, since we never interpret non-(WF+Acyclic) things
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  predicate PointersRespectRank(diskView: DiskView, ranking: GenericDisk.Ranking)
    requires diskView.WF()
  {
    && diskView.entries.Keys <= ranking.Keys
    && (forall address | address in diskView.entries
        :: var node := diskView.entries[address];
          forall childIdx:nat | node.ValidChildIndex(childIdx) && node.children[childIdx].Some?
            :: ranking[node.children[childIdx].value] < ranking[address]
        )
  }

  predicate Acyclic(diskView: DiskView)
  {
    && diskView.WF()
    && (exists ranking :: PointersRespectRank(diskView, ranking))
  }

  function TheRanking(diskView: DiskView) : GenericDisk.Ranking
    requires diskView.WF()
    requires Acyclic(diskView)
  {
    // Make CHOOSE deterministic as Leslie and Hilbert intended
    var ranking :| PointersRespectRank(diskView, ranking); ranking
  }

  function TheRankOf(linked: LinkedBetree) : int
    requires linked.WF()
  {
    if linked.HasRoot() && Acyclic(linked.diskView) then TheRanking(linked.diskView)[linked.root.value] else -1
    // Rustan: I can't believe this works! How are you figuring out that we can pass 0 into
    // negatives, but we stop there!?
  }

  function IChildren(linked: LinkedBetree) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
    requires Acyclic(linked.diskView)
    decreases TheRankOf(linked), 0
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0<=i<numChildren => ILinkedBetree(linked.ChildAtIdx(i)))
  }

  function ILinkedBetree(linked: LinkedBetree) : PivotBetree.BetreeNode
    requires linked.WF()
    requires Acyclic(linked.diskView)
    decreases TheRankOf(linked), 1
  {
    if linked.root.None?
    then PivotBetree.Nil
    else
      var node := linked.Root();
      PivotBetree.BetreeNode(node.buffers, node.pivotTable, IChildren(linked))
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PivotBetree.StampedBetree
    requires stampedBetree.value.WF()
    requires Acyclic(stampedBetree.value.diskView)
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : PivotBetree.Variables
    requires v.WF()
    requires Acyclic(v.linked.diskView)
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate Inv(v: Variables)
  {
    && Acyclic(v.linked.diskView)
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures Inv(v)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
    assume false;
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
