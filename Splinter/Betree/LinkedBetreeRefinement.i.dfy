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

  function EmptyStampedBetree() : StampedBetree
  {
    Stamped(LinkedBetree(None, DiskView(map[])), 0)
  }

  function ILbl(lbl: TransitionLabel) : PivotBetree.TransitionLabel
  {
    match lbl
      case QueryLabel(endLsn, key, value) => PivotBetree.QueryLabel(endLsn, key, value)
      case PutLabel(puts) => PivotBetree.PutLabel(puts)
      case QueryEndLsnLabel(endLsn) => PivotBetree.QueryEndLsnLabel(endLsn)
      case FreezeAsLabel(stampedBetree) => PivotBetree.FreezeAsLabel(
        if stampedBetree.value.WF()
        then IStampedBetree(stampedBetree)
        else IStampedBetree(EmptyStampedBetree())
      )
      case InternalLabel() => PivotBetree.InternalLabel()
  }

  function IChildren(linked: LinkedBetree) : seq<PivotBetree.BetreeNode>
    requires linked.WF()
    requires linked.HasRoot()
  {
    var numChildren := |linked.Root().children|;
    seq(numChildren, i requires 0<=i<numChildren => ILinkedBetree(linked.ChildAtIdx(i)))
  }

  function ILinkedBetree(linked: LinkedBetree) : PivotBetree.BetreeNode
    requires linked.WF()
  {
    if linked.root.None?
    then PivotBetree.Nil
    else
      var node := linked.Root();
      PivotBetree.BetreeNode(node.buffers, node.pivotTable, IChildren(linked))
  }

  function IStampedBetree(stampedBetree: StampedBetree) : PivotBetree.StampedBetree
    requires stampedBetree.value.WF()
  {
    Stamped(ILinkedBetree(stampedBetree.value), stampedBetree.seqEnd)
  }

  function I(v: Variables) : PivotBetree.Variables
    requires v.WF()
  {
    PivotBetree.Variables(v.memtable, ILinkedBetree(v.linked))
  }

  predicate Inv(v: Variables)
  {
    true  // TODO!
  }

  lemma InitRefines(v: Variables, stampedBetree: StampedBetree)
    requires Init(v, stampedBetree)
    ensures PivotBetree.Init(I(v), IStampedBetree(stampedBetree))
  {
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures v'.WF()
    ensures PivotBetree.Next(I(v), I(v'), ILbl(lbl))
  {
  }
}
