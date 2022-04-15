// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"

module PagedBetreeRefinement
{
  import opened Options
  import opened KeyType
  import opened StampedMapMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened PagedBetree

  function INodeAt(betreeNode: BetreeNode, key: Key) : Message
    requires betreeNode.WF()
  {
    BuildQueryReceipt(betreeNode, key).Result()
  }
  
  function INode(betreeNode: BetreeNode) : TotalKMMapMod.TotalKMMap
    requires betreeNode.WF()
  {
    imap key | TotalKMMapMod.AnyKey(key) :: INodeAt(betreeNode, key)
  }

  function IStampedBetree(stampedBetree: StampedBetree) : StampedMap
    requires stampedBetree.WF()
  {
    StampedMap(INode(stampedBetree.root), stampedBetree.seqEnd)
  }
    
  function I(v: Variables) : StampedMap
    requires v.WF()
  {
    IStampedBetree(v.stampedBetree.PrependMemtable(v.memtable))
  }

  lemma NoopSteps(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires v.WF()
    requires v'.WF()
    requires NextStep(v, v', lbl, step)
    requires !step.PutStep?
    ensures I(v') == I(v)
  {
    match step {
      case QueryStep(receipt) => {
        assert Query(v, v', lbl, receipt);
        assert v' == v;
        assert I(v') == I(v);
      }
      case PutStep() => {
        assert false;
      }
      case QueryEndLsnStep() => {
        assert I(v') == I(v);
      }
      case FreezeAsStep(stampedBetree) => {
        assert I(v') == I(v);
      }
      case InternalSplitStep(_, _) => {
        assert I(v') == I(v);
      }
      case InternalFlushStep(_, _) => {
        assert I(v') == I(v);
      }
      case InternalCompactStep(_, _) => {
        assert I(v') == I(v);
      }
    }
  }
}
