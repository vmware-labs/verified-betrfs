// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BlockCache.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../PivotBetree/PivotBetree.i.dfy"
include "../PivotBetree/PivotBetreeSpecWFNodes.i.dfy"
include "../MapSpec/Journal.i.dfy"

//
// Bind a Betree to a BlockCache to get the behavior of both: the map implementation of a Betree,
// and the crash-safety implementation of a BlockCache.
//

module BetreeCache refines BlockMachine {
  import opened Maps
  import opened Sequences
  import opened SectorType
  import opened Journal

  import opened PivotBetreeSpec`Spec
  import G = PivotBetreeGraph
  import BC = BlockCache
  import BI = BetreeBlockInterface
  import PivotBetreeSpecWFNodes

  type Variables = BC.Variables

  type Op = BC.Op

  predicate Init(s: Variables) {
    BC.Init(s)
  }

  datatype Step =
    | BetreeMoveStep(betreeStep: BetreeStep)
    | BlockCacheMoveStep(blockCacheStep: BC.Step)

  predicate BetreeMove(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
  {
    && vop.AdvanceOp?
    && dop.NoDiskOp?
    && s.Ready?
    && ValidBetreeStep(betreeStep)
    && BC.Reads(s, BetreeStepReads(betreeStep))
    && BC.Transaction(s, s', dop, vop, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, vop.uiop)
  }

  predicate BlockCacheMove(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step) {
    && !step.TransactionStep?

    && BC.NextStep(s, s', dop, vop, step)
    && (dop.RespReadNodeOp? && dop.node.Some? ==>
      WFNode(dop.node.value)
    )
  }

  predicate NextStep(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: Step) {
    match step {
      case BetreeMoveStep(step) => BetreeMove(s, s', dop, vop, step)
      case BlockCacheMoveStep(step) => BlockCacheMove(s, s', dop, vop, step)
    }
  }

  predicate Next(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp) {
    exists step: Step :: NextStep(s, s', dop, vop, step)
  }

  predicate Inv(s: Variables)
  {
    && BC.Inv(s)
    && (s.Ready? ==> (forall ref | ref in s.cache :: PivotBetreeSpec.WFNode(s.cache[ref])))
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    BC.InitImpliesInv(s);
  }

  lemma BetreeMoveStepPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
  requires Inv(s)
  requires BetreeMove(s, s', dop, vop, betreeStep)
  ensures Inv(s')
  {
    var ops := BetreeStepOps(betreeStep);
    BC.TransactionStepPreservesInv(s, s', D.NoDiskOp, vop, ops);

    forall i | 0 <= i < |BetreeStepReads(betreeStep)|
    ensures WFNode(BetreeStepReads(betreeStep)[i].node)
    {
      assert BC.ReadStep(s, BetreeStepReads(betreeStep)[i]);
    }

    PivotBetreeSpecWFNodes.ValidStepWritesWFNodes(betreeStep);
  }

  lemma BlockCacheMoveStepPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
  requires Inv(s)
  requires BlockCacheMove(s, s', dop, vop, step)
  ensures Inv(s')
  {
    BC.NextStepPreservesInv(s, s', dop, vop, step);
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: Step)
  requires Inv(s)
  requires NextStep(s, s', dop, vop, step)
  ensures Inv(s')
  {
    match step {
      case BetreeMoveStep(step) => BetreeMoveStepPreservesInv(s, s', dop, vop, step);
      case BlockCacheMoveStep(step) => BlockCacheMoveStepPreservesInv(s, s', dop, vop, step);
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
  requires Inv(s)
  requires Next(s, s', dop, vop)
  ensures Inv(s')
  {
    var step: Step :| NextStep(s, s', dop, vop, step);
    NextStepPreservesInv(s, s', dop, vop, step);
  }
}
