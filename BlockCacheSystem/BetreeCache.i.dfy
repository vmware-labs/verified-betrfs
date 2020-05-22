include "BlockCache.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../PivotBetree/PivotBetree.i.dfy"
include "../PivotBetree/PivotBetreeSpecWFNodes.i.dfy"
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
  type Constants = BC.Constants

  type Op = BC.Op

  predicate Init(k: Constants, s: Variables) {
    BC.Init(k, s)
  }

  datatype Step =
    | BetreeMoveStep(betreeStep: BetreeStep)
    | BlockCacheMoveStep(blockCacheStep: BC.Step)

  predicate BetreeMove(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
  {
    && vop.AdvanceOp?
    && dop.NoDiskOp?
    && s.Ready?
    && ValidBetreeStep(betreeStep)
    && BC.Reads(k, s, BetreeStepReads(betreeStep))
    && BC.Transaction(k, s, s', dop, vop, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, vop.uiop)
  }

  predicate BlockCacheMove(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step) {
    && !step.TransactionStep?

    && BC.NextStep(k, s, s', dop, vop, step)
    && (dop.RespReadNodeOp? && dop.node.Some? ==>
      WFNode(dop.node.value)
    )
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: Step) {
    match step {
      case BetreeMoveStep(step) => BetreeMove(k, s, s', dop, vop, step)
      case BlockCacheMoveStep(step) => BlockCacheMove(k, s, s', dop, vop, step)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp) {
    exists step: Step :: NextStep(k, s, s', dop, vop, step)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && BC.Inv(k, s)
    && (s.Ready? ==> (forall ref | ref in s.cache :: PivotBetreeSpec.WFNode(s.cache[ref])))
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    BC.InitImpliesInv(k, s);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
  requires Inv(k, s)
  requires BetreeMove(k, s, s', dop, vop, betreeStep)
  ensures Inv(k, s')
  {
    var ops := BetreeStepOps(betreeStep);
    BC.TransactionStepPreservesInv(k, s, s', D.NoDiskOp, vop, ops);

    forall i | 0 <= i < |BetreeStepReads(betreeStep)|
    ensures WFNode(BetreeStepReads(betreeStep)[i].node)
    {
      assert BC.ReadStep(k, s, BetreeStepReads(betreeStep)[i]);
    }

    PivotBetreeSpecWFNodes.ValidStepWritesWFNodes(betreeStep);
  }

  lemma BlockCacheMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
  requires Inv(k, s)
  requires BlockCacheMove(k, s, s', dop, vop, step)
  ensures Inv(k, s')
  {
    BC.NextStepPreservesInv(k, s, s', dop, vop, step);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', dop, vop, step)
  ensures Inv(k, s')
  {
    match step {
      case BetreeMoveStep(step) => BetreeMoveStepPreservesInv(k, s, s', dop, vop, step);
      case BlockCacheMoveStep(step) => BlockCacheMoveStepPreservesInv(k, s, s', dop, vop, step);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
  requires Inv(k, s)
  requires Next(k, s, s', dop, vop)
  ensures Inv(k, s')
  {
    var step: Step :| NextStep(k, s, s', dop, vop, step);
    NextStepPreservesInv(k, s, s', dop, vop, step);
  }
}
