include "BlockCache.i.dfy"
include "../lib/Maps.s.dfy"
include "../lib/sequences.s.dfy"
include "AsyncSectorDiskModel.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "PivotBetree.i.dfy"

module BetreeBlockCache refines AsyncSectorDiskMachine {
  import opened Maps
  import opened Sequences

  import opened PivotBetreeSpec`Spec
  import G = PivotBetreeGraph
  import BC = BetreeGraphBlockCache
  import BI = BetreeBlockInterface
  import PivotBetreeSpecWFNodes

  type Variables = BC.Variables
  type Constants = BC.Constants
  type LBA = BC.LBA
  type Sector = BC.Sector

  type Op = BC.Op

  predicate Init(k: Constants, s: Variables) {
    BC.Init(k, s)
  }

  predicate Inv(k: Constants, s: Variables) {
    && BC.Inv(k, s)
    && (s.Ready? ==> (forall ref | ref in s.cache :: PivotBetreeSpec.WFNode(s.cache[ref])))
  }

  datatype Step =
    | BetreeMoveStep(betreeStep: BetreeStep)
    | BlockCacheMoveStep(blockCacheStep: BC.Step)

  predicate BetreeMove(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, betreeStep: BetreeStep)
  {
    && dop.NoDiskOp?
    && s.Ready?
    && ValidBetreeStep(betreeStep)
    && BC.Reads(k, s, BetreeStepReads(betreeStep))
    && BC.OpTransaction(k, s, s', BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, uiop)
  }

  predicate BlockCacheMove(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: BC.Step) {
    && !step.TransactionStep?
    && (step.PushSyncReqStep? ==> uiop.PushSyncOp? && step.id == uiop.id)
    && (step.PopSyncReqStep? ==> uiop.PopSyncOp? && step.id == uiop.id)
    && (!step.PushSyncReqStep? && !step.PopSyncReqStep? ==> uiop.NoOp?)

    && BC.NextStep(k, s, s', dop, step)
    && (dop.RespReadOp? && dop.respRead.sector.Some? && dop.respRead.sector.value.SectorBlock? ==>
      WFNode(dop.respRead.sector.value.block)
    )
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: Step) {
    match step {
      case BetreeMoveStep(step) => BetreeMove(k, s, s', uiop, dop, step)
      case BlockCacheMoveStep(step) => BlockCacheMove(k, s, s', uiop, dop, step)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp) {
    exists step: Step :: NextStep(k, s, s', uiop, dop, step)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    BC.InitImpliesInv(k, s);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, betreeStep: BetreeStep)
  requires Inv(k, s)
  requires BetreeMove(k, s, s', uiop, dop, betreeStep)
  ensures Inv(k, s')
  {
    var ops :| BC.OpTransaction(k, s, s', ops);
    BC.TransactionStepPreservesInv(k, s, s', D.NoDiskOp, ops);
    PivotBetreeSpecWFNodes.ValidStepWritesWFNodes(betreeStep);
  }

  lemma BlockCacheMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: BC.Step)
  requires Inv(k, s)
  requires BlockCacheMove(k, s, s', uiop, dop, step)
  ensures Inv(k, s')
  {
    BC.NextStepPreservesInv(k, s, s', dop, step);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, dop, step)
  ensures Inv(k, s')
  {
    match step {
      case BetreeMoveStep(step) => BetreeMoveStepPreservesInv(k, s, s', uiop, dop, step);
      case BlockCacheMoveStep(step) => BlockCacheMoveStepPreservesInv(k, s, s', uiop, dop, step);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires Next(k, s, s', uiop, dop)
  ensures Inv(k, s')
  {
    var step: Step :| NextStep(k, s, s', uiop, dop, step);
    NextStepPreservesInv(k, s, s', uiop, dop, step);
  }
}
