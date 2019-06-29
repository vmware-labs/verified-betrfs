include "BlockCache.dfy"
include "Betree.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "BlockCacheSystemCrashSafeBlockInterfaceRefinement.dfy"
include "BetreeSpec.dfy"
include "DiskAccessModel.dfy"

include "Main.dfy"

module BetreeBlockCache refines Machine {
  import opened Maps
  import opened Sequences

  import opened BetreeSpec`Spec
  import G = BetreeGraph
  import BC = BetreeGraphBlockCache
  import DB = Betree
  import BI = BetreeBlockInterface

  type Variables = BC.Variables
  type Constants = BC.Constants
  type LBA = BC.LBA
  type Sector = BC.Sector
  //type UIOp = DB.UIOp

  type Op = BC.Op

  predicate Init(k: Constants, s: Variables) {
    BC.Init(k, s)
  }

  predicate Inv(k: Constants, s: Variables) {
    BC.Inv(k, s)
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
    && uiop.NoOp?
    && (
      || step.WriteBackStep?
      || step.WriteBackSuperblockStep?
      || step.UnallocStep?
      || step.PageInStep?
      || step.PageInSuperblockStep?
      || step.EvictStep?
    )
    && BC.NextStep(k, s, s', dop, step)
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

  function BIStepsToOps(step: seq<BI.Step>) : seq<Op>

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, betreeStep: BetreeStep)
  requires Inv(k, s)
  requires BetreeMove(k, s, s', uiop, dop, betreeStep)
  ensures Inv(k, s')
  {
    var ops :| BC.OpTransaction(k, s, s', ops);
    BC.TransactionStepPreservesInvariant(k, s, s', D.NoDiskOp, ops);
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
