include "BlockCache.dfy"
include "DiskBetree.dfy"
include "../lib/Maps.dfy"

module BetreeGraphBlockCache refines BlockCache {
  import G = BetreeGraph
}

module BtreeBlockCache {
  import opened Maps

  import G = BetreeGraph
  import BC = BetreeGraphBlockCache
  import DB = DiskBetree
  import D = Disk

  type Variables = BC.Variables
  type Constants = BC.Constants

  type DiskOp = BC.DiskOp

  predicate Init(k: Constants, s: Variables) {
    BC.Init(k, s)
  }

  predicate Inv(k: Constants, s: Variables) {
    BC.Inv(k, s)
  }

  datatype Step =
    | BetreeMoveStep(betreeStep: DB.Step)
    | BlockCacheMoveStep(blockCacheStep: BC.Step)

  predicate BetreeMove(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: DB.Step) {
    && dop.NoDiskOp?
    && (
      || step.InsertMessageStep?
      || step.FlushStep?
      || step.GrowStep?
      || step.SplitStep?
    )
    && s.Ready?
    && s'.Ready?
    && s' == s.(cache := s'.cache)
    && DB.NextStep(
        DB.Constants(DB.BI.Constants()),
        DB.Variables(DB.BI.Variables(MapToImap(s.cache))),
        DB.Variables(DB.BI.Variables(MapToImap(s'.cache))),
        step)
  }

  predicate BlockCacheMove(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: BC.Step) {
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

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case BetreeMoveStep(step) => BetreeMove(k, s, s', dop, step)
      case BlockCacheMoveStep(step) => BlockCacheMove(k, s, s', dop, step)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step: Step :: NextStep(k, s, s', dop, step)
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    BC.InitImpliesInv(k, s);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: DB.Step)
  requires Inv(k, s)
  requires BetreeMove(k, s, s', dop, step)
  ensures Inv(k, s')
  {
    
  }

  lemma BlockCacheMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: BC.Step)
  requires Inv(k, s)
  requires BlockCacheMove(k, s, s', dop, step)
  ensures Inv(k, s')
  {
    BC.NextStepPreservesInv(k, s, s', dop, step);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', dop, step)
  ensures Inv(k, s')
  {
    match step {
      case BetreeMoveStep(step) => BetreeMoveStepPreservesInv(k, s, s', dop, step);
      case BlockCacheMoveStep(step) => BlockCacheMoveStepPreservesInv(k, s, s', dop, step);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  requires Inv(k, s)
  requires Next(k, s, s', dop)
  ensures Inv(k, s')
  {
    var step: Step :| NextStep(k, s, s', dop, step);
    NextStepPreservesInv(k, s, s', dop, step);
  }
}
