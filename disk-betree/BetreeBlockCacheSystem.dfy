include "Disk.dfy"
include "BlockCache.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "BlockCacheSystem.dfy"
include "BetreeBlockCache.dfy"

module BetreeGraphBlockCacheSystem refines BlockCacheSystem {
  import M = BetreeGraphBlockCache
}

module BetreeBlockCacheSystem {
  import opened Maps
  import opened Sequences

  import BC = BetreeGraphBlockCache
  import BCS = BetreeGraphBlockCacheSystem
  import DB = DiskBetree
  import M = BetreeBlockCache
  import D = Disk

  type Constants = BCS.Constants
  type Variables = BCS.Variables
  type DiskOp = M.DiskOp

  predicate Init(k: Constants, s: Variables)
  {
    BCS.Init(k, s)
  }

  datatype Step =
    | MachineStep(dop: DiskOp)
    | CrashStep

  predicate Machine(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', dop)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  // Invariant

  predicate Inv(k: Constants, s: Variables) {
    && BCS.Inv(k, s)
    // TODO add btree invariants here
  }

  // Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    BCS.InitImpliesInv(k, s);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: DB.Step)
    requires Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, dop, step)
    requires s.disk == s'.disk
    ensures Inv(k, s')

  lemma BlockCacheStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: BC.Step)
    requires Inv(k, s)
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, dop, step)
    requires Machine(k, s, s', dop)
    ensures Inv(k, s')
  {
    assert BCS.Machine(k, s, s', dop);
    assert BCS.NextStep(k, s, s', BCS.MachineStep(dop));
    BCS.NextPreservesInv(k, s, s');
  }

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| M.NextStep(k.machine, s.machine, s'.machine, dop, step);
    match step {
      case BetreeMoveStep(betreeStep) => BetreeMoveStepPreservesInv(k, s, s', dop, betreeStep);
      case BlockCacheMoveStep(blockCacheStep) => BlockCacheStepPreservesInv(k, s, s',dop, blockCacheStep);
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Crash(k, s, s')
    ensures Inv(k, s')
  {
    
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop: DiskOp) => MachineStepPreservesInv(k, s, s', dop);
      case CrashStep => CrashStepPreservesInv(k, s, s');
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInv(k, s, s', step);
  }
}
