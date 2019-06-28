include "Disk.dfy"
include "BetreeInv.dfy"
include "BlockCache.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "BlockCacheSystem.dfy"
include "BetreeBlockCache.dfy"
include "BlockCacheSystemCrashSafeBlockInterfaceRefinement.dfy"

abstract module BetreeBlockCacheSystem refines DiskAccessModel {
  import opened Maps
  import opened Sequences

  import opened BetreeSpec`Spec
  import BC = BetreeGraphBlockCache
  import BCS = BetreeGraphBlockCacheSystem
  import DB = Betree
  import DBI = BetreeInv
  import BI = BetreeBlockInterface
  import Ref = BlockCacheSystemCrashSafeBlockInterfaceRefinement

  import M = BetreeBlockCache

  function DBConst(k: Constants) : DB.Constants {
    DB.Constants(BI.Constants())
  }

  // Invariant

  function PersistentBetree(k: Constants, s: Variables) : DB.Variables
  requires BCS.Inv(k, s)
  {
    DB.Variables(BI.Variables(MapToImap(BCS.PersistentGraph(k, s))))
  }

  function EphemeralBetree(k: Constants, s: Variables) : DB.Variables
  requires BCS.Inv(k, s)
  requires s.machine.Ready?
  {
    DB.Variables(BI.Variables(MapToImap(BCS.EphemeralGraph(k, s))))
  }

  predicate Inv(k: Constants, s: Variables) {
    && BCS.Inv(k, s)
    && DBI.Inv(DBConst(k), PersistentBetree(k, s))
    && (s.machine.Ready? ==> DBI.Inv(DBConst(k), EphemeralBetree(k, s)))
  }

  // Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
    BCS.InitImpliesInv(k, s);
  }

  lemma PersistentGraphEqAcrossOps(k: Constants, s: Variables, s': Variables, ops: seq<BC.Op>)
    requires BC.OpTransaction(k.machine, s.machine, s'.machine, ops);
    requires BCS.Inv(k, s)
    requires BCS.Inv(k, s')
    requires s.disk == s'.disk
    ensures PersistentBetree(k, s) == PersistentBetree(k, s')
    decreases |ops|
  {
    if |ops| == 0 {
    } else if |ops| == 1 {
      BCS.OpPreservesInvariant(k, s, s', ops[0]);
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := DAMTypes.DAMVariables(mid, s.disk);
      BCS.TransactionStepPreservesInvariant(k, s, smid, D.NoDiskOp, ops1);
      PersistentGraphEqAcrossOps(k, s, smid, ops1);
      PersistentGraphEqAcrossOps(k, smid, s', ops2);
    }
  }
    /*
// TODO this verifies but takes about a minute for some reason?
  {
    var path: seq<BC.Variables> :| BC.IsStatePath(k.machine, s.machine, s'.machine, ops, path);
    var i := 0;
    while i < |path| - 1
    invariant i <= |path| - 1
    invariant BCS.Inv(k, BCS.Variables(path[i], s.disk))
    invariant PersistentBetree(k, BCS.Variables(path[i], s.disk))
           == PersistentBetree(k, s)
    {
      BCS.OpPreservesInvariant(k, BCS.Variables(path[i], s.disk), BCS.Variables(path[i+1], s.disk), ops[i]);
      i := i + 1;
    }
  }
  */

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: M.UIOp, dop: DiskOp, betreeStep: BetreeStep)
    requires Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, uiop, dop, betreeStep)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
    var ops := BetreeStepOps(betreeStep);
    BCS.TransactionStepPreservesInvariant(k, s, s', D.NoDiskOp, ops);
    PersistentGraphEqAcrossOps(k, s, s', ops); 
    if (s.machine.Ready?) {
      Ref.RefinesOpTransaction(k, s, s', ops);
      DBI.BetreeStepPreservesInvariant(DBConst(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, betreeStep);
    }
  }

  lemma WriteBackStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: BCS.Reference)
    requires Inv(k, s)
    requires BC.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.WriteBackStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma WriteBackSuperblockStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires BCS.Inv(k, s')
    requires BC.WriteBackSuperblock(k.machine, s.machine, s'.machine, dop)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.WriteBackSuperblockStepSyncsGraphs(k, s, s', dop);
  }

  lemma UnallocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: BCS.Reference)
    requires Inv(k, s)
    requires BCS.Inv(k, s')
    requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.UnallocStepPreservesPersistentGraph(k, s, s', dop, ref);

    Ref.RefinesUnalloc(k, s, s', dop, ref);
    DBI.GCStepPreservesInvariant(DBConst(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), iset{ref});
  }

  lemma PageInStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: BCS.Reference)
    requires Inv(k, s)
    requires BCS.Inv(k, s')
    requires BC.PageIn(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.PageInStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma PageInSuperblockStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires BCS.Inv(k, s')
    requires BC.PageInSuperblock(k.machine, s.machine, s'.machine, dop)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.PageInSuperblockStepPreservesGraphs(k, s, s', dop);
  }

  lemma EvictStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: BCS.Reference)
    requires Inv(k, s)
    requires BCS.Inv(k, s')
    requires BC.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    BCS.EvictStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma BlockCacheStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: M.UIOp, dop: DiskOp, step: BC.Step)
    requires Inv(k, s)
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, uiop, dop, step)
    requires Dam(k, s, s', CrashTypes.NormalOp(uiop), dop)
    ensures Inv(k, s')
  {
    assert BCS.Machine(k, s, s', dop);
    assert BCS.NextStep(k, s, s', BCS.MachineStep(dop));
    BCS.NextPreservesInv(k, s, s');

    match step {
      case WriteBackStep(ref) => WriteBackStepPreservesInv(k, s, s', dop, ref);
      case WriteBackSuperblockStep => WriteBackSuperblockStepPreservesInv(k, s, s', dop);
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, ref);
      case PageInStep(ref) => PageInStepPreservesInv(k, s, s', dop, ref);
      case PageInSuperblockStep => PageInSuperblockStepPreservesInv(k, s, s', dop);
      case EvictStep(ref) => EvictStepPreservesInv(k, s, s', dop, ref);
      case TransactionStep(ops) => { assert false; }
    }
  }

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Dam(k, s, s', uiop, dop)
    ensures Inv(k, s')
  {
    var step :| M.NextStep(k.machine, s.machine, s'.machine, uiop.uiop, dop, step);
    match step {
      case BetreeMoveStep(betreeStep) => BetreeMoveStepPreservesInv(k, s, s', uiop.uiop, dop, betreeStep);
      case BlockCacheMoveStep(blockCacheStep) => BlockCacheStepPreservesInv(k, s, s', uiop.uiop, dop, blockCacheStep);
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp)
    requires Inv(k, s)
    requires Crash(k, s, s', uiop)
    ensures Inv(k, s')
  {
    
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
    match step {
      case DamStep(dop: DiskOp) => MachineStepPreservesInv(k, s, s', uiop, dop);
      case CrashStep => CrashStepPreservesInv(k, s, s', uiop);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInv(k, s, s', uiop, step);
  }
}
