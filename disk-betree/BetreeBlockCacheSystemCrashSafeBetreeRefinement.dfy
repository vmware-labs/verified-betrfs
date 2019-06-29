include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "BetreeBlockCacheSystem.dfy"
include "CrashSafe.dfy"
include "Betree.dfy"

abstract module BetreeBlockCacheSystemCrashSafeBetreeRefinement {
  import opened Maps
  import opened Sequences
  import opened PivotBetreeSpec`Spec
  import CrashTypes

  import G = PivotBetreeGraph
  import BBCS = BetreeBlockCacheSystem
  import BCS = BetreeGraphBlockCacheSystem
  import M = BetreeBlockCache
  import BC = BetreeGraphBlockCache
  import D = Disk
  import CSBT = CrashSafePivotBetree
  import BT = PivotBetree
  import BI = PivotBetreeBlockInterface
  import DBI = PivotBetreeInvAndRefinement
  import Ref = BlockCacheSystemCrashSafeBlockInterfaceRefinement

  type DiskOp = M.DiskOp
  type Reference = G.Reference
  type CrashableUIOp = BBCS.CrashableUIOp

  function Ik(k: BBCS.Constants) : CSBT.Constants {
    BT.Constants(BI.Constants())
  }

  function I(k: BBCS.Constants, s: BBCS.Variables) : CSBT.Variables
  requires BBCS.Inv(k, s)
  {
    CSBT.Variables(
      BBCS.PersistentBetree(k, s),
      if s.machine.Ready? then BBCS.EphemeralBetree(k, s) else BBCS.PersistentBetree(k, s)
    )
  }

  lemma RefinesInit(k: BBCS.Constants, s: BBCS.Variables)
  requires BBCS.Init(k, s)
  ensures BBCS.Inv(k, s)
  ensures CSBT.Init(Ik(k), I(k, s))
  // TODO figure out how initial conditions are going to work
  // Right now the BlockCacheSystem assumes any valid disk
  // whereas the Betree requires the Betree to start empty

  lemma RefinesBetreeMoveStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, betreeStep: BetreeStep)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires M.BetreeMove(k.machine, s.machine, s'.machine, uiop, dop, betreeStep)
  requires D.Next(k.disk, s.disk, s'.disk, dop)
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    assert s.machine.Ready?;

    // TODO duplication with BetreeMoveStepPreservesInv

    var ops := BetreeStepOps(betreeStep);
    BCS.TransactionStepPreservesInvariant(k, s, s', D.NoDiskOp, ops);
    BBCS.PersistentGraphEqAcrossOps(k, s, s', ops); 
    Ref.RefinesOpTransaction(k, s, s', ops);
    DBI.BetreeStepRefines(Ik(k), BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop, betreeStep);

    assert I(k, s).persistent == I(k, s').persistent;
    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.BetreeStep(betreeStep));
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  // TODO I suspect a lot of the below handling of BlockCache operations
  // can be reduced to stuff in the general
  // BlockCacheSystem -> CrashSafeBlockInterface proof.

  lemma RefinesWriteBackStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, ref: Reference)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Write(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.WriteBackStepPreservesGraphs(k, s, s', dop, ref);
    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.StutterStep);
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  lemma RefinesWriteBackSuperblockStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.WriteBackSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Write(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.WriteBackSuperblockStepSyncsGraphs(k, s, s', dop);
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.SyncStep);
  }

  lemma RefinesUnallocStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, ref: Reference)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.UnallocStepPreservesPersistentGraph(k, s, s', dop, ref);

    Ref.RefinesUnalloc(k, s, s', dop, ref);
    DBI.GCStepRefines(Ik(k), BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), M.DB.MS.UI.NoOp, iset{ref});

    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.GCStep(iset{ref}));
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  lemma RefinesPageInStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, ref: Reference)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.PageIn(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Read(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.PageInStepPreservesGraphs(k, s, s', dop, ref);
    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.StutterStep);
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  lemma RefinesPageInSuperblockStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.PageInSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Read(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.PageInSuperblockStepPreservesGraphs(k, s, s', dop);
    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.StutterStep);
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  lemma RefinesEvictStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, ref: Reference)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires BC.Evict(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop);
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    BCS.EvictStepPreservesGraphs(k, s, s', dop, ref);
    assert BT.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, uiop, BT.StutterStep);
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop), CSBT.EphemeralMoveStep);
  }

  lemma RefinesBlockCacheMoveStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, step: BC.Step)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.NoOp?
  requires M.BlockCacheMove(k.machine, s.machine, s'.machine, uiop, dop, step)
  requires D.Next(k.disk, s.disk, s'.disk, dop)
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    match step {
      case WriteBackStep(ref) => RefinesWriteBackStep(k, s, s', uiop, dop, ref);
      case WriteBackSuperblockStep => RefinesWriteBackSuperblockStep(k, s, s', uiop, dop);
      case UnallocStep(ref) => RefinesUnallocStep(k, s, s', uiop, dop, ref);
      case PageInStep(ref) => RefinesPageInStep(k, s, s', uiop, dop, ref);
      case PageInSuperblockStep => RefinesPageInSuperblockStep(k, s, s', uiop, dop);
      case EvictStep(ref) => RefinesEvictStep(k, s, s', uiop, dop, ref);
      case TransactionStep(ops) => { assert false; }
    }

  }

  lemma RefinesMachineStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp, step: M.Step)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, step)
  requires D.Next(k.disk, s.disk, s'.disk, dop)
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    match step {
      case BetreeMoveStep(betreeStep) => RefinesBetreeMoveStep(k, s, s', uiop, dop, betreeStep);
      case BlockCacheMoveStep(step) => RefinesBlockCacheMoveStep(k, s, s', uiop, dop, step);
    }
  }

  lemma RefinesMachine(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: M.UIOp, dop: DiskOp)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.Next(k.disk, s.disk, s'.disk, dop)
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), CrashTypes.NormalOp(uiop))
  {
    var step: M.Step :| M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, step);
    RefinesMachineStep(k, s, s', uiop, dop, step);
  }

  lemma RefinesCrash(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: CrashableUIOp)
  requires BBCS.Inv(k, s)
  requires BBCS.Inv(k, s')
  requires uiop.CrashOp?
  requires M.Init(k.machine, s'.machine)
  requires s.disk == s'.disk
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert I(k, s').ephemeral == I(k, s).persistent;
    assert I(k, s').persistent == I(k, s).persistent;
    assert CSBT.NextStep(Ik(k), I(k, s), I(k, s'), uiop, CSBT.CrashStep);
  }

  lemma RefinesNextStep(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: CrashableUIOp, step: BBCS.Step)
  requires BBCS.Inv(k, s)
  requires BBCS.NextStep(k, s, s', uiop, step)
  ensures BBCS.Inv(k, s')
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    BBCS.NextPreservesInv(k, s, s', uiop);
    match step {
      case DamStep(dop) => RefinesMachine(k, s, s', uiop.uiop, dop);
      case CrashStep => RefinesCrash(k, s, s', uiop);
    }
  }

  lemma RefinesNext(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: CrashableUIOp)
  requires BBCS.Inv(k, s)
  requires BBCS.Next(k, s, s', uiop)
  ensures BBCS.Inv(k, s')
  ensures CSBT.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| BBCS.NextStep(k, s, s', uiop, step);
    RefinesNextStep(k, s, s', uiop, step);
  }

}
