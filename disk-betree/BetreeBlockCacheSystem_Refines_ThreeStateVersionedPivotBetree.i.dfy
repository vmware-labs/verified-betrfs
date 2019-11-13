include "AsyncSectorDiskModel.i.dfy"
include "PivotBetree_Refines_Betree.i.dfy"
include "BlockCache.i.dfy"
include "../lib/Maps.s.dfy"
include "../lib/sequences.i.dfy"
include "BlockCacheSystem.i.dfy"
include "BetreeBlockCache.i.dfy"
include "BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy"
include "ThreeStateVersionedPivotBetree.i.dfy"
include "BetreeBlockCacheSystem.i.dfy"
//
// Take the whole crash-safe BlockCacheSystem, and constrain it to
// run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
// Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
// map.)
//

module BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree {
  import opened Maps
  import opened Sequences

  import BBCS = BetreeBlockCacheSystem
  import TSV = ThreeStateVersionedPivotBetree

  import opened PivotBetreeSpec`Spec
  import BC = BetreeGraphBlockCache
  import BCS = BetreeGraphBlockCacheSystem
  import BT = PivotBetree
  import BTI = PivotBetreeInvAndRefinement
  import BI = PivotBetreeBlockInterface
  import Ref = BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface
  import D = AsyncSectorDisk
  import ThreeState = ThreeStateTypes

  import M = BetreeBlockCache
  type UIOp = BBCS.UIOp

  function Ik(k: BBCS.Constants) : TSV.Constants
  {
    TSV.Constants(BT.Constants(BI.Constants()))
  }

  function I(k: BBCS.Constants, s: BBCS.Variables) : TSV.Variables
  requires BBCS.Inv(k, s)
  {
    TSV.Variables(
      BBCS.PersistentBetree(k, s),
      BBCS.FrozenBetree(k, s),
      BBCS.EphemeralBetree(k, s),
      Ref.SyncReqs(k, s)
    )
  }

  // Proofs

  lemma RefinesInit(k: BBCS.Constants, s: BBCS.Variables)
    requires BBCS.Init(k, s)
    ensures BBCS.Inv(k, s)
    ensures TSV.Init(Ik(k), I(k, s))
  {
    BCS.InitImpliesInv(k, s);
    BTI.InitImpliesInv(Ik(k).k, BBCS.PersistentBetree(k, s));
    Ref.InitImpliesGraphsEq(k, s);
    Ref.reveal_SyncReqs();
  }

  lemma BetreeMoveStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp, dop: M.DiskOp, betreeStep: BetreeStep)
    requires BBCS.Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, uiop, dop, betreeStep)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.MachineStep(dop, BC.TransactionStep(BetreeStepOps(betreeStep))));
    Ref.StepSyncReqs(k, s, s', BCS.MachineStep(dop, BC.TransactionStep(BetreeStepOps(betreeStep))));
    Ref.RefinesReads(k, s, BetreeStepReads(betreeStep));
    assert BT.NextStep(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop, BT.BetreeStep(betreeStep));
    BTI.NextPreservesInv(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop);

    assert TSV.Move3(Ik(k), I(k, s), I(k, s'), uiop);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
  }

  lemma BlockCacheMoveStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp, dop: M.DiskOp, step: BC.Step)
    requires BBCS.Inv(k, s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, uiop, dop, step)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.MachineStep(dop, step));
    Ref.StepSyncReqs(k, s, s', BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(Ik(k).bck, EphemeralBetree(k, s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(k, s, s', dop, step.ref);
      /*assert step.ref in EphemeralBetree(k, s).bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(Ik(k).bck, EphemeralBetree(k, s).bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(k, s).bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(k, s).bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(k, s).bcv.view, iset{step.ref});*/
      assert BT.GC(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop, iset{step.ref});
      BTI.GCStepRefines(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop, iset{step.ref});

      assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.GCStep(iset{step.ref}));
      assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
    } else {
      if (step.FreezeStep?) {
        assert TSV.Move2to3(Ik(k), I(k, s), I(k, s'), uiop);
        assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move2to3Step);
        assert TSV.Next(Ik(k), I(k, s), I(k, s'), uiop);
      } else if (step.PushSyncReqStep?) {
        assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.PushSyncStep(step.id as int));
      } else if (step.PopSyncReqStep?) {
        assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.PopSyncStep(step.id as int));
      } else {
        // everything else is a no-op
        assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.StutterStep);
        assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
      }
    }
  }

  lemma CrashStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp)
    requires BBCS.Inv(k, s)
    requires BBCS.Crash(k, s, s', uiop)
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.CrashStep);
    Ref.StepSyncReqs(k, s, s', BCS.CrashStep);
    assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.CrashStep);
  }

  lemma DiskInternalStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp, step: D.InternalStep)
    requires BBCS.Inv(k, s)
    requires BBCS.DiskInternal(k, s, s', uiop, step)
    requires uiop.NoOp?
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.DiskInternalStep(step));
    Ref.StepSyncReqs(k, s, s', BCS.DiskInternalStep(step));
    if (TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move1to2Step)) {
      assert TSV.Next(Ik(k), I(k, s), I(k, s'), uiop);
    } else {
      assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.StutterStep);
      assert TSV.Move3(Ik(k), I(k, s), I(k, s'), uiop);
      assert TSV.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSV.Move3Step);
    }
  }

  lemma NextStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp, step: BBCS.Step)
    requires BBCS.Inv(k, s)
    requires BBCS.NextStep(k, s, s', uiop, step)
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepRefines(k, s, s', uiop, dop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepRefines(k, s, s', uiop, dop, blockCacheStep);
        }
      }
      case DiskInternalStep(step) => DiskInternalStepRefines(k, s, s', uiop, step);
      case CrashStep => CrashStepRefines(k, s, s', uiop);
    }
  }

  lemma RefinesNext(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp)
    requires BBCS.Inv(k, s)
    requires BBCS.Next(k, s, s', uiop)
    ensures BBCS.Inv(k, s')
    ensures TSV.Next(Ik(k), I(k, s), I(k, s'), uiop);
  {
    var step :| BBCS.NextStep(k, s, s', uiop, step);
    NextStepRefines(k, s, s', uiop, step);
  }
}
