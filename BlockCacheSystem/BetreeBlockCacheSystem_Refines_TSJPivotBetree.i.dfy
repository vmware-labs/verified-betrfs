include "../BlockCacheSystem/AsyncSectorDiskModel.i.dfy"
include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../BlockCacheSystem/BlockCacheSystem.i.dfy"
include "../BlockCacheSystem/BetreeBlockCache.i.dfy"
include "../BlockCacheSystem/BlockCacheSystem_Refines_TSJBlockInterface.i.dfy"
include "../PivotBetree/TSJPivotBetree.i.dfy"
include "../BlockCacheSystem/BetreeBlockCacheSystem.i.dfy"
//
// Take the whole crash-safe BlockCacheSystem, and constrain it to
// run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
// Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
// map.)
//

module BetreeBlockCacheSystem_Refines_TSJPivotBetree {
  import opened Maps
  import opened Sequences

  import BBCS = BetreeBlockCacheSystem
  import TSJ = TSJPivotBetree

  import opened PivotBetreeSpec`Spec
  import opened Journal
  import UI
  import BC = BlockCache
  import BCS = BlockCacheSystem
  import BT = PivotBetree
  import BI = PivotBetreeBlockInterface
  import Ref = BlockCacheSystem_Refines_TSJBlockInterface
  import D = AsyncSectorDisk
  import ThreeState = ThreeStateTypes

  import M = BetreeBlockCache

  function Ik(k: BBCS.Constants) : TSJ.Constants
  {
    TSJ.Constants(BT.Constants(BI.Constants()))
  }

  function I(k: BBCS.Constants, s: BBCS.Variables) : TSJ.Variables
  requires BBCS.Inv(k, s)
  {
    TSJ.Variables(
      BBCS.PersistentBetree(k, s),
      BBCS.FrozenBetree(k, s),
      BBCS.EphemeralBetree(k, s),
      BCS.PersistentJournal(s),
      BCS.FrozenJournal(s),
      BCS.EphemeralJournal(s),
      BCS.GammaJournal(s),
      BCS.DeltaJournal(s),
      Ref.SyncReqs(k, s)
    )
  }

  // Proofs

  lemma RefinesInit(k: BBCS.Constants, s: BBCS.Variables)
    requires BBCS.Init(k, s)
    ensures BBCS.Inv(k, s)
    ensures TSJ.Init(Ik(k), I(k, s))
  {
    BCS.InitImpliesInv(k, s);
    BT.InitImpliesInv(Ik(k).k, BBCS.PersistentBetree(k, s));
    BCS.InitGraphs(k, s);
    BCS.InitJournals(k, s);
    Ref.reveal_SyncReqs();
  }

  lemma BetreeMoveStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op, dop: M.DiskOp, betreeStep: BetreeStep, js: M.JournalUIOpStep)
    requires BBCS.Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, uiop, dop, betreeStep, js)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var j := if js.JSNew? then (
        BC.JSNew(JournalEntriesForUIOp(uiop))
      ) else (
        BC.JSReplay(JournalEntriesForUIOp(js.replayedUIOp))
      );

    var ruiop := if js.JSNew? then uiop else js.replayedUIOp;

    var transactionStep := BC.TransactionStep(BetreeStepOps(betreeStep), j);
    Ref.StepGraphs(k, s, s', BCS.MachineStep(dop, transactionStep));
    Ref.StepSyncReqs(k, s, s', BCS.MachineStep(dop, transactionStep));
    Ref.RefinesReads(k, s, BetreeStepReads(betreeStep));
    assert BT.NextStep(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), ruiop, BT.BetreeStep(betreeStep));
    BT.NextPreservesInv(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), ruiop);

    if (js.JSNew?) {
      assert TSJ.Move3(Ik(k), I(k, s), I(k, s'), uiop);
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move3Step);
    } else {
      assert TSJ.Replay(Ik(k), I(k, s), I(k, s'), uiop, ruiop);
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(ruiop));
    }
  }

  lemma BlockCacheMoveStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op, dop: M.DiskOp, step: BC.Step)
    requires BBCS.Inv(k, s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, uiop, dop, step)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
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
      BT.GCStepRefines(Ik(k).k, BBCS.EphemeralBetree(k, s), BBCS.EphemeralBetree(k, s'), uiop, iset{step.ref});

      assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.GCStep(iset{step.ref}));

      // TSJ doesn't have an explit NoOp step, but it happens that a NoOp
      // is a special case of a `Replay` step.
      // We can't use a `Move3` step because a Move3 requires s.j3 == [].
      // `Replay` and `Move3` are otherwise equivalent for a uiop=NoOp
      // step like an `unalloc`.

      assert TSJ.Replay(Ik(k), I(k, s), I(k, s'), uiop, UI.NoOp);
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(UI.NoOp));
    } else {
      if Ref.IsFreezeStep(k, s, BCS.MachineStep(dop, step)) {
        if Ref.UpdateMove2to3(k, s, s') {
          assert TSJ.Move2to3(Ik(k), I(k, s), I(k, s'), uiop);
          assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move2to3Step);
          assert TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop);
        } else {
          assert Ref.UpdateExtendLog2(k, s, s');
          assert TSJ.ExtendLog2(Ik(k), I(k, s), I(k, s'), uiop);
          assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog2Step);
          assert TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop);
        }
      } else if (step.PushSyncReqStep?) {
        assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PushSyncStep(step.id as int));
      } else if (step.PopSyncReqStep?) {
        assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PopSyncStep(step.id as int));
      } else {
        // everything else is a no-op
        assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.StutterStep);
        assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(UI.NoOp));
      }
    }
  }

  lemma CrashStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op)
    requires BBCS.Inv(k, s)
    requires BBCS.Crash(k, s, s', uiop)
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.CrashStep);
    Ref.StepSyncReqs(k, s, s', BCS.CrashStep);
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.CrashStep);
  }

  lemma DiskInternalStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op, step: D.InternalStep)
    requires BBCS.Inv(k, s)
    requires BBCS.DiskInternal(k, s, s', uiop, step)
    requires uiop.NoOp?
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref.StepGraphs(k, s, s', BCS.DiskInternalStep(step));
    Ref.StepSyncReqs(k, s, s', BCS.DiskInternalStep(step));
    if Ref.IsPersistStep(k, s, BCS.DiskInternalStep(step)) {
      if Ref.UpdateMove1to2(k, s, s') {
        assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move1to2Step);
        assert TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop);
      } else {
        assert Ref.UpdateExtendLog1(k, s, s');
        assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog1Step);
        assert TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop);
      }
    } else {
      assert BT.NextStep(Ik(k).k, I(k, s).s3, I(k, s').s3, uiop, BT.StutterStep);
      assert TSJ.Replay(Ik(k), I(k, s), I(k, s'), uiop, UI.NoOp);
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(UI.NoOp));
    }
  }

  lemma NextStepRefines(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op, step: BBCS.Step)
    requires BBCS.Inv(k, s)
    requires BBCS.NextStep(k, s, s', uiop, step)
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep, js) => BetreeMoveStepRefines(k, s, s', uiop, dop, betreeStep, js);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepRefines(k, s, s', uiop, dop, blockCacheStep);
        }
      }
      case DiskInternalStep(step) => DiskInternalStepRefines(k, s, s', uiop, step);
      case CrashStep => CrashStepRefines(k, s, s', uiop);
    }
  }

  lemma RefinesNext(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UI.Op)
    requires BBCS.Inv(k, s)
    requires BBCS.Next(k, s, s', uiop)
    ensures BBCS.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop);
  {
    var step :| BBCS.NextStep(k, s, s', uiop, step);
    NextStepRefines(k, s, s', uiop, step);
  }
}
