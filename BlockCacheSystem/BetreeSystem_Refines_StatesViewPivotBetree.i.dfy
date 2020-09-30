include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "BetreeSystem.i.dfy"
include "../PivotBetree/StatesViewPivotBetree.i.dfy"
//
// Take the whole crash-safe BlockCacheSystem, and constrain it to
// run the (Pivot)Betree as its client, thereby yielding a 3-state-crash-safe
// Betree. (We'll eventually tie that up the stack to get a 3-state-crash-safe
// map.)
//

module BetreeSystem_Refines_StatesViewPivotBetree {
  import opened Maps
  import opened Sequences

  import System = BetreeSystem
  import View = StatesViewPivotBetree

  import opened PivotBetreeSpec`Spec
  import opened ViewOp
  import opened DiskLayout
  import BC = BlockCache
  import BCS = BlockSystem
  import BT = PivotBetree
  import BI = PivotBetreeBlockInterface
  import Ref = BlockSystem_Refines_StatesView
  import D = BlockDisk

  import M = BetreeCache

  function I(s: System.Variables) : View.Variables
  requires System.Inv(s)
  {
    View.Variables(
      System.BetreeDisk(s),
      BCS.PersistentLoc(s),
      BCS.FrozenLoc(s),
      System.FrozenBetree(s),
      System.EphemeralBetree(s)
    )
  }

  // Proofs

  lemma RefinesInit(s: System.Variables, loc: Location)
    requires System.Init(s, loc)
    ensures System.Inv(s)
    ensures View.Init(I(s), loc)
  {
    BCS.InitImpliesInv(s, loc);
    BT.InitImpliesInv(System.BetreeDisk(s)[loc]);
    BCS.InitGraphs(s, loc);
  }

  lemma BetreeMoveStepRefines(s: System.Variables, s': System.Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
    requires System.Inv(s)
    requires M.BetreeMove(s.machine, s'.machine, dop, vop, betreeStep)
    requires D.Next(s.disk, s'.disk, dop)
    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop)
  {
    var transactionStep := BC.TransactionStep(BetreeStepOps(betreeStep));
    Ref.StepGraphs(s, s', vop, BCS.MachineStep(dop, transactionStep));
    Ref.RefinesReads(s, BetreeStepReads(betreeStep));
    assert BT.NextStep(System.EphemeralBetree(s).value, System.EphemeralBetree(s').value, vop.uiop, BT.BetreeStep(betreeStep));
    BT.NextPreservesInv(System.EphemeralBetree(s).value, System.EphemeralBetree(s').value, vop.uiop);
    assert View.NextStep(I(s), I(s'), vop, View.AdvanceStep);
  }

  lemma BlockCacheMoveStepRefines(s: System.Variables, s': System.Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
    requires System.Inv(s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(s.machine, s'.machine, dop, vop, step)
    requires D.Next(s.disk, s'.disk, dop)
    requires (vop.SendPersistentLocOp? ==>
      BCS.Inv(s) ==>
        && vop.loc in Ref.DiskGraphMap(s)
        && BT.Inv(BT.Variables(BI.Variables(Ref.DiskGraphMap(s)[vop.loc])))
    )

    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop)
  {
    Ref.StepGraphs(s, s', vop, BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(EphemeralBetree(s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(s, s', dop, vop, step.ref);
      /*assert step.ref in EphemeralBetree(s).bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(EphemeralBetree(s).bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(s).bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(s).bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(s).bcv.view, iset{step.ref});*/
      assert BT.GC(System.EphemeralBetree(s).value, System.EphemeralBetree(s').value, UI.NoOp, iset{step.ref});
      BT.GCStepRefines(System.EphemeralBetree(s).value, System.EphemeralBetree(s').value, UI.NoOp, iset{step.ref});

      assert BT.NextStep(I(s).ephemeralState.value, I(s').ephemeralState.value, UI.NoOp, BT.GCStep(iset{step.ref}));

      assert View.Advance(I(s), I(s'), vop);
      assert View.NextStep(I(s), I(s'), vop, View.AdvanceStep);
    } else {
      if vop.FreezeOp? {
        assert View.NextStep(I(s), I(s'), vop, View.FreezeStep);
      }
      else if vop.CrashOp? {
        assert View.NextStep(I(s), I(s'), vop, View.CrashStep);
      }
      else if vop.SendPersistentLocOp? {
        assert View.ObtainPersistentLoc(I(s), I(s'), vop);
        assert View.NextStep(I(s), I(s'), vop, View.ObtainPersistentLocStep);
      }
      else if vop.SendFrozenLocOp? {
        assert View.NextStep(I(s), I(s'), vop, View.ProvideFrozenLocStep);
      }
      else if vop.CleanUpOp? {
        assert View.NextStep(I(s), I(s'), vop, View.ForgetOldStep);
      }
      else if vop.AdvanceOp? {
        assert false;
      }
      else if vop.StatesInternalOp? {
        if Ref.UpdateAllEq(s, s') {
          assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
        }
        else if Ref.UpdateDiskChange(s, s') {
          assert View.NextStep(I(s), I(s'), vop, View.DiskChangeStep);
        }
        else if Ref.UpdateUnalloc(s, s', BCS.MachineStep(dop, step)) {
          assert false;
        }
        else {
        }
      }
      else if vop.JournalInternalOp? {
        assert Ref.UpdateAllEq(s, s');
        assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
      }
      else if vop.PushSyncOp? {
        assert Ref.UpdateAllEq(s, s');
        assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
      }
      else if vop.PopSyncOp? {
        assert Ref.UpdateAllEq(s, s');
        assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
      }
      else {
        assert false;
      }
    }
  }

  lemma CrashStepRefines(s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(s)
    requires System.Crash(s, s', vop)
    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop)
  {
    Ref.StepGraphs(s, s', vop, BCS.CrashStep);
    assert View.NextStep(I(s), I(s'), vop, View.CrashStep);
  }

  lemma NextStepRefines(s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
    requires System.Inv(s)
    requires System.NextStep(s, s', vop, step)
    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop)
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(s.machine, s'.machine, dop, vop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepRefines(s, s', dop, vop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepRefines(s, s', dop, vop, blockCacheStep);
        }
      }
      case CrashStep => CrashStepRefines(s, s', vop);
    }
  }

  lemma RefinesNext(s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(s)
    requires System.Next(s, s', vop)
    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop);
  {
    var step :| System.NextStep(s, s', vop, step);
    NextStepRefines(s, s', vop, step);
  }
}
