include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
include "../lib/Base/Maps.s.dfy"
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

  function Ik(k: System.Constants) : View.Constants
  {
    View.Constants(BT.Constants(BI.Constants()))
  }

  function I(k: System.Constants, s: System.Variables) : View.Variables
  requires System.Inv(k, s)
  {
    View.Variables(
      System.BetreeDisk(k, s),
      BCS.PersistentLoc(k, s),
      BCS.FrozenLoc(k, s),
      System.FrozenBetree(k, s),
      System.EphemeralBetree(k, s)
    )
  }

  // Proofs

  lemma RefinesInit(k: System.Constants, s: System.Variables, loc: Location)
    requires System.Init(k, s, loc)
    ensures System.Inv(k, s)
    ensures View.Init(Ik(k), I(k, s), loc)
  {
    BCS.InitImpliesInv(k, s, loc);
    BT.InitImpliesInv(Ik(k).k, System.BetreeDisk(k, s)[loc]);
    BCS.InitGraphs(k, s, loc);
  }

  lemma BetreeMoveStepRefines(k: System.Constants, s: System.Variables, s': System.Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
    requires System.Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, dop, vop, betreeStep)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    var transactionStep := BC.TransactionStep(BetreeStepOps(betreeStep));
    Ref.StepGraphs(k, s, s', vop, BCS.MachineStep(dop, transactionStep));
    Ref.RefinesReads(k, s, BetreeStepReads(betreeStep));
    assert BT.NextStep(Ik(k).k, System.EphemeralBetree(k, s).value, System.EphemeralBetree(k, s').value, vop.uiop, BT.BetreeStep(betreeStep));
    BT.NextPreservesInv(Ik(k).k, System.EphemeralBetree(k, s).value, System.EphemeralBetree(k, s').value, vop.uiop);
    assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.AdvanceStep);
  }

  lemma BlockCacheMoveStepRefines(k: System.Constants, s: System.Variables, s': System.Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
    requires System.Inv(k, s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, dop, vop, step)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    requires (vop.SendPersistentLocOp? ==>
      BCS.Inv(k, s) ==>
        && vop.loc in Ref.DiskGraphMap(k, s)
        && BT.Inv(Ik(k).k, BT.Variables(BI.Variables(Ref.DiskGraphMap(k, s)[vop.loc])))
    )

    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    Ref.StepGraphs(k, s, s', vop, BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(Ik(k).bck, EphemeralBetree(k, s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(k, s, s', dop, vop, step.ref);
      /*assert step.ref in EphemeralBetree(k, s).bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(Ik(k).bck, EphemeralBetree(k, s).bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(k, s).bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(k, s).bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(k, s).bcv.view, iset{step.ref});*/
      assert BT.GC(Ik(k).k, System.EphemeralBetree(k, s).value, System.EphemeralBetree(k, s').value, UI.NoOp, iset{step.ref});
      BT.GCStepRefines(Ik(k).k, System.EphemeralBetree(k, s).value, System.EphemeralBetree(k, s').value, UI.NoOp, iset{step.ref});

      assert BT.NextStep(Ik(k).k, I(k, s).ephemeralState.value, I(k, s').ephemeralState.value, UI.NoOp, BT.GCStep(iset{step.ref}));

      assert View.Advance(Ik(k), I(k, s), I(k, s'), vop);
      assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.AdvanceStep);
    } else {
      if vop.FreezeOp? {
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.FreezeStep);
      }
      else if vop.CrashOp? {
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.CrashStep);
      }
      else if vop.SendPersistentLocOp? {
        assert View.ObtainPersistentLoc(Ik(k), I(k, s), I(k, s'), vop);
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ObtainPersistentLocStep);
      }
      else if vop.SendFrozenLocOp? {
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ProvideFrozenLocStep);
      }
      else if vop.CleanUpOp? {
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ForgetOldStep);
      }
      else if vop.AdvanceOp? {
        assert false;
      }
      else if vop.StatesInternalOp? {
        if Ref.UpdateAllEq(k, s, s') {
          assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
        }
        else if Ref.UpdateDiskChange(k, s, s') {
          assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.DiskChangeStep);
        }
        else if Ref.UpdateUnalloc(k, s, s', BCS.MachineStep(dop, step)) {
          assert false;
        }
        else {
        }
      }
      else if vop.JournalInternalOp? {
        assert Ref.UpdateAllEq(k, s, s');
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
      }
      else if vop.PushSyncOp? {
        assert Ref.UpdateAllEq(k, s, s');
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
      }
      else if vop.PopSyncOp? {
        assert Ref.UpdateAllEq(k, s, s');
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
      }
      else {
        assert false;
      }
    }
  }

  lemma CrashStepRefines(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(k, s)
    requires System.Crash(k, s, s', vop)
    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    Ref.StepGraphs(k, s, s', vop, BCS.CrashStep);
    assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.CrashStep);
  }

  lemma NextStepRefines(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
    requires System.Inv(k, s)
    requires System.NextStep(k, s, s', vop, step)
    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(k.machine, s.machine, s'.machine, dop, vop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepRefines(k, s, s', dop, vop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepRefines(k, s, s', dop, vop, blockCacheStep);
        }
      }
      case CrashStep => CrashStepRefines(k, s, s', vop);
    }
  }

  lemma RefinesNext(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(k, s)
    requires System.Next(k, s, s', vop)
    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop);
  {
    var step :| System.NextStep(k, s, s', vop, step);
    NextStepRefines(k, s, s', vop, step);
  }
}
