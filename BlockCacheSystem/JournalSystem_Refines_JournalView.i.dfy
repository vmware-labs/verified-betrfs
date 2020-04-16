include "JournalSystem.i.dfy"
include "../Versions/JournalView.i.dfy"

module JournalSystem_Refines_JournalView {
  import System = JournalSystem
  import View = JournalView
  import opened DiskLayout
  import opened ViewOp

  function Ik(k: System.Constants) : View.Constants
  {
    View.Constants
  }

  function I(k: System.Constants, s: System.Variables) : View.Variables
  requires System.Inv(k, s)
  {
    View.Variables(
        System.PersistentJournal(s),
        System.FrozenJournal(s),
        System.EphemeralJournal(s),
        System.GammaJournal(s),
        System.DeltaJournal(s),
        System.PersistentLoc(s),
        System.FrozenLoc(s),
        System.SyncReqs(s))
  }

  lemma RefinesInit(k: System.Constants, s: System.Variables, loc: Location)
    requires System.Init(k, s, loc)
    ensures System.Inv(k, s)
    ensures View.Init(Ik(k), I(k, s), loc)
  {
    System.InitJournals(k, s, loc);
    System.InitImpliesInv(k, s, loc);
  }

  lemma RefinesNextStep(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
    requires System.Inv(k, s)
    requires System.NextStep(k, s, s', vop, step)
    requires System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop);
  {
    assert System.M.Inv(k.machine, s.machine);
    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackJournalReqStep(jr) => {
            System.WriteBackJournalReqStepPreservesJournals(k, s, s', dop, vop, jr);
            if !(s.machine.Ready? && s.machine.inMemoryJournalFrozen == []) {
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
            } else {
              assert View.ExtendLog2(Ik(k), I(k, s), I(k, s'), vop);
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ExtendLog2Step);
            }
          }
          case WriteBackJournalRespStep => {
            System.WriteBackJournalRespStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockReq_AdvanceLog_Step => {
            System.WriteBackSuperblockReq_AdvanceLog_StepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockReq_AdvanceLocation_Step => {
            System.WriteBackSuperblockReq_AdvanceLocation_StepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockRespStep => {
            System.WriteBackSuperblockRespStepPreservesJournals(k, s, s', dop, vop);
            if vop.CleanUpOp? {
              assert View.CleanUp(Ik(k), I(k, s), I(k, s'), vop);
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.CleanUpStep);
            } else {
              assert vop.JournalInternalOp?;
              assert I(k, s) == I(k, s');
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
            }
          }
          case PageInJournalReqStep(which) => {
            System.PageInJournalReqStepPreservesJournals(k, s, s', dop, vop, which);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case PageInJournalRespStep(which) => {
            System.PageInJournalRespStepPreservesJournals(k, s, s', dop, vop, which);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case PageInSuperblockReqStep(which) => {
            System.PageInSuperblockReqStepPreservesJournals(k, s, s', dop, vop, which);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case PageInSuperblockRespStep(which) => {
            System.PageInSuperblockRespStepPreservesJournals(k, s, s', dop, vop, which);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case FinishLoadingSuperblockPhaseStep => {
            System.FinishLoadingSuperblockPhaseStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.PresentPersistentLocStep);
          }
          case FinishLoadingOtherPhaseStep => {
            System.FinishLoadingOtherPhaseStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
          case FreezeStep => {
            System.FreezeStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.Move2to3Step);
          }
          case ReceiveFrozenLocStep => {
            System.ReceiveFrozenLocStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ObtainFrozenLocStep);
          }
          case AdvanceStep => {
            System.AdvanceStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.Move3Step);
          }
          case ReplayStep => {
            System.ReplayStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ReplayStep);
          }
          case PushSyncReqStep(id) => {
            System.PushSyncReqStepPreservesJournals(k, s, s', dop, vop, id);
            assert View.PushSync(Ik(k), I(k, s), I(k, s'), vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.PushSyncStep);
          }
          case PopSyncReqStep(id) => {
            System.PopSyncReqStepPreservesJournals(k, s, s', dop, vop, id);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.PopSyncStep);
          }
          case NoOpStep => {
            System.NoOpStepPreservesJournals(k, s, s', dop, vop);
            assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.StutterStep);
          }
        }
      }
      case DiskInternalStep(step) => {
        match step {
          case ProcessWriteSuperblockStep(which) => {
            System.ProcessWriteSuperblockPreservesJournals(k, s, s', vop, which);
            if System.ProcessWriteIsGraphUpdate(k, s) {
              assert View.Move1to2(Ik(k), I(k, s), I(k, s'), vop);
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.Move1to2Step);
            } else {
              assert View.ExtendLog1(Ik(k), I(k, s), I(k, s'), vop);
              assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.ExtendLog1Step);
            }
          }
        }
      }
      case CrashStep => {
        System.CrashPreservesJournals(k, s, s', vop);
        assert View.Crash(Ik(k), I(k, s), I(k, s'), vop);
        assert View.NextStep(Ik(k), I(k, s), I(k, s'), vop, View.CrashStep);
      }
    }
  }

  lemma RefinesNext(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(k, s)
    requires System.Next(k, s, s', vop)
    ensures System.Inv(k, s')
    ensures View.Next(Ik(k), I(k, s), I(k, s'), vop);
  {
    System.NextPreservesInv(k, s, s', vop);
    var step :| System.NextStep(k, s, s', vop, step);
    RefinesNextStep(k, s, s', vop, step);
  }
}
