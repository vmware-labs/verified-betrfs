// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "JournalSystem.i.dfy"
include "../Versions/JournalView.i.dfy"

module JournalSystem_Refines_JournalView {
  import System = JournalSystem
  import View = JournalView
  import opened DiskLayout
  import opened ViewOp

  function I(s: System.Variables) : View.Variables
  requires System.Inv(s)
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

  lemma RefinesInit(s: System.Variables, loc: Location)
    requires System.Init(s, loc)
    ensures System.Inv(s)
    ensures View.Init(I(s), loc)
  {
    System.InitJournals(s, loc);
    System.InitImpliesInv(s, loc);
  }

  lemma RefinesNextStep(s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
    requires System.Inv(s)
    requires System.NextStep(s, s', vop, step)
    requires System.Inv(s')
    ensures View.Next(I(s), I(s'), vop);
  {
    assert System.M.Inv(s.machine);
    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackJournalReqStep(jr) => {
            System.WriteBackJournalReqStepPreservesJournals(s, s', dop, vop, jr);
            if !(s.machine.Ready? && s.machine.inMemoryJournalFrozen == []) {
              assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
            } else {
              assert View.ExtendLog2(I(s), I(s'), vop);
              assert View.NextStep(I(s), I(s'), vop, View.ExtendLog2Step);
            }
          }
          case WriteBackJournalRespStep => {
            System.WriteBackJournalRespStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockReq_AdvanceLog_Step => {
            System.WriteBackSuperblockReq_AdvanceLog_StepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockReq_AdvanceLocation_Step => {
            System.WriteBackSuperblockReq_AdvanceLocation_StepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case WriteBackSuperblockRespStep => {
            System.WriteBackSuperblockRespStepPreservesJournals(s, s', dop, vop);
            if vop.CleanUpOp? {
              assert View.CleanUp(I(s), I(s'), vop);
              assert View.NextStep(I(s), I(s'), vop, View.CleanUpStep);
            } else {
              assert vop.JournalInternalOp?;
              assert I(s) == I(s');
              assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
            }
          }
          case PageInJournalReqStep(which) => {
            System.PageInJournalReqStepPreservesJournals(s, s', dop, vop, which);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case PageInJournalRespStep(which) => {
            System.PageInJournalRespStepPreservesJournals(s, s', dop, vop, which);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case PageInSuperblockReqStep(which) => {
            System.PageInSuperblockReqStepPreservesJournals(s, s', dop, vop, which);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case PageInSuperblockRespStep(which) => {
            System.PageInSuperblockRespStepPreservesJournals(s, s', dop, vop, which);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case FinishLoadingSuperblockPhaseStep => {
            System.FinishLoadingSuperblockPhaseStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.PresentPersistentLocStep);
          }
          case FinishLoadingOtherPhaseStep => {
            System.FinishLoadingOtherPhaseStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
          case FreezeStep => {
            System.FreezeStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.Move2to3Step);
          }
          case ReceiveFrozenLocStep => {
            System.ReceiveFrozenLocStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.ObtainFrozenLocStep);
          }
          case AdvanceStep => {
            System.AdvanceStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.Move3Step);
          }
          case ReplayStep => {
            System.ReplayStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.ReplayStep);
          }
          case PushSyncReqStep(id) => {
            System.PushSyncReqStepPreservesJournals(s, s', dop, vop, id);
            assert View.PushSync(I(s), I(s'), vop);
            assert View.NextStep(I(s), I(s'), vop, View.PushSyncStep);
          }
          case PopSyncReqStep(id) => {
            System.PopSyncReqStepPreservesJournals(s, s', dop, vop, id);
            assert View.NextStep(I(s), I(s'), vop, View.PopSyncStep);
          }
          case NoOpStep => {
            System.NoOpStepPreservesJournals(s, s', dop, vop);
            assert View.NextStep(I(s), I(s'), vop, View.StutterStep);
          }
        }
      }
      case DiskInternalStep(step) => {
        match step {
          case ProcessWriteSuperblockStep(which) => {
            System.ProcessWriteSuperblockPreservesJournals(s, s', vop, which);
            if System.ProcessWriteIsGraphUpdate(s) {
              assert View.Move1to2(I(s), I(s'), vop);
              assert View.NextStep(I(s), I(s'), vop, View.Move1to2Step);
            } else {
              assert View.ExtendLog1(I(s), I(s'), vop);
              assert View.NextStep(I(s), I(s'), vop, View.ExtendLog1Step);
            }
          }
        }
      }
      case CrashStep => {
        System.CrashPreservesJournals(s, s', vop);
        assert View.Crash(I(s), I(s'), vop);
        assert View.NextStep(I(s), I(s'), vop, View.CrashStep);
      }
    }
  }

  lemma RefinesNext(s: System.Variables, s': System.Variables, vop: VOp)
    requires System.Inv(s)
    requires System.Next(s, s', vop)
    ensures System.Inv(s')
    ensures View.Next(I(s), I(s'), vop);
  {
    System.NextPreservesInv(s, s', vop);
    var step :| System.NextStep(s, s', vop, step);
    RefinesNextStep(s, s', vop, step);
  }
}
