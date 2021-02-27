// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "CompositeView.i.dfy"
include "../MapSpec/TSJMap.i.dfy"

module CompositeView_Refines_TSJMap {
  import CompositeView
  import StatesViewMap
  import TSJ = TSJMap
  import opened Options
  import opened Sequences
  import opened Journal
  import opened ViewOp
  import MapSpec
  import JournalView

  function I(s: CompositeView.Variables) : TSJ.Variables
  requires CompositeView.Inv(s)
  {
    TSJ.Variables(
      CompositeView.s1(s),
      CompositeView.s2(s),
      CompositeView.s3(s),
      s.jc.j1,
      s.jc.j2,
      s.jc.j3,
      s.jc.j_gamma,
      s.jc.j_delta,
      s.jc.syncReqs
    )
  }

  lemma RefinesInit(s: CompositeView.Variables)
    requires CompositeView.Init(s)
    ensures CompositeView.Inv(s)
    ensures TSJ.Init(I(s))
  {
    CompositeView.InitImpliesInv(s);
  }

  lemma SendPersistentLocRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.SendPersistentLocOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.StutterStep);
  }

  lemma AdvanceRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.AdvanceOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    if JournalView.Move3(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move3Step);
    } else if JournalView.Replay(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.ReplayStep(vop.uiop));
    }
  }

  lemma CrashRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.CrashOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.CrashStep);
  }

  lemma FreezeRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.FreezeOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move2to3Step);
  }

  lemma StatesInternalRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.StatesInternalOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.StutterStep);
  }

  lemma JournalInternalRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.JournalInternalOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    if JournalView.Move1to2(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move1to2Step);
    }
    else if JournalView.ExtendLog1(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.ExtendLog1Step);
    }
    else if JournalView.ExtendLog2(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.ExtendLog2Step);
    }
    else if JournalView.Stutter(s.jc, s'.jc, vop) {
      assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.StutterStep);
    }
  }

  lemma SendFrozenLocRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.SendFrozenLocOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.StutterStep);
  }

  lemma CleanUpRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.CleanUpOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.StutterStep);
  }

  lemma PushSyncRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.PushSyncOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.PushSyncStep(vop.id));
  }

  lemma PopSyncRefines(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    requires vop.PopSyncOp?
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.PopSyncStep(vop.id));
  }

  lemma RefinesNextStep(s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(s)
    requires CompositeView.Inv(s')
    requires CompositeView.NextStep(s, s', vop, uiop)
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    match vop {
      case SendPersistentLocOp(loc) => { SendPersistentLocRefines(s, s', uiop, vop); }
      case AdvanceOp(_, replay) => { AdvanceRefines(s, s', uiop, vop); }
      case CrashOp => { CrashRefines(s, s', uiop, vop); }
      case FreezeOp => { FreezeRefines(s, s', uiop, vop); }
      case StatesInternalOp => { StatesInternalRefines(s, s', uiop, vop); }
      case JournalInternalOp => { JournalInternalRefines(s, s', uiop, vop); }
      case SendFrozenLocOp(loc) => { SendFrozenLocRefines(s, s', uiop, vop); }
      case CleanUpOp => { CleanUpRefines(s, s', uiop, vop); }
      case PushSyncOp(id) => { PushSyncRefines(s, s', uiop, vop); }
      case PopSyncOp(id) => { PopSyncRefines(s, s', uiop, vop); }
    }
  }

  lemma RefinesNext(s: CompositeView.Variables, s': CompositeView.Variables, uiop: UI.Op)
    requires CompositeView.Inv(s)
    requires CompositeView.Next(s, s', uiop)
    ensures CompositeView.Inv(s')
    ensures TSJ.Next(I(s), I(s'), uiop)
  {
    CompositeView.NextPreservesInv(s, s', uiop);
    var vop :| CompositeView.NextStep(s, s', vop, uiop);
    RefinesNextStep(s, s', uiop, vop);
  }
}
