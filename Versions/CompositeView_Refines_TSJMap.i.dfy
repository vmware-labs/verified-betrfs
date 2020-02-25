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

  function Ik(k: CompositeView.Constants) : TSJ.Constants
  {
    TSJ.Constants(k.tsm.k)
  }

  function I(k: CompositeView.Constants, s: CompositeView.Variables) : TSJ.Variables
  requires CompositeView.Inv(k, s)
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

  lemma RefinesInit(k: CompositeView.Constants, s: CompositeView.Variables)
    requires CompositeView.Init(k, s)
    ensures CompositeView.Inv(k, s)
    ensures TSJ.Init(Ik(k), I(k, s))
  {
    CompositeView.InitImpliesInv(k, s);
  }

  lemma SendPersistentLocRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.SendPersistentLocOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma AdvanceRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.AdvanceOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    if JournalView.Move3(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move3Step);
    } else if JournalView.Replay(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(vop.uiop));
    }
  }

  lemma CrashRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.CrashOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.CrashStep);
  }

  lemma FreezeRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.FreezeOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move2to3Step);
  }

  lemma StatesInternalRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.StatesInternalOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma JournalInternalRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.JournalInternalOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    if JournalView.Move1to2(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move1to2Step);
    }
    else if JournalView.ExtendLog1(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog1Step);
    }
    else if JournalView.ExtendLog2(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog2Step);
    }
    else if JournalView.Stutter(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
    }
  }

  lemma SendFrozenLocRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.SendFrozenLocOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma CleanUpRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.CleanUpOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma PushSyncRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.PushSyncOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PushSyncStep(vop.id));
  }

  lemma PopSyncRefines(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    requires vop.PopSyncOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PopSyncStep(vop.id));
  }

  lemma RefinesNextStep(k: CompositeView.Constants, s: CompositeView.Variables, s':CompositeView.Variables, uiop: UI.Op, vop: VOp)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Inv(k, s')
    requires CompositeView.NextStep(k, s, s', vop, uiop)
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match vop {
      case SendPersistentLocOp(loc) => { SendPersistentLocRefines(k, s, s', uiop, vop); }
      case AdvanceOp(_, replay) => { AdvanceRefines(k, s, s', uiop, vop); }
      case CrashOp => { CrashRefines(k, s, s', uiop, vop); }
      case FreezeOp => { FreezeRefines(k, s, s', uiop, vop); }
      case StatesInternalOp => { StatesInternalRefines(k, s, s', uiop, vop); }
      case JournalInternalOp => { JournalInternalRefines(k, s, s', uiop, vop); }
      case SendFrozenLocOp(loc) => { SendFrozenLocRefines(k, s, s', uiop, vop); }
      case CleanUpOp => { CleanUpRefines(k, s, s', uiop, vop); }
      case PushSyncOp(id) => { PushSyncRefines(k, s, s', uiop, vop); }
      case PopSyncOp(id) => { PopSyncRefines(k, s, s', uiop, vop); }
    }
  }

  lemma RefinesNext(k: CompositeView.Constants, s: CompositeView.Variables, s': CompositeView.Variables, uiop: UI.Op)
    requires CompositeView.Inv(k, s)
    requires CompositeView.Next(k, s, s', uiop)
    ensures CompositeView.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    CompositeView.NextPreservesInv(k, s, s', uiop);
    var vop :| CompositeView.NextStep(k, s, s', vop, uiop);
    RefinesNextStep(k, s, s', uiop, vop);
  }
}
