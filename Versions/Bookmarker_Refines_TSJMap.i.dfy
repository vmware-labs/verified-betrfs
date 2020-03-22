include "Bookmarker.i.dfy"
include "../MapSpec/TSJMap.i.dfy"

module Bookmarker_Refines_TSJMap {
  import Bookmarker
  import TriStateMap
  import TSJ = TSJMap
  import opened Options
  import opened Sequences
  import opened Journal
  import opened VersionOp
  import MapSpec
  import JournalChain

  function Ik(k: Bookmarker.Constants) : TSJ.Constants
  {
    TSJ.Constants(k.tsm.k)
  }

  function I(k: Bookmarker.Constants, s: Bookmarker.Variables) : TSJ.Variables
  requires Bookmarker.Inv(k, s)
  {
    TSJ.Variables(
      Bookmarker.s1(s),
      Bookmarker.s2(s),
      Bookmarker.s3(s),
      s.jc.j1,
      s.jc.j2,
      s.jc.j3,
      s.jc.j_gamma,
      s.jc.j_delta,
      s.jc.syncReqs
    )
  }

  lemma RefinesInit(k: Bookmarker.Constants, s: Bookmarker.Variables)
    requires Bookmarker.Init(k, s)
    ensures TSJ.Init(Ik(k), I(k, s))
  {
  }

  lemma SendPersistentLocRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.SendPersistentLocOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma AdvanceRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.AdvanceOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    if JournalChain.Move3(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move3Step);
    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(vop.uiop));
    }
  }

  lemma CrashRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.CrashOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.CrashStep);
  }

  lemma FreezeRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.FreezeOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move2to3Step);
  }

  lemma TristateInternalRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.TristateInternalOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma JournalInternalRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.JournalInternalOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    if JournalChain.Move1to2(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move1to2Step);
    }
    else if JournalChain.ExtendLog1(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog1Step);
    }
    else if JournalChain.ExtendLog2(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog2Step);
    }
    else if JournalChain.Stutter(k.jc, s.jc, s'.jc, vop) {
      assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
    }
  }

  lemma SendFrozenLocRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.SendFrozenLocOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma CleanUpRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.CleanUpOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.StutterStep);
  }

  lemma PushSyncRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.PushSyncOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PushSyncStep(vop.id));
  }

  lemma PopSyncRefines(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    requires vop.PopSyncOp?
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.PopSyncStep(vop.id));
  }

  lemma RefinesNextStep(k: Bookmarker.Constants, s: Bookmarker.Variables, s':Bookmarker.Variables, uiop: UI.Op, vop: VOp)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Inv(k, s')
    requires Bookmarker.NextStep(k, s, s', vop, uiop)
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match vop {
      case SendPersistentLocOp(loc) => { SendPersistentLocRefines(k, s, s', uiop, vop); }
      case AdvanceOp(_, replay) => { AdvanceRefines(k, s, s', uiop, vop); }
      case CrashOp => { CrashRefines(k, s, s', uiop, vop); }
      case FreezeOp => { FreezeRefines(k, s, s', uiop, vop); }
      case TristateInternalOp => { TristateInternalRefines(k, s, s', uiop, vop); }
      case JournalInternalOp => { JournalInternalRefines(k, s, s', uiop, vop); }
      case SendFrozenLocOp(loc) => { SendFrozenLocRefines(k, s, s', uiop, vop); }
      case CleanUpOp => { CleanUpRefines(k, s, s', uiop, vop); }
      case PushSyncOp(id) => { PushSyncRefines(k, s, s', uiop, vop); }
      case PopSyncOp(id) => { PopSyncRefines(k, s, s', uiop, vop); }
    }
  }

  lemma RefinesNext(k: Bookmarker.Constants, s: Bookmarker.Variables, s': Bookmarker.Variables, uiop: UI.Op)
    requires Bookmarker.Inv(k, s)
    requires Bookmarker.Next(k, s, s', uiop)
    ensures Bookmarker.Inv(k, s')
    ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var vop :| Bookmarker.NextStep(k, s, s', vop, uiop);
    RefinesNextStep(k, s, s', uiop, vop);
  }
}
