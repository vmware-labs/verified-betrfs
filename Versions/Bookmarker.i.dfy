include "TristateMap.i.dfy"
include "JournalChain.i.dfy"

// Combine TriStateMap and JournalChain.

module Bookmarker {
  import TriStateMap
  import JournalChain
  import SM = MapSpec
  import opened VersionOp

  import UI

  datatype Constants = Constants(
      tsm: TriStateMap.Constants,
      jc: JournalChain.Constants)

  datatype Variables = Variables(
      tsm: TriStateMap.Variables,
      jc: JournalChain.Variables)

  datatype Step = Step(vop: VOp) 

  predicate Init(k: Constants, s: Variables)
  {
    && TriStateMap.Init(k.tsm, s.tsm)
    && JournalChain.Init(k.jc, s.jc)
  }

  predicate SendPersistentLoc(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && uiop.NoOp?
    && vop.SendPersistentLocOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate Advance(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.AdvanceOp?
    && (vop.replay ==> uiop.NoOp?)
    && (!vop.replay ==> vop.uiop == uiop)
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.CrashOp?
    && uiop.CrashOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate Freeze(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.FreezeOp?
    && uiop.CrashOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate TristateInternal(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.TristateInternalOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && s'.jc == s.jc
  }

  predicate JournalInternal(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.JournalInternalOp?
    && s'.tsm == s.tsm
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate SendFrozenLoc(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.SendFrozenLocOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate ForgetOld(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.ForgetOldOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.PushSyncOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && vop.PopSyncOp?
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && (vop.SendPersistentLocOp? ==> SendPersistentLoc(k, s, s', vop, uiop))
    && (vop.AdvanceOp? ==> Advance(k, s, s', vop, uiop))
    && (vop.CrashOp? ==> Crash(k, s, s', vop, uiop))
    && (vop.FreezeOp? ==> Freeze(k, s, s', vop, uiop))
    && (vop.TristateInternalOp? ==> TristateInternal(k, s, s', vop, uiop))
    && (vop.JournalInternalOp? ==> JournalInternal(k, s, s', vop, uiop))
    && (vop.SendFrozenLocOp? ==> SendFrozenLoc(k, s, s', vop, uiop))
    && (vop.ForgetOldOp? ==> ForgetOld(k, s, s', vop, uiop))
    && (vop.PushSyncOp? ==> PushSync(k, s, s', vop, uiop))
    && (vop.PopSyncOp? ==> PopSync(k, s, s', vop, uiop))
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  {
    exists step: Step :: NextStep(k, s, s', step.vop, uiop)
  }
}
