include "../MapSpec/UIStateMachine.s.dfy"
include "../MapSpec/Journal.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "VOp.i.dfy"
include "../MapSpec/ThreeStateVersioned.s.dfy"

module JournalView {
  import UI
  import opened Options
  import opened ViewOp
  import opened Journal
  import opened Maps
  import opened ThreeStateTypes

  type SyncReqId = int

  // s1 -------> t1
  //       j1
  //
  //                   s2 -------> t2
  //                         j2
  //
  //                                      s3 -------> t3
  //                                            j3
  //
  //   -------------------------->  ---------------->
  //              gamma                   delta

  datatype Constants = Constants
  datatype Variables = Variables(
      j1: seq<JournalEntry>,
      j2: seq<JournalEntry>,
      j3: seq<JournalEntry>,
      j_gamma: seq<JournalEntry>,
      j_delta: seq<JournalEntry>,

      persistentLoc: Loc,
      frozenLoc: Option<Loc>,

      ghost syncReqs: map<SyncReqId, SyncReqStatus>
  )

  predicate Init(k: Constants, s: Variables, loc: Loc)
  {
    && s.j1 == []
    && s.j2 == []
    && s.j3 == []
    && s.j_gamma == []
    && s.j_delta == []

    && s.persistentLoc == loc
    && s.frozenLoc == None

    && s.syncReqs == map[]
  }

  datatype Step =
    | PresentPersistentLocStep
    | ObtainFrozenLocStep
    | CleanUpStep

    | CrashStep
    | Move1to2Step
    | Move2to3Step
    | ExtendLog1Step
    | ExtendLog2Step
    | Move3Step
    | ReplayStep

    | PushSyncStep
    | PopSyncStep
    | StutterStep

  predicate PresentPersistentLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendPersistentLocOp?
    && vop.loc == s.persistentLoc

    && s' == s
  }

  predicate ObtainFrozenLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendFrozenLocOp?

    && s' == s.(frozenLoc := Some(vop.loc))
  }

  predicate CleanUp(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CleanUpOp?
    && s.frozenLoc == Some(s.persistentLoc)
    && s' == s.(frozenLoc := None)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?

    && s'.j1 == s.j1
    && s'.j2 == s.j1
    && s'.j3 == s.j1
    && s'.j_gamma == s.j1
    && s'.j_delta == []
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenLoc == None
    && s'.syncReqs == map[]
  }

  predicate Move1to2(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.JournalInternalOp?
    && s.frozenLoc.Some?
    && s' == Variables(
      s.j2,
      s.j2,
      s.j3,
      s.j2,
      s.j_delta,
      s.frozenLoc.value,
      s.frozenLoc,
      SyncReqs2to1(s.syncReqs))
  }

  predicate Move2to3(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.FreezeOp?
    && s.frozenLoc != Some(s.persistentLoc)
    && s' == Variables(
      s.j1,
      s.j3,
      s.j3,
      s.j_gamma + s.j_delta,
      [],
      s.persistentLoc,
      None,
      SyncReqs3to2(s.syncReqs))
  }

  predicate ExtendLog1(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.JournalInternalOp?
    && s' == Variables(
      s.j_gamma,
      s.j2,
      s.j3,
      s.j_gamma,
      s.j_delta,
      s.persistentLoc,
      s.frozenLoc,
      SyncReqs2to1(s.syncReqs))
  }

  predicate ExtendLog2(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.JournalInternalOp?
    && s' == Variables(
      s.j1,
      s.j2 + s.j_delta,
      s.j3,
      s.j_gamma + s.j_delta,
      [],
      s.persistentLoc,
      s.frozenLoc,
      SyncReqs3to2(s.syncReqs))
  }

  predicate Move3(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?
    && !vop.replay
    && var new_je := JournalEntriesForUIOp(vop.uiop);
    && s.j3 == []
    && s' == Variables(
      s.j1,
      s.j2,
      s.j3,
      s.j_gamma,
      s.j_delta + new_je,
      s.persistentLoc,
      s.frozenLoc,
      s.syncReqs)
  }

  predicate Replay(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?
    && vop.replay
    && s.j3 == JournalEntriesForUIOp(vop.uiop) + s'.j3
    && s' == Variables(
      s.j1,
      s.j2,
      s'.j3,
      s.j_gamma,
      s.j_delta,
      s.persistentLoc,
      s.frozenLoc,
      s.syncReqs)
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.PushSyncOp?

    && vop.id !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[vop.id := State3])
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.PopSyncOp?

    && vop.id in s.syncReqs
    && s.syncReqs[vop.id] == State1
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, vop.id))
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.StatesInternalOp?)
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case PresentPersistentLocStep => PresentPersistentLoc(k, s, s', vop)
      case ObtainFrozenLocStep => ObtainFrozenLoc(k, s, s', vop)
      case CleanUpStep => CleanUp(k, s, s', vop)
      case CrashStep => Crash(k, s, s', vop)
      case Move1to2Step => Move1to2(k, s, s', vop)
      case Move2to3Step => Move2to3(k, s, s', vop)
      case ExtendLog1Step => ExtendLog1(k, s, s', vop)
      case ExtendLog2Step => ExtendLog2(k, s, s', vop)
      case Move3Step => Move3(k, s, s', vop)
      case ReplayStep => Replay(k, s, s', vop)
      case PushSyncStep => PushSync(k, s, s', vop)
      case PopSyncStep => PopSync(k, s, s', vop)
      case StutterStep => Stutter(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }
}
