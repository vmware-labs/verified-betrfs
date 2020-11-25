include "../MapSpec/UIStateMachine.s.dfy"
include "../MapSpec/Journal.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Maps.i.dfy"
include "VOp.i.dfy"
include "../MapSpec/ThreeStateVersioned.s.dfy"

// Abstraction of the journal side of the system.

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

  predicate Init(s: Variables, loc: Loc)
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

  predicate PresentPersistentLoc(s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendPersistentLocOp?
    && vop.loc == s.persistentLoc

    && s' == s
  }

  predicate ObtainFrozenLoc(s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendFrozenLocOp?

    && s' == s.(frozenLoc := Some(vop.loc))
  }

  predicate CleanUp(s: Variables, s': Variables, vop: VOp)
  {
    && vop.CleanUpOp?
    && s.frozenLoc == Some(s.persistentLoc)
    && s' == s.(frozenLoc := None)
  }

  predicate Crash(s: Variables, s': Variables, vop: VOp)
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

  predicate Move1to2(s: Variables, s': Variables, vop: VOp)
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

  predicate Move2to3(s: Variables, s': Variables, vop: VOp)
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

  predicate ExtendLog1(s: Variables, s': Variables, vop: VOp)
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

  predicate ExtendLog2(s: Variables, s': Variables, vop: VOp)
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

  predicate Move3(s: Variables, s': Variables, vop: VOp)
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

  predicate Replay(s: Variables, s': Variables, vop: VOp)
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

  predicate PushSync(s: Variables, s': Variables, vop: VOp)
  {
    && vop.PushSyncOp?

    && vop.id !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[vop.id := State3])
  }

  predicate PopSync(s: Variables, s': Variables, vop: VOp)
  {
    && vop.PopSyncOp?

    && vop.id in s.syncReqs
    && s.syncReqs[vop.id] == State1
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, vop.id))
  }

  predicate Stutter(s: Variables, s': Variables, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.StatesInternalOp?)
    && s' == s
  }

  predicate NextStep(s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case PresentPersistentLocStep => PresentPersistentLoc(s, s', vop)
      case ObtainFrozenLocStep => ObtainFrozenLoc(s, s', vop)
      case CleanUpStep => CleanUp(s, s', vop)
      case CrashStep => Crash(s, s', vop)
      case Move1to2Step => Move1to2(s, s', vop)
      case Move2to3Step => Move2to3(s, s', vop)
      case ExtendLog1Step => ExtendLog1(s, s', vop)
      case ExtendLog2Step => ExtendLog2(s, s', vop)
      case Move3Step => Move3(s, s', vop)
      case ReplayStep => Replay(s, s', vop)
      case PushSyncStep => PushSync(s, s', vop)
      case PopSyncStep => PopSync(s, s', vop)
      case StutterStep => Stutter(s, s', vop)
    }
  }

  predicate Next(s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(s, s', vop, step)
  }
}
