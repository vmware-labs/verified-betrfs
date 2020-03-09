include "../MapSpec/MapSpec.s.dfy"
include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../MapSpec/ThreeStateVersioned.s.dfy"
include "Journal.i.dfy"

abstract module TSJ {
  import SM : UIStateMachine

  import opened Maps
  import UI
  import opened ThreeStateTypes
  import opened Journal

  datatype Constants = Constants(k: SM.Constants)

  // s1 -------> S1 
  //       j1
  //
  //                   s2 -------> S2
  //                         j2
  //
  //                                      s3 -------> S3
  //                                            j3
  //
  //   -------------------------->  ---------------->
  //              gamma                   delta

  datatype Variables = Variables(
      s1: SM.Variables,
      s2: SM.Variables,
      s3: SM.Variables,
      j1: seq<JournalEntry>,
      j2: seq<JournalEntry>,
      j3: seq<JournalEntry>,
      j_gamma: seq<JournalEntry>,
      j_delta: seq<JournalEntry>,
      ghost outstandingSyncReqs: map<int, SyncReqStatus>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && SM.Init(k.k, s.s1)
    && s.s2 == s.s1
    && s.s3 == s.s1
    && s.j1 == []
    && s.j2 == []
    && s.j3 == []
    && s.j_gamma == []
    && s.j_delta == []
    && s.outstandingSyncReqs == map[]
  }

  datatype Step =
    | CrashStep
    | Move1to2Step
    | Move2to3Step
    | ExtendLog1Step
    | Move3Step
    | ReplayStep(replayedUIOp: SM.UIOp)
    | PushSyncStep(ghost id: int)
    | PopSyncStep(ghost id: int)

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.CrashOp?
    && s' == Variables(
      s.s1,
      s.s1,
      s.s1,
      s.j1,
      s.j1,
      s.j1,
      s.j1,
      [],
      map[])
  }

  predicate Move1to2(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s2,
      s.s2,
      s.s3,
      s.j2,
      s.j2,
      s.j3,
      s.j2,
      s.j_delta,
      SyncReqs2to1(s.outstandingSyncReqs))
  }

  predicate Move2to3(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s1,
      s.s3,
      s.s3,
      s.j1,
      s.j3,
      s.j3,
      s.j_gamma + s.j_delta,
      [],
      SyncReqs3to2(s.outstandingSyncReqs))
  }

  predicate ExtendLog1(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == Variables(
      s.s1,
      s.s2,
      s.s3,
      s.j1,
      s.j_gamma,
      s.j3,
      s.j_gamma,
      s.j_delta,
      SyncReqs3to2(s.outstandingSyncReqs))
  }

  predicate Move3(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && SM.Next(k.k, s.s3, s'.s3, uiop)
    && var new_je := JournalEntriesForUIOp(uiop);
    && s' == Variables(
      s.s1,
      s.s2,
      s'.s3,
      s.j1,
      s.j2,
      s.j3 + new_je,
      s.j_gamma,
      s.j_delta + new_je,
      s.outstandingSyncReqs)
  }

  predicate Replay(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, replayedUIOp: SM.UIOp)
  {
    && uiop.NoOp?
    && SM.Next(k.k, s.s3, s'.s3, replayedUIOp)
    && s.j3 == JournalEntriesForUIOp(replayedUIOp) + s'.j3
    && s' == Variables(
      s.s1,
      s.s2,
      s'.s3,
      s.j1,
      s.j2,
      s'.j3,
      s.j_gamma,
      s.j_delta,
      s.outstandingSyncReqs)
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PushSyncOp(id)
    && id !in s.outstandingSyncReqs
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, s.outstandingSyncReqs[id := State3])
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: int)
  {
    && uiop == UI.PopSyncOp(id)
    && id in s.outstandingSyncReqs
    && s.outstandingSyncReqs[id] == State1
    && s' == Variables(s.s1, s.s2, s.s3, s.j1, s.j2, s.j3, s.j_gamma, s.j_delta, MapRemove1(s.outstandingSyncReqs, id))
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, step: Step)
  {
    match step {
      case CrashStep => Crash(k, s, s', uiop)
      case Move1to2Step => Move1to2(k, s, s', uiop)
      case Move2to3Step => Move2to3(k, s, s', uiop)
      case ExtendLog1Step => ExtendLog1(k, s, s', uiop)
      case Move3Step => Move3(k, s, s', uiop)
      case ReplayStep(replayedUIOp) => Replay(k, s, s', uiop, replayedUIOp)
      case PushSyncStep(id) => PushSync(k, s, s', uiop, id)
      case PopSyncStep(id) => PopSync(k, s, s', uiop, id)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }
}
