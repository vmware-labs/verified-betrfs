include "../MapSpec/UIStateMachine.s.dfy"
include "../lib/Base/Maps.s.dfy"
//
// Our definition of crash-safety.
//

abstract module FullVersioned {
  import SM : UIStateMachine

  import opened Maps
  import UI

  type Version = int
  type SyncReqId = int

  datatype Constants = Constants(k: SM.Constants)
  datatype Variables = Variables(
      ghost version: Version,
      states: seq<SM.Variables>,
      ghost syncReqs: map<SyncReqId, Version>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && s.version == 0
    && |s.states| == 1
    && SM.Init(k.k, s.states[0])
    && s.syncReqs == map[]
  }

  datatype Step =
    | CrashStep
    | AdvanceStep
    | PersistStep
    | PushSyncStep(ghost id: SyncReqId)
    | PopSyncStep(ghost id: SyncReqId)
    | StutterStep

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.CrashOp?
    && s'.version == 0
    && |s.states| > 0
    && s'.states == [s.states[0]]
    && s'.syncReqs == map[]
  }

  predicate Advance(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && |s'.states| == |s.states| + 1
    && |s.states| > 0
    && s.states == s'.states[.. |s.states|]
    && SM.Next(k.k,
        s'.states[|s'.states| - 2],
        s'.states[|s'.states| - 1],
        uiop)
    && s'.version == s.version
    && s'.syncReqs == s.syncReqs
  }

  predicate Persist(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s.version <= s'.version <= s.version + |s.states| - 1
    && s'.states == s.states[s'.version - s.version ..]
    && s'.syncReqs == s.syncReqs
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: SyncReqId)
  {
    && uiop == UI.PushSyncOp(id)
    && id !in s.syncReqs
    && s'.version == s.version
    && s'.states == s.states
    && s'.syncReqs ==
        s.syncReqs[id := s.version + |s.states| - 1]
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, id: SyncReqId)
  {
    && uiop == UI.PopSyncOp(id)
    && id in s.syncReqs
    && s.syncReqs[id] <= s.version
    && s'.version == s.version
    && s'.states == s.states
    && s'.syncReqs == MapRemove1(s.syncReqs, id)
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp)
  {
    && uiop.NoOp?
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp, step: Step)
  {
    match step {
      case CrashStep => Crash(k, s, s', uiop)
      case AdvanceStep => Advance(k, s, s', uiop)
      case PersistStep => Persist(k, s, s', uiop)
      case PushSyncStep(id) => PushSync(k, s, s', uiop, id)
      case PopSyncStep(id) => PopSync(k, s, s', uiop, id)
      case StutterStep => Stutter(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: SM.UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }
}
