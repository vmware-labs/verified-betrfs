include "../MapSpec/UIStateMachine.s.dfy"
include "../MapSpec/Journal.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "VOp.i.dfy"

module JournalChain {
  import UI
  import opened Options
  import opened VersionOp
  import opened Journal
  import opened Maps

  type Version = int
  type SyncReqId = int

  datatype Constants = Constants
  datatype Variables = Variables(
      startVersion: Version,
      journal: seq<JournalEntry>,

      persistentStateIndex: Version,
      persistentJournalIndex: Version,
      persistentLoc: Location,

      frozenStateIndex: Option<Version>,
      frozenLoc: Option<Location>,

      ephemeralStateIndex: int,

      syncReqs: map<SyncReqId, Version>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && s.startVersion == 0
    && s.journal == []
    && s.persistentStateIndex == 0
    && s.persistentJournalIndex == 0
    && s.persistentLoc == Loc1
    && s.frozenStateIndex == None
    && s.frozenLoc == None
    && s.ephemeralStateIndex == 0
    && s.syncReqs == map[]
  }

  datatype Step =
    | PresentPersistentLocStep
    | AdvanceEphemeralStep
    | ReplayStep
    | CrashStep
    | AdvancePersistentStep
    | CleanUpStep
    | ObtainFrozenLocStep
    | ForgetOldStep
    | PushSyncStep
    | PopSyncStep
    | StutterStep

  predicate PresentPersistentLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendPersistentLocOp?
    && vop.loc == s.persistentLoc

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs
  }

  predicate AdvanceEphemeral(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?
    && !vop.replay

    && s.ephemeralStateIndex == s.startVersion + |s.journal|
    && var jes := JournalEntriesForUIOp(vop.uiop);

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal + jes
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex + |jes|
    && s'.syncReqs == s.syncReqs
  }

  predicate Replay(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.AdvanceOp?
    && vop.replay

    && var jes := JournalEntriesForUIOp(vop.uiop);
    && s.ephemeralStateIndex + |jes| <= s.startVersion + |s.journal|
    && 0 <= s.ephemeralStateIndex - s.startVersion <= |s.journal|
    && jes == s.journal[
                 s.ephemeralStateIndex - s.startVersion
              .. s.ephemeralStateIndex - s.startVersion + |jes|]

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex + |jes|
    && s'.syncReqs == s.syncReqs
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?

    && s'.startVersion == 0
    && 0 <= s.persistentStateIndex - s.startVersion <= |s.journal|
    && s'.journal
        == s.journal[s.persistentStateIndex - s.startVersion
                  .. s.persistentJournalIndex - s.startVersion]
    && s'.persistentStateIndex == 0
    && s'.persistentJournalIndex
        == s.persistentJournalIndex - s.persistentStateIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == None
    && s'.frozenLoc == None
    && s'.ephemeralStateIndex == 0
    && s'.syncReqs == map[]
  }

  predicate AdvancePersistent(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.JournalInternalOp?

    && s.frozenStateIndex.Some?
    && s.frozenLoc.Some?

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.frozenStateIndex.value
    && s'.persistentJournalIndex == (
      if s.persistentJournalIndex < s.frozenStateIndex.value then
        s.frozenStateIndex.value
      else
        s.persistentJournalIndex
    )
    && s'.persistentLoc == s.frozenLoc.value
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs
  }

  predicate CleanUp(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.JournalInternalOp?

    && 0 <= s'.startVersion - s.startVersion <= |s.journal|

    && s'.startVersion <= s'.persistentStateIndex
    && s'.journal == s.journal[s'.startVersion - s.startVersion ..]
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs
  }

  predicate ObtainFrozenLoc(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.SendFrozenLocOp?

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == Some(vop.loc)
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs
  }

  predicate ForgetOld(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.ForgetOldOp?

    && s.frozenStateIndex == Some(s.persistentStateIndex)
    && s.frozenLoc.Some?

    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.frozenLoc.value
    && s'.frozenStateIndex == None
    && s'.frozenLoc == None
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs
  }

  predicate PushSync(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.PushSyncOp?

    && vop.id !in s.syncReqs
    
    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == s.syncReqs[vop.id := s.startVersion + |s.journal|]
  }

  predicate PopSync(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.PopSyncOp?

    && vop.id in s.syncReqs
    && s.syncReqs[vop.id] <= s.persistentJournalIndex
    
    && s'.startVersion == s.startVersion
    && s'.journal == s.journal
    && s'.persistentStateIndex == s.persistentStateIndex
    && s'.persistentJournalIndex == s.persistentJournalIndex
    && s'.persistentLoc == s.persistentLoc
    && s'.frozenStateIndex == s.frozenStateIndex
    && s'.frozenLoc == s.frozenLoc
    && s'.ephemeralStateIndex == s.ephemeralStateIndex
    && s'.syncReqs == MapRemove1(s.syncReqs, vop.id)
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.TristateInternalOp?)
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case PresentPersistentLocStep => PresentPersistentLoc(k, s, s', vop)
      case AdvanceEphemeralStep => AdvanceEphemeral(k, s, s', vop)
      case ReplayStep => Replay(k, s, s', vop)
      case CrashStep => Crash(k, s, s', vop)
      case AdvancePersistentStep => AdvancePersistent(k, s, s', vop)
      case CleanUpStep => CleanUp(k, s, s', vop)
      case ObtainFrozenLocStep => ObtainFrozenLoc(k, s, s', vop)
      case ForgetOldStep => ForgetOld(k, s, s', vop)
      case PushSyncStep => PushSync(k, s, s', vop)
      case PopSyncStep => PopSync(k, s, s', vop)
      case StutterStep => Stutter(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }
}
