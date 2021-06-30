include "../lib/Base/SequencesLite.s.dfy"
include "Async.s.dfy"

// Collect the entire history of possible snapshots, with a pointer to the persistent one.
// Sync requests begin at the head of the list (the ephemeral state).
// Once the persistent pointer reaches that same index, the sync may be acknowledged as complete.
// We don't do anything with old snapshots (indeed, no implementation could); I just wrote it
// this way for greatest simplicity.
module CrashTolerantMod(atomic: AtomicStateMachineMod) {
  import opened SequencesLite // Last, DropLast
  import async = AsyncMod(atomic) // Crash tolerance adds asynchrony whether you like it or not.

  type SyncReqId = nat
  datatype Version =
    | Truncated
      // jonh apology: The spec exposes the implementation-specific idea
      // of log truncation to keep the interpretation functions easy to
      // build. This way, when we truncate in the implementation, we
      // can just map that to a Truncated version in this spec version
      // sequence. This is lame, because we're asking the spec inspector
      // to understand impl details. An alternative would be to add
      // a "write-only ghost state" mechanism to the bottom bread, into
      // which Program.i could tuck away old ghost versions going back
      // to the dawn of time, and then the interpretation function
      // could peek at those to construct the version seq. This is a way
      // to add Lamport's history variable while respecting the .s/.i
      // split. But I'm too lazy to do that now, so please judge away.
    | Version(asyncState: async.Variables, syncReqIds: set<SyncReqId>)

  datatype Variables = Variables(versions: seq<Version>, stableIdx: nat)
  {
    predicate WF() {
      && 0 < |versions|  // always some persistent, ephemeral version
      // All versions beginning with the stableIdx aren't truncated,
      // so that crashing can't take us to a Truncated version.

      // QUESTION: Sowmya note: asyncState doesn't have a Version, but i think we're
      // trying to express that there are valid entries for all the records after the stable idx
      // So I think I'm right?
      //&& (forall i :: stableIdx<=i<|versions| ==> versions[i].asyncState.Version?)
      && (forall i :: stableIdx<=i<|versions| ==> versions[i].Version?)
      && stableIdx < |versions|
    }
  }


  function InitState() : Variables {
    Variables([Version(async.InitState(), {})], 0)
  }

  predicate Operate(s: Variables, s': Variables, op: async.UIOp)
  {
    && s.WF()
    && s'.WF()
    && DropLast(s'.versions) == s.versions  // Concatenate a single version.
    && async.NextStep(Last(s.versions).asyncState, Last(s'.versions).asyncState, op)
    && Last(s'.versions).syncReqIds == {} // taking a map step introduces a new version, with no new sync reqs on it yet
    && s'.stableIdx == s.stableIdx
  }

  // Uh oh, anything not flushed (past stableIdx) is gone. But you still get a consistent version
  // at least as new as every version synced before the crash.
  predicate Crash(s: Variables, s': Variables)
  {
    && s.WF()
    && s'.versions == s.versions[..s.stableIdx+1]
    && s'.stableIdx == s.stableIdx
  }

  // The implementation may push some stuff out to the disk without getting
  // all the way up to date with the ephemeral state.
  predicate SpontaneousCommit(s: Variables, s': Variables)
  {
    && s.WF()
    && |s'.versions| == |s.versions|
    // Commit can truncate old versions
    && (forall i | 0<=i<|s.versions| ::
      || s'.versions == s.versions
      || (i < s.stableIdx && s'.versions[i].Truncated?)
      )
    && s'.WF()  // But it can't truncate things after stableIdx
    // stableIdx advances towards, possibly all the way to, ephemeral state.
    && s.stableIdx < s'.stableIdx < |s.versions|
  }

  // sync api contract to the end user
  predicate ReqSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && s.WF()
    // Add the syncReqId to the ephemeral version.
    // NB If there is only one version, ephemeral==persistent, so the sync
    // request is immediately complete. Which means the right thing happens.
    && var eph := Last(s.versions);
    && s'.versions == DropLast(s.versions)
                  + [eph.(syncReqIds := eph.syncReqIds + {syncReqId})]
  }

  // When your syncReqId gets flushed all the way to the persistent version slot,
  // the sync is complete and that version is stable.
  // requestedAt is a there-exists variable that we're pushing up to stay in Jay Normal Form.
  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId, requestedAt: nat)
  {
    && s.WF()
    && requestedAt < |s.versions|
    && s.versions[requestedAt].Version?
    && syncReqId in s.versions[requestedAt].syncReqIds
    && requestedAt <= s.stableIdx
  }

  // The Op provides *most* of Jay Normal Form -- except skolem variables, of which we have
  // exactly one, so I decided to just exists it like a clown.
  datatype UIOp =
    | OperateOp(baseOp: async.UIOp) // Put or Query Internally
    | CrashOp
    | SpontaneousCommitOp // Check with Jon
    | ReqSyncOp(syncReqId: SyncReqId)
    | CompleteSyncOp(syncReqId: SyncReqId)
    | NoopOp

  predicate NextStep(s: Variables, s': Variables, uiop: UIOp)
  {
    match uiop {
      case OperateOp(baseOp) => Operate(s, s', baseOp)
      case CrashOp => Crash(s, s')
      case SpontaneousCommitOp => SpontaneousCommit(s, s')
      case ReqSyncOp(syncReqId) => ReqSync(s, s', syncReqId)
      case CompleteSyncOp(syncReqId) => (exists requestedAt :: CompleteSync(s, s', syncReqId, requestedAt))
      case NoopOp => s' == s
    }
  }

  predicate Next(s: Variables, s': Variables, uiop: UIOp)
  {
    exists uiop :: NextStep(s, s', uiop)
  }
}

