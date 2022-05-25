include "../lib/Base/FloatingSeq.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"
include "../lib/Base/MapRemove.s.dfy"
include "RefinementObligation.s.dfy"
include "Async.s.dfy"

// Collect the entire history of possible snapshots, with a pointer to the persistent one.
// Sync requests begin at the head of the list (the ephemeral state).
// Once the persistent pointer reaches that same index, the sync may be acknowledged as complete.
// Old snapshots are "forgotten", but we keep their place in the sequence for
// simplicity and hence readability: we don't have to do a bunch of confusing
// offset math to represent truncation.

module CrashTolerantUIOp(atomic: AtomicStateMachineMod) refines UIOpIfc {
  import async = AsyncMod(atomic) // Crash tolerance adds asynchrony whether you like it or not.

  type SyncReqId = nat
  datatype UIOp =
    | OperateOp(baseOp: async.UIOp)
    | CrashOp
    | SyncOp
    | ReqSyncOp(syncReqId: SyncReqId)
    | ReplySyncOp(syncReqId: SyncReqId)
    | NoopOp
}

module CrashTolerantMod(atomic: AtomicStateMachineMod) refines StateMachineIfc(CrashTolerantUIOp(atomic)) {
  import opened MapRemove_s
  import opened FloatingSeqMod
  import opened SequencesLite // Last, DropLast

  // Crash tolerance adds asynchrony whether you like it or not.

  //import uiopifc = CrashTolerantUIOp(atomic)
  // TODO(bparno): I think it's a bug that I have to use the next line, but the
  // prior isn't equivalent.
   // I really want to write this, but uiopifc isn't available in imports
//  import async = uiopifc.async
  // So I tried other synonyms, but they don't act module-equivalent:
  // import uiopmod = StateMachineIfc(CrashTolerantUIOp(atomic)).uiopifc
  //import async = uiopifc.async
  //import async = StateMachineIfc(CrashTolerantUIOp(atomic)).uiopifc.async

  datatype Constants = Constants
  type Version = uiopifc.async.PersistentState
  datatype Variables = Variables(
    versions: FloatingSeq<Version>,
    asyncEphemeral: uiopifc.async.EphemeralState,

    // Request id points at the number of LSNs that must be persisted.
    // So if the client ReqSyncs after 3 writes (seqEnd==3), the value
    // in the map is 3.
    syncRequests: map<uiopifc.SyncReqId, nat>
    )
  {
    predicate WF() {
      // There is always some persistent version, even if just a view of the
      // mkfs state
      && 0 < |versions|
      && versions.IsActive(|versions|-1) // At least one active version
    }

    // The stable index of the system; all later versions are liable to be lost on Crash
    function StableIndex() : nat
    {
      versions.FirstActiveIndex()
    }
  }

  function InitState() : Variables {
    Variables(FloatingSeq(0, [uiopifc.async.InitPersistentState()]), uiopifc.async.InitEphemeralState(), map[])
  }

  // This isn't a transition, just a partial action for readibility.
  predicate OptionallyAppendVersion(versions: FloatingSeq<Version>, versions': FloatingSeq<Version>)
  {
    // new versions list is either some new thing appended to the old one,
    || (0<|versions'| && versions'.DropLast() == versions)
    // or unchanged. We allow unchanged in the trusted spec so that
    // implementations don't have to account for number of read-only (query) ops.
    || versions' == versions
  }

  predicate Operate(v: Variables, v': Variables, op: uiopifc.async.UIOp)
  {
    // let nondeterminism of v' choose these values
    // (Imagine they're coming in from JNF via a skolemized exists -- but that makes
    // proofs need exists-witnesses.)
    && var newVersions := v'.versions;
    && var newAsyncEphemeral := v'.asyncEphemeral;

    && v.WF()
    && v'.WF()
    && OptionallyAppendVersion(v.versions, newVersions)
    && uiopifc.async.NextStep(
        uiopifc.async.Variables(v.versions.Last(), v.asyncEphemeral),
        uiopifc.async.Variables(newVersions.Last(), newAsyncEphemeral),
        op)
    && v' == v.(
        versions := newVersions,
        asyncEphemeral := newAsyncEphemeral
      )
  }

  // Uh oh, anything not flushed (past stableIdx) is gone. But you still get a consistent version
  // at least as new as every version synced before the crash.
  predicate Crash(v: Variables, v': Variables)
  {
    && v.WF()
    && v' == v.(
        versions := v.versions.GetPrefix(v.StableIndex()+1),
      // Crash forgets ephemeral stuff -- requests and syncRequests submitted but not answered.
        asyncEphemeral := uiopifc.async.InitEphemeralState(),
        syncRequests := map[]
      )
  }

  // The Sync *action* causes some LSNs to become persistent, which may enable
  // the system to reply to some sync *requests*.
  // some sync *requests* to be replied to.
  // The implementation may push some stuff out to the disk without getting
  // all the way up to date with the ephemeral state.
  predicate Sync(v: Variables, v': Variables)
  {
    // let nondeterminism of v' choose this value
    // This wouldn't take so much explaining if we just exists newStableIdx, but then
    // it's harder to use and muddies up the UIOp skolem. Sorry.
    && var newStableIdx := v'.StableIndex();

    && v.WF()
    && v.StableIndex() <= newStableIdx < |v.versions|
    // Commit forgets old versions.
    && v' == v.(versions := v.versions.GetSuffix(newStableIdx))
  }

  // sync api contract to the end user
  // NB it's a very little bit funky. For all normal requests, three atomic
  // actions occur: the request arrives, it's executed (serialized), the reply
  // is delivered. For Syncs, we don't bother explicitly recording the serialization
  // point; ReplySync just gets enabled at some point before it occurs. Sorry?
  predicate ReqSync(v: Variables, v': Variables, syncReqId: uiopifc.SyncReqId)
  {
    && v.WF()
    && syncReqId !in v.syncRequests // don't want to talk about weird behavior with duplicate ids
    && v' == v.(syncRequests := v.syncRequests[syncReqId := |v.versions|-1])
  }

  // When your syncReqId gets flushed all the way to the persistent version slot,
  // the sync is complete and that version is stable.
  predicate ReplySync(v: Variables, v': Variables, syncReqId: uiopifc.SyncReqId)
  {
    && v.WF()
    && syncReqId in v.syncRequests
    && v.syncRequests[syncReqId] <= v.StableIndex()
    && v' == v.(syncRequests := MapRemove1(v.syncRequests, syncReqId))
  }

  predicate NextStep(c: Constants, v: Variables, v': Variables, uiop: uiopifc.UIOp)
  {
    match uiop {
      case OperateOp(baseOp) => Operate(v, v', baseOp)
      case CrashOp => Crash(v, v')
      case SyncOp() => Sync(v, v')
      case ReqSyncOp(syncReqId) => ReqSync(v, v', syncReqId)
      case ReplySyncOp(syncReqId) => ReplySync(v, v', syncReqId)
      case NoopOp => v' == v
    }
  }

  predicate Next(c: Constants, v: Variables, v': Variables, uiop: uiopifc.UIOp)
  {
    exists uiop :: NextStep(c, v, v', uiop)
  }
}
