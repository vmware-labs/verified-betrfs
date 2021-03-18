include "Base.i.dfy"

module MapSpecMod {
  import opened MessageMod
  import InterpMod

  datatype Variables = Variables(interp: InterpMod.Interp)
  {
    predicate WF() {
      interp.WF()
    }
  }

  predicate Init(s: Variables)
  {
    && s.interp == InterpMod.Empty()
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s
    && s.interp.WF()
    && s.interp.mi[k] == v
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s.(interp := s.interp.(mi := s.interp.mi[k := v], seqEnd := s.interp.seqEnd + 1))
      // NB mutations advance the sequence number
  }
}

// Collect a chain of possible snapshots from the most recent committed
// version to the current ephemeral version.
// Sync requests are associated with the ephemeral version, and travel with
// that version until they arrive in the persistent state slot (index 0).
module DeferredWriteMapSpecMod {
  import opened Sequences
  import opened MessageMod
  import InterpMod
  import MapSpecMod

  type SyncReqId = nat
  datatype Version = Version(mapp: MapSpecMod.Variables, syncReqIds: set<SyncReqId>)
  datatype Variables = Variables(versions: seq<Version>)
  {
    predicate WF() {
      && 0 < |versions|  // always some persistent, ephemeral version
      && (forall i :: 0<=i<|versions| ==> versions[i].mapp.WF())
    }
  }

  predicate Init(s: Variables)
  {
    && |s.versions| == 1
    && MapSpecMod.Init(s.versions[0].mapp)
    && s.versions[0].syncReqIds == {}
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.WF()
    && s' == s
    && MapSpecMod.Query(Last(s.versions).mapp, Last(s'.versions).mapp, k, v)
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.WF()
    && s'.WF()
    && DropLast(s'.versions) == s.versions  // Concatenate a single version.
    && MapSpecMod.Put(Last(s.versions).mapp, Last(s'.versions).mapp, k, v)
    && Last(s'.versions).syncReqIds == {} // no sync reqs yet
  }

  // Uh oh, anything not flushed is gone. But you still get a consistent version
  // at least as new as every version synced before the crash.
  predicate Crash(s: Variables, s': Variables)
  {
    && s.WF()
    && s'.versions == [s.versions[0]]
  }

  // TODO move to lib
  function UnionAll<T>(sets: seq<set<T>>) : (uset:set<T>)
    ensures forall i, v | 0<=i<|sets| && v in sets[i] :: v in uset
    // ensures forall v | v in uset :: exists i :: 0<=i<|sets| && v in sets[i]
  {
    if |sets|==0 then {} else UnionAll(DropLast(sets)) + Last(sets)
  }

  // The implementation may push some stuff out to the disk without getting
  // all the way up to date with the ephemeral state.
  predicate AsyncFlush(s: Variables, s': Variables, numConsumed: nat)
  {
    && s.WF()
    && numConsumed < |s.versions| // Must leave at least one version left over
    // Aggregate all the affected syncReqIds into one big set in the persistent slot
    && var syncedReqIds := UnionAll(seq(numConsumed, i requires 0<=i<numConsumed => s.versions[i].syncReqIds));
    && s'.versions == [ Version(s.versions[numConsumed].mapp, syncedReqIds) ]
      + s.versions[numConsumed+1..]
  }

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
  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && s.WF()
    && s' == s
    && syncReqId in s.versions[0].syncReqIds
  }

  // JNF
  datatype Step =
    | QueryStep(k: Key, v: Value)
    | PutStep(k: Key, v: Value)
    | CrashStep
    | AsyncFlushStep(numConsumed: nat)
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)

  predicate NextStep(s: Variables, s': Variables, step: Step)
  {
    match step {
      case QueryStep(k: Key, v: Value) => Query(s, s', k, v)
      case PutStep(k: Key, v: Value) => Put(s, s', k, v)
      case CrashStep => Crash(s, s')
      case AsyncFlushStep(numConsumed: nat) => AsyncFlush(s, s', numConsumed)
      case ReqSyncStep(syncReqId: SyncReqId) => ReqSync(s, s', syncReqId)
      case CompleteSyncStep(syncReqId: SyncReqId) => CompleteSync(s, s', syncReqId)
    }
  }

  predicate Next(s: Variables, s': Variables)
  {
    exists step :: NextStep(s, s', step)
  }
}
