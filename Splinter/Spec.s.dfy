// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Base.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"

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

// Collect the entire history of possible snapshots, with a pointer to the persistent one.
// Sync requests begin at the head of the list (the ephemeral state).
// Once the persistent pointer reaches that same index, the sync may be acknowledged as complete.
// We don't do anything with old snapshots (indeed, no implementation could); I just wrote it
// this way for greatest simplicity.
module DeferredWriteMapSpecMod {
  import opened SequencesLite // Last, DropLast
  import opened MessageMod
  import InterpMod
  import MapSpecMod

  type SyncReqId = nat
  datatype Version = Version(mapp: MapSpecMod.Variables, syncReqIds: set<SyncReqId>)
  datatype Variables = Variables(versions: seq<Version>, stableIdx: nat)
  {
    predicate WF() {
      && 0 < |versions|  // always some persistent, ephemeral version
      && (forall i :: 0<=i<|versions| ==> versions[i].mapp.WF())
      && stableIdx < |versions|
    }
  }

  predicate Init(s: Variables)
  {
    && |s.versions| == 1
    && MapSpecMod.Init(s.versions[0].mapp)
    && s.versions[0].syncReqIds == {}
    && s.stableIdx == 0
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
  predicate AsyncFlush(s: Variables, s': Variables)
  {
    && s.WF()
    && s'.versions == s.versions
    // stableIdx advances towards, possibly all the way to, ephemeral state.
    && s.stableIdx < s'.stableIdx < |s.versions|
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
  // requestedAt is a there-exists variable that we're pushing up to stay in Jay Normal Form.
  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId, requestedAt: nat)
  {
    && s.WF()
    && requestedAt < |s.versions|
    && syncReqId in s.versions[requestedAt].syncReqIds
    && s.stableIdx <= requestedAt
    && s' == s
  }

  // JNF
  datatype Step =
    | QueryStep(k: Key, v: Value)
    | PutStep(k: Key, v: Value)
    | CrashStep
    | AsyncFlushStep
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId, requestedAt: nat)

  predicate NextStep(s: Variables, s': Variables, step: Step)
  {
    match step {
      case QueryStep(k: Key, v: Value) => Query(s, s', k, v)
      case PutStep(k: Key, v: Value) => Put(s, s', k, v)
      case CrashStep => Crash(s, s')
      case AsyncFlushStep => AsyncFlush(s, s')
      case ReqSyncStep(syncReqId) => ReqSync(s, s', syncReqId)
      case CompleteSyncStep(syncReqId, requestId) => CompleteSync(s, s', syncReqId, requestId)
    }
  }

  predicate Next(s: Variables, s': Variables)
  {
    exists step :: NextStep(s, s', step)
  }
}
