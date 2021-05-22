// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Message.s.dfy"
include "Interp.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"

module MapSpecMod {
  import opened MessageMod
  import InterpMod

  // UI
  datatype Input = GetInput(k: Key) | PutInput(k: Key, v: Value) | NoopInput
  datatype Output = GetOutput(v: Value) | PutOutput | NoopOutput

  // State machine
  datatype Variables = Variables(interp: InterpMod.Interp)
  {
    predicate WF() {
      interp.WF()
    }
  }

  function Empty() : Variables {
    Variables(InterpMod.Empty())
  }

  predicate Init(s: Variables)
  {
    && s == Empty()
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s
    && s.interp.WF()
    && s.interp.mi[k] == v
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s.(interp := s.interp.Put(k,v))
      // NB mutations advance the sequence number
  }

  predicate Next(v: Variables, v': Variables, input: Input, out: Output)
  {
  true
    || (
        && input.GetInput?
        && out.GetOutput?
        && Query(v, v', input.k, out.v)
       )
    || (
        && input.PutInput?
        && out.PutOutput?
        && Put(v, v', input.k, input.v)
       )
    || (
        && input.NoopInput?
        && out.NoopOutput?
        && v' == v
       )
  }
}

module AsyncMapSpecMod {
  import MapSpecMod

  type ID(==, !new)
  datatype Request = Request(input: MapSpecMod.Input, id: ID)
  datatype Reply = Reply(output: MapSpecMod.Output, id: ID)

  datatype Variables = Variables(mapv: MapSpecMod.Variables, requests: set<Request>, replies: set<Reply>)
  {
    predicate WF() {
      mapv.WF()
    }
  }

  function Empty() : Variables {
    Variables(MapSpecMod.Empty(), {}, {})
  }

  predicate Init(v: Variables) {
    && MapSpecMod.Init(v.mapv)
    && v.requests == {}
    && v.replies == {}
  }

  predicate DoRequest(v: Variables, v': Variables, req: Request) {
    // TODO Probably should disallow ID conflicts
    && v' == v.(requests := v.requests + {req})
  }

  // The serialization point for this request
  predicate DoExecute(v: Variables, v': Variables, req: Request, reply: Reply) {
    && reply.id == req.id
    && req in v.requests
    && MapSpecMod.Next(v.mapv, v'.mapv, req.input, reply.output)
    && v'.requests == v.requests - {req}
    && v'.replies == v.replies + {reply}
  }

  predicate DoReply(v: Variables, v': Variables, reply: Reply) {
    && v' == v.(replies := v.replies + {reply})
  }

  datatype UIOp =
    | RequestOp(req: Request)
    | ExecuteOp(req: Request, reply: Reply)
    | ReplyOp(reply: Reply)

  predicate NextStep(v: Variables, v': Variables, op: UIOp) {
    match op
      case RequestOp(req) => DoRequest(v, v', req)
      case ExecuteOp(req, reply) => DoExecute(v, v', req, reply)
      case ReplyOp(reply) => DoReply(v, v', reply)
  }

  predicate Next(v: Variables, v': Variables) {
    exists step :: NextStep(v, v', step)
  }
}

// Collect the entire history of possible snapshots, with a pointer to the persistent one.
// Sync requests begin at the head of the list (the ephemeral state).
// Once the persistent pointer reaches that same index, the sync may be acknowledged as complete.
// We don't do anything with old snapshots (indeed, no implementation could); I just wrote it
// this way for greatest simplicity.
module CrashTolerantMapSpecMod {
  import opened SequencesLite // Last, DropLast
  import opened MessageMod
  import InterpMod
  import AsyncMapSpecMod

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
    | Version(mapp: AsyncMapSpecMod.Variables, syncReqIds: set<SyncReqId>)

  datatype Variables = Variables(versions: seq<Version>, stableIdx: nat)
  {
    predicate WF() {
      && 0 < |versions|  // always some persistent, ephemeral version
      // All versions beginning with the stableIdx aren't truncated,
      // so that crashing can't take us to a Truncated version.

      // QUESTION: Sowmya note: mapp doesn't have a Version, but i think we're 
      // trying to express that there are valid entries for all the records after the stable idx 
      // So I think I'm right?
      //&& (forall i :: stableIdx<=i<|versions| ==> versions[i].mapp.Version?)
      // Sowmya's changes
      && (forall i :: stableIdx<=i<|versions| ==> versions[i].Version?)
      // && (forall i :: 0<=i<|versions| ==> versions[i].mapp.WF())
      && (forall i :: stableIdx<=i<|versions| ==> versions[i].mapp.WF())
      // end of Sowmya's changes ----
      && stableIdx < |versions|
    }
  }

  function Empty() : Variables {
    Variables([Version(AsyncMapSpecMod.Empty(), {})], 0)
  }

  predicate Init(s: Variables)
  {
    s == Empty()
  }

  predicate Operate(s: Variables, s': Variables, op: AsyncMapSpecMod.UIOp)
  {
    && s.WF()
    && s'.WF()
    && DropLast(s'.versions) == s.versions  // Concatenate a single version.
    && AsyncMapSpecMod.NextStep(Last(s.versions).mapp, Last(s'.versions).mapp, op)
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
  predicate AsyncCommit(s: Variables, s': Variables)
  {
    && s.WF()
    && |s'.versions| == |s.versions|
    // Commit can truncate old versions
    && (forall i | 0<=i<|s.versions| ::
      || s'.versions == s.versions
      || s'.versions[i].Truncated?)
    && s'.WF()  // But it can't truncate things after stableIdx
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
    && s.versions[requestedAt].Version?
    && syncReqId in s.versions[requestedAt].syncReqIds
    && requestedAt <= s.stableIdx
    && s' == s
  }

  // The Op provides *most* of Jay Normal Form -- except skolem variables, of which we have
  // exactly one, so I decided to just exists it like a clown.
  datatype UIOp =
    | OperateOp(baseOp: AsyncMapSpecMod.UIOp)
    | CrashOp
    | AsyncCommitOp
    | ReqSyncOp(syncReqId: SyncReqId)
    | CompleteSyncOp(syncReqId: SyncReqId)
    | NoopOp

  predicate NextStep(s: Variables, s': Variables, uiop: UIOp)
  {
    match uiop {
      case OperateOp(baseOp) => Operate(s, s', baseOp)
      case CrashOp => Crash(s, s')
      case AsyncCommitOp => AsyncCommit(s, s')
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
