// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CoordinationSystem.i.dfy"
include "GCCrashTolerantJournal.i.dfy"
include "GCCrashTolerantMap.i.dfy"

// TODO(jonh,robj): This file consists largely of copy-pastage from CoordinationSystem.
// Figure out how to refactor; maybe create subpredicates in CoordinationSystem to reuse here?
// Or maybe now it's just functor re-use.
// Or maybe it'll get interesting because we're going to begin talking about framing finally.

module GCCoordinationSystem {
  import opened MapRemove_s
  import opened CrashTolerantMapSpecMod
  import opened MsgHistoryMod
  import opened ValueMessage
  import opened TotalKMMapMod
  import opened LSNMod
  import opened GCCrashTolerantJournal
  import opened GCCrashTolerantMap
  import CoordinationSystem

  import Async = CrashTolerantMapSpecMod.uiopifc.async
  type UIOp = CrashTolerantMapSpecMod.uiopifc.UIOp

  type SyncReqs = map<CrashTolerantMapSpecMod.uiopifc.SyncReqId, LSN>

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,
      mapLsn: LSN  // invariant: agrees with mapp.stampedMap.seqEnd
    )
  {
  }

  datatype Variables = Variables(
    journal: GCCrashTolerantJournal.Variables,
    mapp: GCCrashTolerantMap.Variables,
    ephemeral: Ephemeral
  )
  {
    predicate WF()
    {
      && journal.WF()
      && mapp.WF()
      && (ephemeral.Known? == journal.ephemeral.Known? == mapp.ephemeral.Known?)
      // Provable from invariant:
      && (journal.inFlight.Some? ==> mapp.inFlight.Some?)
    }

    predicate Init()
    {
      && GCCrashTolerantJournal.Init(journal)
      && GCCrashTolerantMap.Init(mapp)
      && ephemeral.Unknown?
    }
  }

  function SimpleJournalLabel(clbl: CrashTolerantJournal.TransitionLabel) : GCCrashTolerantJournal.TransitionLabel
  {
    GCCrashTolerantJournal.TransitionLabel([], {}, clbl)
  }

  function SimpleMapLabel(clbl: CrashTolerantMap.TransitionLabel) : GCCrashTolerantMap.TransitionLabel
  {
    GCCrashTolerantMap.TransitionLabel([], {}, clbl)
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v'.ephemeral.Known?
    // todo(tony): allocs and freed are now constrained in two places, by SimpleJournalLabel(), and journal.LoadEphemeralFromPersistent. Danger.
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.LoadEphemeralFromPersistentLabel()))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn)))
    && v'.ephemeral.progress == Async.InitEphemeralState()
    && v'.ephemeral.syncReqs == map[]
    // and thus all fields of v' are constrained.
  }

  // Move some journal state into the map to make it (closer to) fresh
  predicate Recover(v: Variables, v': Variables, uiop : UIOp, records:MsgHistory)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v'.WF()
    && v'.ephemeral.Known?

    && records.WF()

    // NB that Recover can interleave with mapadt steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.ReadForRecoveryLabel(records)))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.PutRecordsLabel(records)))

    && v'.ephemeral == v.ephemeral.(mapLsn := records.seqEnd) // all else defined via predicates above
  }

  predicate AcceptRequest(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.RequestOp?
    && uiop.baseOp.req !in v.ephemeral.progress.requests
    && v' == v.(ephemeral := v.ephemeral.(progress := v.ephemeral.progress.(
        requests := v.ephemeral.progress.requests + {uiop.baseOp.req})))
  }

  predicate Query(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.GetInput? // ensures that the uiop translates to a Get op
    && uiop.baseOp.reply.output.GetOutput?
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id

    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply !in v.ephemeral.progress.replies
    && var key := uiop.baseOp.req.input.key;
    && var value := uiop.baseOp.reply.output.value;
    && assert AnyKey(key);

    // Journal confirms that the map is up-to-date (but otherwise doesn't do anything).
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.QueryEndLsnLabel(v.ephemeral.mapLsn)))
    // Map handles the query
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.QueryLabel(v.ephemeral.mapLsn, key, value)))

    && v'.ephemeral == v.ephemeral.(progress := v.ephemeral.progress.(
          requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
          replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
      ))
  }

  predicate Put(v: Variables, v': Variables, uiop : UIOp)
  {
    // At this layer we allow puts to run ahead, and then just let Queries be
    // delayed until Recover catches up the mapadt.
    // We expect the real implementation to maintain the invariant that, after
    // recovery, the map stays "fresh" with the puts in the journal rather than
    // checking that property at each query.
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?

    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.PutInput? // ensures that the uiop translates to a put op
    && uiop.baseOp.reply.output.PutOutput?
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id
    && uiop.baseOp.reply !in v.ephemeral.progress.replies

    && var key := uiop.baseOp.req.input.key;
    && var val := uiop.baseOp.req.input.value;

    && var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));

    && v.WF()
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.PutLabel(singleton)))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.PutRecordsLabel(singleton)))

    && v'.ephemeral == v.ephemeral.(
          mapLsn := v.ephemeral.mapLsn + 1,
          progress := v.ephemeral.progress.(
            requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
            replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
          // syncReqs UNCHANGED
          )
      )
  }

  predicate DeliverReply(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && uiop.OperateOp?
    && uiop.baseOp.ReplyOp?
    && uiop.baseOp.reply in v.ephemeral.progress.replies
    && v' == v.(ephemeral := v.ephemeral.(progress := v.ephemeral.progress.(
        replies := v.ephemeral.progress.replies - {uiop.baseOp.reply})))
  }

  // Journal Internal steps (writing stuff out to disk, for example)
  // and Betree Internal steps (writing stuff to disk, flushing and compacting,
  // which create new blocks in cache and rearrange the indirection table)
  // all look like stutters at this layer.

  predicate JournalInternal(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    // TODO(tony): is having an 'exists' here a good idea?
    // journal internal step that maybe does GC
    // lbl.alloc and freed are constrained by GCCrashTolerantJournal.Next
    && (exists lbl: GCCrashTolerantJournal.TransitionLabel ::
        && lbl.base.InternalLabel?
        && GCCrashTolerantJournal.Next(v.journal, v'.journal, lbl)
        && v' == v.(journal := v'.journal)  // predicate update above
    )
  }

  predicate MapInternal(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    // TODO(tony): is having an 'exists' here a good idea?
    // Map internal step that maybe does GC
    // lbl.alloc and freed are constrained by GCCrashTolerantMap.Next
    && (exists lbl: GCCrashTolerantMap.TransitionLabel ::
        && lbl.base.InternalLabel?
        && GCCrashTolerantMap.Next(v.mapp, v'.mapp, lbl)
        && v' == v.(mapp := v'.mapp)  // predicate update above
    )
  }

  predicate ReqSync(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.ReqSyncOp?
    && uiop.syncReqId !in v.ephemeral.syncReqs

    // TODO(robj): cleanup: delete this predicate; it's probably totally unecessary.
    // Need to record the current LSN, which is generally the current map state. But we
    // also need to confirm that the journal hasn't gone ahead, since sync is relative to
    // writes (which have affected the journal).
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.QueryEndLsnLabel(v.ephemeral.mapLsn)))

    && v'.mapp == v.mapp

    // NB that the label for a sync in the table is the LSN AFTER the last write
    && v'.ephemeral == v.ephemeral.(
        syncReqs := v.ephemeral.syncReqs[uiop.syncReqId := v.ephemeral.mapLsn]
      )
  }

  predicate ReplySync(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v.ephemeral.Known?
    && uiop.ReplySyncOp?
    && uiop.syncReqId in v.ephemeral.syncReqs
    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.QueryLsnPersistenceLabel(v.ephemeral.syncReqs[uiop.syncReqId])))
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := MapRemove1(v.ephemeral.syncReqs, uiop.syncReqId)
      ))
  }

  // This step models issuing the superblock write
  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, newBoundaryLsn: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?

    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.CommitStartLabel(newBoundaryLsn, v.ephemeral.mapLsn)))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.CommitStartLabel(newBoundaryLsn)))

    && v'.ephemeral == v.ephemeral  // UNCHANGED
  }

  // This step models learning that the outstanding superblock write has completed.
  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && uiop.SyncOp?
    && v.ephemeral.Known? // provable from invariant

    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.CommitCompleteLabel(v.ephemeral.mapLsn)))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.CommitCompleteLabel()))

    && v'.ephemeral == v.ephemeral  // UNCHANGED
  }

  predicate Crash(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && uiop.CrashOp?

    && GCCrashTolerantJournal.Next(v.journal, v'.journal, SimpleJournalLabel(CrashTolerantJournal.CrashLabel()))
    && GCCrashTolerantMap.Next(v.mapp, v'.mapp, SimpleMapLabel(CrashTolerantMap.CrashLabel()))

    && v'.ephemeral.Unknown?
  }

  predicate Init(v: Variables) {
    v.Init()
  }

  type Step = CoordinationSystem.Step // laaaazy

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, step: Step) {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', uiop)
      case RecoverStep(puts) => Recover(v, v', uiop, puts)
      case AcceptRequestStep() => AcceptRequest(v, v', uiop)
      case QueryStep() => Query(v, v', uiop)
      case PutStep() => Put(v, v', uiop)
      case DeliverReplyStep() => DeliverReply(v, v', uiop)
      case JournalInternalStep() => JournalInternal(v, v', uiop)
      case MapInternalStep() => MapInternal(v, v', uiop)
      case ReqSyncStep() => ReqSync(v, v', uiop)
      case ReplySyncStep() => ReplySync(v, v', uiop)
      case CommitStartStep(newBoundaryLsn) => CommitStart(v, v', uiop, newBoundaryLsn)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
      case CrashStep() => Crash(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
