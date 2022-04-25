// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CrashTolerantMap.i.dfy"
include "CrashTolerantJournal.i.dfy"
include "../../Spec/MapSpec.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../lib/Base/MapRemove.s.dfy"

module CoordinationSystem {
  import opened Options
  import opened MapRemove_s
  import opened CrashTolerantMapSpecMod
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
  import opened TotalKMMapMod
  import opened LSNMod
  import opened CrashTolerantJournal
  import opened CrashTolerantMap

  import Async = CrashTolerantMapSpecMod.uiopifc.async
  type UIOp = CrashTolerantMapSpecMod.uiopifc.UIOp

  type SyncReqs = map<CrashTolerantMapSpecMod.uiopifc.SyncReqId, LSN>

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,
      mapLsn: LSN  // invariant: agrees with mapadt.stampedMap.seqEnd
    )
  {
  }

  datatype Variables = Variables(
    journal: CrashTolerantJournal.Variables,
    mapadt: CrashTolerantMap.Variables,
    ephemeral: Ephemeral
  )
  {
    predicate WF()
    {
      && journal.WF()
      && mapadt.WF()
      && (ephemeral.Known? == journal.ephemeral.Known? == mapadt.ephemeral.Known?)
      // Provable from invariant:
      && (journal.inFlight.Some? ==> mapadt.inFlight.Some?)
    }

    predicate Init()
    {
      && CrashTolerantJournal.Init(journal)
      && CrashTolerantMap.Init(mapadt)
      && ephemeral.Unknown?
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v'.ephemeral.Known?
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.LoadEphemeralFromPersistentLabel())
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn))
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
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.ReadForRecoveryLabel(records))
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.PutRecordsLabel(records))

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
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))
    // Map handles the query
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.QueryLabel(v.ephemeral.mapLsn, key, value))

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
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.PutLabel(singleton))
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.PutRecordsLabel(singleton))

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
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.InternalLabel())
    && v' == v.(journal := v'.journal)  // predicate update above
  }

  predicate MapInternal(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.InternalLabel())
    && v' == v.(mapadt := v'.mapadt)  // predicate update above
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
    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))

    && v'.mapadt == v.mapadt

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
    && CrashTolerantJournal.Next(v.journal, v'.journal,
      CrashTolerantJournal.QueryLsnPersistenceLabel(v.ephemeral.syncReqs[uiop.syncReqId]))
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

    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.CommitStartLabel(newBoundaryLsn, v.ephemeral.mapLsn))
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.CommitStartLabel(newBoundaryLsn))

    && v'.ephemeral == v.ephemeral  // UNCHANGED
  }

  // This step models learning that the outstanding superblock write has completed.
  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && uiop.SyncOp?
    && v.ephemeral.Known? // provable from invariant

    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.CommitCompleteLabel(v.ephemeral.mapLsn))
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.CommitCompleteLabel())

    && v'.ephemeral == v.ephemeral  // UNCHANGED
  }

  predicate Crash(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && uiop.CrashOp?

    && CrashTolerantJournal.Next(v.journal, v'.journal, CrashTolerantJournal.CrashLabel())
    && CrashTolerantMap.Next(v.mapadt, v'.mapadt, CrashTolerantMap.CrashLabel())

    && v'.ephemeral.Unknown?
  }

  predicate Init(v: Variables) {
    v.Init()
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | RecoverStep(puts: MsgHistory)
    | AcceptRequestStep()
    | QueryStep()
    | PutStep()
    | DeliverReplyStep()
    | JournalInternalStep()
    | MapInternalStep()
    | ReqSyncStep()
    | ReplySyncStep()
    | CommitStartStep(newBoundaryLsn: LSN)
    | CommitCompleteStep()
    | CrashStep()

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
