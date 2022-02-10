// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "JournalIfc.i.dfy"
include "../../Spec/MapSpec.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../lib/Base/MapRemove.s.dfy"

module CoordinatorMod(journalMod: JournalIfc)  {
  import opened Options
  import opened MapRemove_s
  import opened StampedMapMod
  import opened CrashTolerantMapSpecMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
  import opened FullKMMapMod

  import Async = CrashTolerantMapSpecMod.async
  type UIOp = CrashTolerantMapSpecMod.UIOp

  // TODO(jonh): plug in PagedMap here. Right now only exploring journal.
  type MapAdt = StampedMapMod.StampedMap
  type Journal = journalMod.PersistentJournal

  function MapAdtMkfs() : MapAdt {
    StampedMapMod.Empty()
  }

  datatype DiskImage = DiskImage(
    mapadt: MapAdt,
    journal: Journal
    )
  {
    predicate WF() {
      && journalMod.PWF(journal)
    }

    function SeqEnd() : LSN
      requires WF()
    {
      if journalMod.PJournalSeqEnd(journal).Some? then journalMod.PJournalSeqEnd(journal).value else mapadt.seqEnd
    }

    predicate CompletesSync(lsn: LSN)
      requires WF()
    {
      lsn < SeqEnd()
    }
  }

  type SyncReqs = map<CrashTolerantMapSpecMod.SyncReqId, LSN>

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,

      mapadt: MapAdt,
      journal: journalMod.EphemeralJournal,

      frozenMap: Option<MapAdt>
    )
  {
    predicate WF() {
      Known? ==> (
        && journalMod.EWF(journal)
      )
    }
  }

  function MkfsDiskImage() : DiskImage
  {
    DiskImage(MapAdtMkfs(), journalMod.Mkfs())
  }

  // TODO(jonh): maybe this is a parameterized type we can reuse in CMJ & here?
  // Actually, maybe we should parameterize the entire module and plug in these
  // paged implementations! I'll start with it concrete though.
  datatype Variables = Variables(
    persistentImage: DiskImage,
    ephemeral: Ephemeral,
    inFlightImage: Option<DiskImage>
  )
  {
    predicate WF()
    {
      && persistentImage.WF()
      && (ephemeral.Known? ==> ephemeral.WF())
      && (inFlightImage.Some? ==> inFlightImage.value.WF())
    }

    predicate Mkfs()
    {
      && persistentImage == MkfsDiskImage()
      && ephemeral.Unknown?
      && inFlightImage.None?
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v.ephemeral.Unknown?
    && v' == v.(ephemeral := Known(
      Async.InitEphemeralState(),
      map[],  // syncReqs
      v.persistentImage.mapadt,
      journalMod.LoadJournal(v.persistentImage.journal),
      None  // frozen map
      ))
  }

  // The ephemeral map and ephemeral journal are at the same lsn, which only happens
  // after recovery has "caught the map up" to the journal.
  predicate MapIsFresh(v: Variables)
  {
    && v.WF()
    && v.ephemeral.Known?
    && var jend := journalMod.EJournalSeqEnd(v.ephemeral.journal);
      (jend.Some? ==> jend.value == v.ephemeral.mapadt.seqEnd)
  }

  function NextLSN(v: Variables) : LSN
    requires v.ephemeral.Known?
  {
    v.ephemeral.mapadt.seqEnd
  }

  // Move some journal state into the map to make it (closer to) fresh
  predicate Recover(v: Variables, v': Variables, uiop : UIOp, puts:MsgHistory)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && !MapIsFresh(v)
    && v'.WF()

    && puts.WF()
    && puts.CanFollow(v.ephemeral.mapadt.seqEnd)
    && journalMod.JournalIncludesSubseq(v.ephemeral.journal, puts)

    // NB that Recover can interleave with mapadt steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && v' == v.(ephemeral := v.ephemeral.(mapadt := MapPlusHistory(v.ephemeral.mapadt, puts)))
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
    && MapIsFresh(v)
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
    && value == v.ephemeral.mapadt.mi[key].value
    && v' == v.(ephemeral := v.ephemeral.(progress := v.ephemeral.progress.(
        requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
        replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
      )))
  }

  predicate Put(v: Variables, v': Variables, uiop : UIOp)
  {
    // Here we're not allowing puts until MapIsFresh, and then maintaining that
    // invariant. We could alternately allow puts to run ahead, and then just
    // let Queries be delayed until Recover catches up the mapadt.
    // I'm modeling it this way because this matches the phase-driven behavior
    // (recover, then be done recovering until next crash) we expect the real
    // implementation to maintain.
    && MapIsFresh(v)

    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.PutInput? // ensures that the uiop translates to a put op
    && uiop.baseOp.reply.output.PutOutput?
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id
    && uiop.baseOp.reply !in v.ephemeral.progress.replies

    && var key := uiop.baseOp.req.input.key;
    && var val := uiop.baseOp.req.input.value;

    && var singleton := MsgHistoryMod.Singleton(NextLSN(v), KeyedMessage(key, Define(val)));

    && v.WF()
    && v' == v.(ephemeral := v.ephemeral.(
          journal := journalMod.JournalConcat(v.ephemeral.journal, singleton),
          mapadt := MapPlusHistory(v.ephemeral.mapadt, singleton),
          // Frozen stuff unchanged here.
          progress := v.ephemeral.progress.(
            requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
            replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
          )
      ))
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

  // predicate JournalInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: JournalMachineMod.Skolem)
  // predicate SplinterTreeInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: SplinterTreeMachineMod.Skolem)

  predicate ReqSync(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.ReqSyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.
    && v'.ephemeral.Known?
    && uiop.syncReqId !in v.ephemeral.syncReqs
    // NB that the label for a sync in the table is the LSN AFTER the last write
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := v.ephemeral.syncReqs[uiop.syncReqId := NextLSN(v)]
      ))
  }

  predicate ReplySync(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.ReplySyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.
    && uiop.syncReqId in v.ephemeral.syncReqs
    && v.persistentImage.CompletesSync(v.ephemeral.syncReqs[uiop.syncReqId]) // sync lsn is persistent
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := MapRemove1(v.ephemeral.syncReqs, uiop.syncReqId)
      ))
  }

  predicate FreezeMapAdt(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    // Copy the current map into the frozen one, deleting whatever was
    // frozen.
    // TODO this should cause mischief if a Commit is in progress. Does it?
    && v' == v.(ephemeral := v.ephemeral.(frozenMap := Some(v.ephemeral.mapadt)))
  }

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, endJournal: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v.inFlightImage.None?

    && v.ephemeral.frozenMap.Some?
    && var startJournal := v.ephemeral.frozenMap.value.seqEnd;
    // Frozen map can't go backwards vs persistent map, lest we end up with
    // a gap to the ephemeral journal start.
    && v.persistentImage.mapadt.seqEnd <= startJournal
    // And of course there should be no way for it to have passed the ephemeral map!
    && startJournal <= v.ephemeral.mapadt.seqEnd
    && startJournal <= endJournal
    && v.persistentImage.SeqEnd() <= endJournal
    && journalMod.JournalCanFreeze(v.ephemeral.journal, startJournal, endJournal)

    && v'.inFlightImage.Some?
    && v' == v.(inFlightImage := Some(DiskImage(
        v.ephemeral.frozenMap.value,
        journalMod.JournalFreeze(v.ephemeral.journal, startJournal, endJournal))))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.inFlightImage.Some?
    && var ifImage := v.inFlightImage.value;

    && uiop.SyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.

    // TODO(jonh): this had better be an invariant, but if it's not, we're
    // gonna have a weird liveness/crash recovery bug. Confirm that'll show up in
    // proof.
    && journalMod.CanDiscardOld(v.ephemeral.journal, ifImage.mapadt.seqEnd)

    // pruning below is nonsense without this, but "luckily" this is an invariant:
//    && JournalCanDiscardTo(v.ephemeral.journal, ifImage.mapadt.seqEnd)

    // Now that the disk journal is updated, we need to behead the
    // ephemeral journal, since interpretation want to CanFollow it
    // onto the persistent mapadt.
    && var j' := journalMod.DiscardOld(v.ephemeral.journal, ifImage.mapadt.seqEnd);

    && v' == v.(
        persistentImage := ifImage,
        ephemeral := v.ephemeral.(journal := j'),
        // Update journal, mapadt here if modeling clean, frozen
        inFlightImage := None)
  }

  predicate Crash(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.CrashOp?
    && v' == v.(ephemeral := Unknown, inFlightImage := None)
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | RecoverStep(puts:MsgHistory)
    | AcceptRequestStep()
    | QueryStep()
    | PutStep()
    | DeliverReplyStep()
//    | JournalInternalStep()
//    | SplinterTreeInternalStep()
    | ReqSyncStep()
    | ReplySyncStep()
    | FreezeMapAdtStep()
    | CommitStartStep(seqBoundary: LSN)
    | CommitCompleteStep()
    | CrashStep()

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, step: Step) {
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', uiop)
      case RecoverStep(puts) => Recover(v, v', uiop, puts)
      case AcceptRequestStep() => AcceptRequest(v, v', uiop)
      case QueryStep() => Query(v, v', uiop)
      case PutStep() => Put(v, v', uiop)
//      case JournalInternalStep(sk) => JournalInternal(v, v', uiop, cacheOps, sk)
//      case SplinterTreeInternalStep(sk) => SplinterTreeInternal(v, v', uiop, cacheOps, sk)
      case DeliverReplyStep() => DeliverReply(v, v', uiop)
      case ReqSyncStep() => ReqSync(v, v', uiop)
      case ReplySyncStep() => ReplySync(v, v', uiop)
      case FreezeMapAdtStep() => FreezeMapAdt(v, v', uiop)
      case CommitStartStep(seqBoundary) => CommitStart(v, v', uiop, seqBoundary)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
      case CrashStep() => Crash(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
