// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "../CoordinationLayer/AbstractMap.i.dfy"
include "../Journal/MarshalledJournal.i.dfy"

// TODO(jonh,robj): This file consists largely of copy-pastage from CoordinationSystem.
// Figure out how to refactor; maybe create subpredicates in CoordinationSystem to reuse here?
module BlockCoordinationSystem
{
  import opened Options
  import opened MapRemove_s
  import opened MsgHistoryMod
  import opened LSNMod
  import opened KeyType
  import opened ValueMessage
  import opened TotalKMMapMod
  import opened CrashTolerantMapSpecMod
  import opened StampedMapMod
  import opened MarshalledJournal
  import opened GenericDisk
  import opened AbstractMap

  import Async = CrashTolerantMapSpecMod.uiopifc.async
  type UIOp = CrashTolerantMapSpecMod.uiopifc.UIOp
  type SyncReqs = map<CrashTolerantMapSpecMod.uiopifc.SyncReqId, LSN>

  // This DiskImage corresponds to the datatype by the same name way up at the
  // CoordinationSystem layer. In the implementation it represents the superblock
  // and all the blocks reachable from the superblock.
  datatype DiskImage = DiskImage(
    mapadt: StampedMap,
    journal: JournalImage)
  {
    predicate WF() {
      && journal.WF()
    }

    function SeqEnd() : LSN
      requires WF()
    {
      journal.SeqEnd()
    }

    predicate CompletesSync(lsn: LSN)
      requires WF()
    {
      lsn < SeqEnd()
    }
  }

  datatype Ephemeral =
    | Unknown
    | Known(
      progress: Async.EphemeralState,
      syncReqs: SyncReqs,

      mapadt: AbstractMap.Variables,
      mapLsn: LSN,  // invariant: agrees with mapadt.stampedMap.seqEnd
      journal: MarshalledJournal.Variables,

      frozenMap: Option<StampedMap>
    )
  {
    predicate WF() {
      Known? ==> (
        && true
      )
    }
  }

  datatype Variables = Variables(
    persistentImage: DiskImage,
    ephemeral: Ephemeral,
    inFlightImage: Option<DiskImage>
  )
  {
    predicate WF() {
      && persistentImage.WF()
      && (ephemeral.Known? ==> ephemeral.WF())
      && (inFlightImage.Some? ==> inFlightImage.value.WF())
    }
  }

  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && uiop.NoopOp?
    && v.ephemeral.Unknown?
    && v'.ephemeral.Known?
    && MarshalledJournal.Init(v'.ephemeral.journal, v.persistentImage.journal)
    && AbstractMap.Init(v'.ephemeral.mapadt, v.persistentImage.mapadt)
    && v' == v.(ephemeral := Known(
      Async.InitEphemeralState(),
      map[],  // syncReqs
      v'.ephemeral.mapadt, // defined by predicate update update
      v.persistentImage.mapadt.seqEnd,
      v'.ephemeral.journal, // defined by predicate update update
      None  // frozen map
      ))
  }

  // Move some journal state into the map to make it (closer to) fresh
  predicate Recover(v: Variables, v': Variables, uiop : UIOp, puts:MsgHistory)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v'.WF()
    && v'.ephemeral.Known?

    && puts.WF()

    // NB that Recover can interleave with mapadt steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.ReadForRecoveryLabel(puts))
    && AbstractMap.Put(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.PutLabel(puts))
    && v' == v.(ephemeral := v.ephemeral.(
        journal := v'.ephemeral.journal, // predicate update above
        mapadt := v'.ephemeral.mapadt,   // predicate update above
        mapLsn := puts.seqEnd
      ))
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
    // Map handles the query
    && AbstractMap.Query(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.QueryLabel(v.ephemeral.mapLsn, key, value))
    // Journal confirms that the map is up-to-date (but otherwise doesn't do anything).
    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))
    && v' == v.(ephemeral := v.ephemeral.(
        mapadt := v'.ephemeral.mapadt,  // predicate update above
        journal := v'.ephemeral.journal,  // predicate update above
        progress := v.ephemeral.progress.(
          requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
          replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
      )))
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
    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.PutLabel(singleton))
    && AbstractMap.Next(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.PutLabel(singleton))
    && v' == v.(ephemeral := v.ephemeral.(
          journal := v'.ephemeral.journal,  // predicate update above
          mapadt := v'.ephemeral.mapadt,  // predicate update above
          mapLsn := v.ephemeral.mapLsn + 1,
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
  // all look like no-ops ("stutter" in Lamport's TLA+ terminology) at this layer.

  predicate JournalInternal(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.InternalLabel())
    && v' == v.(ephemeral := v.ephemeral.(
          journal := v'.ephemeral.journal))  // predicate update above
  }

  predicate MapInternal(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.NoopOp?
    && AbstractMap.Next(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.InternalLabel())
    && v' == v.(ephemeral := v.ephemeral.(
          mapadt := v'.ephemeral.mapadt))  // predicate update above
  }

  predicate ReqSync(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && uiop.ReqSyncOp?
    && uiop.syncReqId !in v.ephemeral.syncReqs
    // Need to record the current LSN, which is generally the current map state. But we
    // also need to confirm that the journal hasn't gone ahead, since sync is relative to
    // writes (which have affected the journal).
    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.QueryEndLsnLabel(v.ephemeral.mapLsn))
    && AbstractMap.Next(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.QueryEndLsnLabel(v.ephemeral.mapLsn))

    // NB that the label for a sync in the table is the LSN AFTER the last write
    && v' == v.(ephemeral := v.ephemeral.(
        journal := v'.ephemeral.journal,  // predicate update above
        mapadt := v'.ephemeral.mapadt,  // predicate update above
        syncReqs := v.ephemeral.syncReqs[uiop.syncReqId := v.ephemeral.mapLsn]
      ))
  }

  predicate ReplySync(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v.ephemeral.Known?
    && uiop.ReplySyncOp?
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
    && v'.ephemeral.Known?
    // Copy the current map into the frozen one, deleting whatever was
    // frozen.
    && v'.ephemeral.frozenMap.Some?
    && AbstractMap.FreezeAs(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.FreezeAsLabel(v'.ephemeral.frozenMap.value))
    // TODO this should cause mischief if a Commit is in progress. Does it?
    && v' == v.(ephemeral := v.ephemeral.(
        mapadt := v'.ephemeral.mapadt,  // predicate update above
        frozenMap := v'.ephemeral.frozenMap  // predicate update above
      ))
  }

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, frozenJournal: JournalImage)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && v'.ephemeral.Known?
    && v.inFlightImage.None?

    && v.ephemeral.frozenMap.Some?
    && frozenJournal.WF()
    && v.ephemeral.frozenMap.value.seqEnd == frozenJournal.SeqStart()
    // Frozen map can't go backwards vs persistent map, lest we end up with
    // a gap to the ephemeral journal start.
    && v.persistentImage.mapadt.seqEnd <= frozenJournal.SeqStart()
    // And of course there should be no way for it to have passed the ephemeral map!
    && frozenJournal.SeqStart() <= v.ephemeral.mapLsn
    && v.persistentImage.SeqEnd() <= frozenJournal.SeqEnd()

    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal,
        MarshalledJournal.FreezeForCommitLabel(frozenJournal))
    && AbstractMap.Next(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.QueryEndLsnLabel(v.ephemeral.mapLsn))

    && v'.inFlightImage.Some?
    && v' == v.(
        ephemeral := v.ephemeral.(mapadt := v'.ephemeral.mapadt),  // predicate update above
        inFlightImage := Some(DiskImage(v.ephemeral.frozenMap.value, frozenJournal)))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.WF()
    && v'.WF()
    && v.ephemeral.Known?
    && v.inFlightImage.Some?
    && var ifImage := v.inFlightImage.value;

    && uiop.SyncOp?
    && v'.ephemeral.Known?

    && MarshalledJournal.Next(v.ephemeral.journal, v'.ephemeral.journal,
        MarshalledJournal.DiscardOldLabel(ifImage.mapadt.seqEnd, v.ephemeral.mapLsn))
    && AbstractMap.Next(v.ephemeral.mapadt, v'.ephemeral.mapadt, AbstractMap.QueryEndLsnLabel(v.ephemeral.mapLsn))

    && v' == v.(
        persistentImage := ifImage,
        ephemeral := v.ephemeral.(
          journal := v'.ephemeral.journal, // predicate update above
          mapadt := v'.ephemeral.mapadt    // predicate update above
        ),
        inFlightImage := None)
  }

  predicate Crash(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.CrashOp?
    && v' == v.(ephemeral := Unknown, inFlightImage := None)
  }

  function MkfsDiskImage() : DiskImage
  {
    DiskImage(StampedMapMod.Empty(), MarshalledJournal.Mkfs())
  }

  predicate Init(v: Variables)
  {
    && v.persistentImage == MkfsDiskImage()
    && v.ephemeral.Unknown?
    && v.inFlightImage.None?
  }

  datatype Step =
    | LoadEphemeralFromPersistentStep()
    | RecoverStep(puts:MsgHistory)
    | AcceptRequestStep()
    | QueryStep()
    | PutStep()
    | DeliverReplyStep()
    | JournalInternalStep()
    | MapInternalStep()
    | ReqSyncStep()
    | ReplySyncStep()
    | FreezeMapAdtStep()
    | CommitStartStep(frozenJournal: JournalImage)
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
      case FreezeMapAdtStep() => FreezeMapAdt(v, v', uiop)
      case CommitStartStep(frozenJournal) => CommitStart(v, v', uiop, frozenJournal)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
      case CrashStep() => Crash(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}