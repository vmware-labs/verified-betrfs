// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../lib/Base/MapRemove.s.dfy"
include "MsgHistory.i.dfy"

module CoordinatedMapJournalMod {
  // This module models how the program coordinates interactions between a map
  // datatype (an abstraction of the B^epsilon tree) and a journal. Here we
  // abstract away both data structures to simple models. This state machine
  // models the entire system, not just the program: it models the disk state,
  // program memory state, in-flight disk writes for the superblock, and
  // crashes.

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
  type Journal = MsgHistory
  type MapAdt = StampedMapMod.StampedMap

  function JournalMkfs() : Journal
  {
    MsgHistoryMod.EmptyHistory
  }

  function MapAdtMkfs() : MapAdt {
    StampedMapMod.Empty()
  }

  function SeqEndFor(lsn: LSN, journal: Journal) : LSN
  {
      if journal.EmptyHistory? then lsn else journal.seqEnd
  }

  // An image of the quiescent disk. The persistent state is this (because we
  // come up from shutdown to see a quiescent disk image). The in-flight state
  // is also a DiskImage, since it's destined to become a persistent state.
  datatype DiskImage = DiskImage(
      mapadt: MapAdt,
      journal: Journal)
  {
    predicate WF()
    {
      && journal.WF()
        // No point even assembling a disk image that doesn't have its journal adjacent to its map.
      && journal.CanFollow(mapadt.seqEnd)
    }

    function SeqEnd() : LSN
    {
      SeqEndFor(mapadt.seqEnd, journal)
    }

    predicate CompletesSync(lsn: LSN)
    {
      lsn < SeqEnd()
    }
  }

  function MkfsDiskImage() : DiskImage
  {
    DiskImage(MapAdtMkfs(), JournalMkfs())
  }

  type SyncReqs = map<CrashTolerantMapSpecMod.SyncReqId, LSN>

  // In-memory state. It may be unknown if we've just booted and haven't
  // read anything off the disk.
  datatype Ephemeral =
    | Unknown
    | Known(
      // the requests and responses of uiops
      progress: Async.EphemeralState,

      // Same idea for sync reqs (which get layered after Async reqs/resps)
      syncReqs: SyncReqs,

      // The journal
      journal: Journal,

      // The map that enables journal beheading.
      // Note that, here in the ephemeral object, (mapadt,journal) don't form a
      // DiskImage. In a DiskImage, they work in serial: the journal starts
      // where the map left off. In the ephemeral state, they work in parallel:
      // the mapadt captures the effects of all the LSNs that the journal records (plus
      // those in the persistent map the ephemeral journal is based on).
      mapadt: MapAdt,

      // The prefix of the journal that's persisted and hence can be
      // copied into an inFlightImage.
      frozenJournalLSN: LSN,

      // If Some, .value is persisted and can be copied into an
      // inFlightImage.
      frozenMap: Option<MapAdt>
      )
  {
    predicate WF()
    {
      Known? ==> journal.WF()
    }

    function SeqEnd() : LSN
      requires Known?
    {
      SeqEndFor(mapadt.seqEnd, journal)
    }
  }

  datatype Variables = Variables(
    persistentImage: DiskImage,       // represents the persistent disk state reachable from superblock
    ephemeral: Ephemeral,             // represents the in-memory filesystem state
    inFlightImage: Option<DiskImage>  // represents an in-flight disk I/O request to the superblock
  )
  {
    predicate WF()
    {
      && persistentImage.WF()
      && (ephemeral.Known? ==> ephemeral.WF())
      && (inFlightImage.Some? ==> inFlightImage.value.WF())
    }

    // How should the disk look on first startup if we want it to act like
    // an empty K-V store?
    predicate Mkfs()
    {
      && persistentImage == MkfsDiskImage()
      && ephemeral.Unknown?
      && inFlightImage.None?
    }

  }

  // Since this state machine is an abstraction of the entire IOSystem (including
  // disk and crashes), this Init is the Mkfs() step. Reboots (where RAM is cleared
  // but disk state remains) appear elsewhere.
  predicate Init(v: Variables)
  {
    v.Mkfs()
  }

  // This operation corresponds to faulting in the superblock: before we do, we
  // have to get our interpretation only from the disk; once we do, we can fill
  // in the ephemeral state and interpret it (with the rest of the disk as
  // backing store) as if we're in normal operating mode.
  // (In the next layer down, we don't bring *all* the persistent state into
  // ephemeral RAM, but the proof can still refine by filling the details from
  // the disk state.)
  predicate LoadEphemeralFromPersistent(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.ephemeral.Unknown?
    && v' == v.(ephemeral := Known(
      Async.InitEphemeralState(),
      map[],  // syncReqs
      v.persistentImage.journal,
      v.persistentImage.mapadt,
      // persistent journal is already frozen:
      if v.persistentImage.journal.EmptyHistory? then 0 else v.persistentImage.journal.seqEnd,
      None
      ))
  }

  // The ephemeral map and ephemeral journal are at the same lsn, which only happens
  // after recovery has "caught the map up" to the journal.
  predicate MapIsFresh(v: Variables)
  {
    && v.WF()
    && v.ephemeral.Known?
    && (v.ephemeral.journal.MsgHistory? ==> v.ephemeral.journal.seqEnd == v.ephemeral.mapadt.seqEnd)
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
    && v.ephemeral.journal.IncludesSubseq(puts)

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
          journal := v.ephemeral.journal.Concat(singleton),
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

  predicate FreezeJournal(v: Variables, v': Variables, uiop : UIOp, newFrozenLSN: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    // Freezin' only goes forward.
    && v.ephemeral.frozenJournalLSN < newFrozenLSN
    // ephemeral journal actually includes all the proposed-frozen stuff
    && v.ephemeral.journal.CanDiscardTo(newFrozenLSN)
    && v' == v.(ephemeral := v.ephemeral.(frozenJournalLSN := newFrozenLSN))
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

  function BestFrozenState(v: Variables) : (odi:Option<DiskImage>)
    requires v.WF()
    requires v.ephemeral.Known?
    ensures odi.Some? ==> odi.value.WF()
  {
    if
      // no frozen map to write
      || v.ephemeral.frozenMap.None?
      || var frozenMap := v.ephemeral.frozenMap.value;
      // frozen journal is useless
      || !(frozenMap.seqEnd < v.ephemeral.frozenJournalLSN) // TODO(robj): why not remove this case?
      // frozen LSN is out of bounds for the actual joural it's pointing to
      || !v.ephemeral.journal.CanDiscardTo(v.ephemeral.frozenJournalLSN)
      // or has been beheaded beyond the frozen tree
      || !v.ephemeral.journal.CanDiscardTo(frozenMap.seqEnd)
      // or frozen state loses information
      || !(v.persistentImage.SeqEnd() <= v.ephemeral.frozenJournalLSN)
      // or frozen map goes backwards, so if we committed it, we could have a
      // gap to our ephemeral journal start
      || !(v.persistentImage.mapadt.seqEnd <= frozenMap.seqEnd)
    then None
    else
      // Use frozen map and available frozen journal.
      var frozenJournal := v.ephemeral.journal
        .DiscardRecent(v.ephemeral.frozenJournalLSN)
        .DiscardOld(v.ephemeral.frozenMap.value.seqEnd);
      Some(DiskImage(v.ephemeral.frozenMap.value, frozenJournal))
  }

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, seqBoundary: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && BestFrozenState(v).Some?
    // Have to go forwards in LSN time
    && NextLSN(v) < BestFrozenState(v).value.SeqEnd()
    && v.inFlightImage.None?
    && v'.inFlightImage.Some?
    && v' == v.(inFlightImage := BestFrozenState(v))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.inFlightImage.Some?
    && var ifImage := v.inFlightImage.value;

    && uiop.SyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.

    // pruning below is nonsense without this, but "luckily" this is an invariant:
    && v.ephemeral.journal.CanDiscardTo(ifImage.mapadt.seqEnd)

    // Now that the disk journal is updated, we need to behead the
    // ephemeral journal, since interpretation want to CanFollow it
    // onto the persistent mapadt.
    && var j' := v.ephemeral.journal.DiscardOld(ifImage.mapadt.seqEnd);

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
    | FreezeJournalStep(newFrozenLSN: LSN)
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
      case FreezeJournalStep(newFrozenLSN) => FreezeJournal(v, v', uiop, newFrozenLSN)
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
