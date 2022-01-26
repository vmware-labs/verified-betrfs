// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../lib/Base/MapRemove.s.dfy"
include "MsgHistory.i.dfy"

module CoordProgramMod {
  import opened Options
  import opened MapRemove_s
  import StampedMapMod
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

  // TODO(jonh): rename "DiskImage"
  // Persistent state of disk
  datatype Superblock = Superblock(
      mapadt: MapAdt,
      journal: Journal)
  {
    predicate WF()
    {
      && journal.WF()
        // No point even assembling a superblock that doesn't have its journal adjacent to its map.
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

  function MkfsSuperblock() : Superblock
  {
    Superblock(MapAdtMkfs(), JournalMkfs())
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

      // The prefix of the journal that's persisted and hence can be
      // copied into an inFlightSuperblock.
      frozenJournalLSN: LSN,

      // The map that enables journal beheading.
      mapadt: MapAdt,

      // If Some, .value is persisted and can be copied into an
      // inFlightSuperblock.
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
    persistentSuperblock: Superblock,       // represents the persistent disk state reachable from superblock
    ephemeral: Ephemeral,                   // represents the in-memory filesystem state
    inFlightSuperblock: Option<Superblock>  // represents an in-flight disk I/O request to the superblock
  )
  {
    predicate WF()
    {
      && persistentSuperblock.WF()
      && (ephemeral.Known? ==> ephemeral.WF())
      && (inFlightSuperblock.Some? ==> inFlightSuperblock.value.WF())
    }

    // How should the disk look on first startup if we want it to act like
    // an empty K-V store?
    predicate Mkfs()
    {
      && persistentSuperblock == MkfsSuperblock()
      && ephemeral.Unknown?
      && inFlightSuperblock.None?
    }

  }

  // Since this state machine is an abstraction of the entire IOSystem (including
  // disk and crashes), this Init is the Mkfs() step. Reboots (where RAM is cleared
  // but disk state remains) appear elsewhere.
  predicate Init(v: Variables)
  {
    v.Mkfs()
  }

  // Learn what the persistent state is, so we 
  // (In the next layer down, we don't bring *all* the persistent state into
  // ephemeral RAM, but the proof can still refine by filling the details from
  // the disk state.)
  // TODO(jonh): rename LoadEphemeralFromPersistent
  predicate LoadEphemeralState(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.ephemeral.Unknown?
    && v' == v.(ephemeral := Known(
      Async.InitEphemeralState(),
      map[],  // syncReqs
      v.persistentSuperblock.journal,
      // sb journal is already frozen:
      if v.persistentSuperblock.journal.EmptyHistory? then 0 else v.persistentSuperblock.journal.seqEnd,
      v.persistentSuperblock.mapadt,
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
    && v.persistentSuperblock.CompletesSync(v.ephemeral.syncReqs[uiop.syncReqId]) // sync lsn is persistent
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

  function BestFrozenState(v: Variables) : (osb:Option<Superblock>)
    requires v.WF()
    requires v.ephemeral.Known?
    ensures osb.Some? ==> osb.value.WF()
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
      || !(v.persistentSuperblock.SeqEnd() <= v.ephemeral.frozenJournalLSN)
      // or frozen map goes backwards, so if we committed it, we could have a
      // gap to our ephemeral journal start
      || !(v.persistentSuperblock.mapadt.seqEnd <= frozenMap.seqEnd)
    then None
    else
      // Use frozen map and available frozen journal.
      var frozenJournal := v.ephemeral.journal
        .DiscardRecent(v.ephemeral.frozenJournalLSN)
        .DiscardOld(v.ephemeral.frozenMap.value.seqEnd);
      Some(Superblock(v.ephemeral.frozenMap.value, frozenJournal))
  }

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, seqBoundary: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && BestFrozenState(v).Some?
    // Have to go forwards in LSN time
    && NextLSN(v) < BestFrozenState(v).value.SeqEnd()
    && v.inFlightSuperblock.None?
    && v'.inFlightSuperblock.Some?
    && v' == v.(inFlightSuperblock := BestFrozenState(v))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && v.inFlightSuperblock.Some?
    && var sb := v.inFlightSuperblock.value;

    && uiop.SyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.

    // pruning below is nonsense without this, but "luckily" this is an invariant:
    && v.ephemeral.journal.CanDiscardTo(sb.mapadt.seqEnd)

    // Now that the disk journal is updated, we need to behead the
    // ephemeral journal, since interpretation want to CanFollow it
    // onto the persistent mapadt.
    && var j' := v.ephemeral.journal.DiscardOld(sb.mapadt.seqEnd);

    && v' == v.(
        persistentSuperblock := sb,
        ephemeral := v.ephemeral.(journal := j'),
        // Update journal, mapadt here if modeling clean, frozen
        inFlightSuperblock := None)
  }

  datatype Step =
    | LoadEphemeralStateStep()
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

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, step: Step) {
    match step {
      case LoadEphemeralStateStep() => LoadEphemeralState(v, v', uiop)
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
      // TODO Um, Crash!?
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
