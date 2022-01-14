// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "../../Spec/Interp.s.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../../lib/Base/MapRemove.s.dfy"
include "../MsgHistory.i.dfy"

module CoordProgramMod {
  import opened Options
  import opened MapRemove_s
  import InterpMod
  import opened CrashTolerantMapSpecMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage

  import Async = CrashTolerantMapSpecMod.async

  type UIOp = CrashTolerantMapSpecMod.UIOp
  type Journal = MsgSeq
  type MapAdt = InterpMod.Interp

  function JournalMkfs() : Journal
  {
    MsgHistoryMod.Empty()
  }

  function MapAdtMkfs() : MapAdt {
    InterpMod.Empty()
  }

  function SeqEndFor(lsn: LSN, journal: Journal) : LSN
  {
      if journal.IsEmpty() then lsn else journal.seqEnd
  }

  // Persistent state of disk
  datatype Superblock = Superblock(
      journal: Journal,
      mapadt: MapAdt)
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
    Superblock(JournalMkfs(), MapAdtMkfs())
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
    persistentSuperblock: Superblock,
    ephemeral: Ephemeral,
    inFlightSuperblock: Option<Superblock>)
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
  predicate LoadEphemeralState(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.ephemeral.Unknown?
    && v' == v.(ephemeral := Known(
      Async.InitEphemeralState(),
      map[],  // syncReqs
      v.persistentSuperblock.journal,
      v.persistentSuperblock.journal.seqEnd, // this journal is frozen.
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
    && v.ephemeral.mapadt.seqEnd == v.ephemeral.journal.seqEnd
  }

  function NextLSN(v: Variables) : LSN
    requires MapIsFresh(v)
  {
    v.ephemeral.mapadt.seqEnd
  }

  // Move some journal state into the map to make it (closer to) fresh
  predicate Recover(v: Variables, v': Variables, uiop : UIOp, puts:MsgSeq)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    && !MapIsFresh(v)
    && v'.WF()

    && puts.WF()
    && puts.seqStart == v.ephemeral.mapadt.seqEnd
    && v.ephemeral.journal.IncludesSubseq(puts)

    // NB that Recover can interleave with mapadt steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && v' == v.(ephemeral := v.ephemeral.(mapadt := MsgHistoryMod.Concat(v.ephemeral.mapadt, puts)))
  }

  predicate Query(v: Variables, v': Variables, uiop : UIOp, key: Key, val: Value)
  {
    && MapIsFresh(v)
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.GetInput? // ensures that the uiop translates to a Get op
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id
    && val == v.ephemeral.mapadt.mi[key].value
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
    && uiop.baseOp.req in v.ephemeral.progress.requests
    && uiop.baseOp.reply.id == uiop.baseOp.req.id
 
    && var key := uiop.baseOp.req.input.k;
    && var val := uiop.baseOp.req.input.v;

    && var singleton :=
        MsgHistoryMod.Singleton(NextLSN(v), KeyedMessage(key, Define(val)));

    && v.WF()
    && v' == v.(ephemeral := v.ephemeral.(
          journal := v.ephemeral.journal.Concat(singleton),
          mapadt := MsgHistoryMod.Concat(v.ephemeral.mapadt, singleton),
          // Frozen stuff unchanged here.
          progress := v.ephemeral.progress.(
            requests := v.ephemeral.progress.requests - {uiop.baseOp.req},
            replies := v.ephemeral.progress.replies + {uiop.baseOp.reply}
          )
      ))
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
    // NB that the label for a sync in the table is the LSN AFTER the last write
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := v.ephemeral.syncReqs[uiop.syncReqId := NextLSN(v)]
      ))
  }

  predicate CompleteSync(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.CompleteSyncOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.
    && uiop.syncReqId in v.ephemeral.syncReqs
    && v.persistentSuperblock.CompletesSync(v.ephemeral.syncReqs[uiop.syncReqId]) // sync lsn is persistent
    && v' == v.(ephemeral := v.ephemeral.(
        syncReqs := MapRemove1(v.ephemeral.syncReqs, uiop.syncReqId)
      ))
  }

  function BestFrozenState(v: Variables) : (sb:Superblock)
    requires v.WF()
    requires v.ephemeral.Known?
    ensures sb.WF()
  {
    if
      // no frozen map to write
      || v.ephemeral.frozenMap.None?
    then MkfsSuperblock()
    else if
      // frozen journal is useless
      || !(v.ephemeral.frozenMap.value.seqEnd < v.ephemeral.frozenJournalLSN)
      // frozen LSN is out of bounds for the actual joural it's pointing to
      || !v.ephemeral.journal.CanPruneTo(v.ephemeral.frozenJournalLSN)
      // or has been beheaded beyond the frozen tree
      || !v.ephemeral.journal.CanPruneTo(v.ephemeral.frozenMap.value.seqEnd)
    then
      // Could actually just use the frozen map here, but we don't really care
      // to support this case; this is a silly branch in that it's never
      // invoked in any Inv()-preserving behavior.
      // Superblock(v.ephemeral.frozenMap.value, JournalInterpTypeMod.Mkfs())
      MkfsSuperblock()
    else
      // Use frozen map and available frozen journal.
      var frozenJournal := v.ephemeral.journal
        .PruneTail(v.ephemeral.frozenJournalLSN)
        .PruneHead(v.ephemeral.frozenMap.value.seqEnd);
      Superblock(frozenJournal, v.ephemeral.frozenMap.value)
  }

  predicate FreezeJournal(v: Variables, v': Variables, uiop : UIOp, newFrozenLSN: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    // Freezin' only goes forward.
    && v.ephemeral.frozenJournalLSN < newFrozenLSN <= v.ephemeral.journal.seqEnd
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

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, seqBoundary: LSN)
  {
    && uiop.NoopOp?
    && v.WF()
    && v.ephemeral.Known?
    // Have to go forwards in LSN time
    && v.ephemeral.mapadt.seqEnd < BestFrozenState(v).journal.seqEnd
    && v.inFlightSuperblock.None?
    && v'.inFlightSuperblock.Some?
    && v' == v.(inFlightSuperblock := Some(BestFrozenState(v)))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.SpontaneousCommitOp?
    && MapIsFresh(v) // Actually, v.ephemeral.Known? is sufficient here.
    && v.inFlightSuperblock.Some?

    && var sb := v.inFlightSuperblock.value;

    // Now that the disk journal is updated, we need to behead the
    // ephemeral journal, since interpretation want to CanFollow it
    // onto the persistent mapadt.
    && var j := v.ephemeral.journal;
    && var j' :=
      if j.CanPruneTo(sb.mapadt.seqEnd)
      then j.PruneHead(sb.mapadt.seqEnd)
      else j;    // Case never occurs, but need Inv to prove so.

    && v' == v.(
        persistentSuperblock := sb,
        ephemeral := v.ephemeral.(journal := j'),
        // Update journal, mapadt here if modeling clean, frozen
        inFlightSuperblock := None)
  }

  datatype Step =
    | LoadEphemeralStateStep()
    | RecoverStep(puts:MsgSeq)
    | QueryStep(key: Key, val: Value)
    | PutStep()
//    | JournalInternalStep()
//    | SplinterTreeInternalStep()
    | ReqSyncStep()
    | CompleteSyncStep()
    | FreezeJournalStep(newFrozenLSN: LSN)
    | FreezeMapAdtStep()
    | CommitStartStep(seqBoundary: LSN)
    | CommitCompleteStep()

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, step: Step) {
    match step {
      case LoadEphemeralStateStep() => LoadEphemeralState(v, v', uiop)
      case RecoverStep(puts) => Recover(v, v', uiop, puts)
      case QueryStep(key, val) => Query(v, v', uiop, key, val)
      case PutStep() => Put(v, v', uiop)
//      case JournalInternalStep(sk) => JournalInternal(v, v', uiop, cacheOps, sk)
//      case SplinterTreeInternalStep(sk) => SplinterTreeInternal(v, v', uiop, cacheOps, sk)
      case ReqSyncStep() => ReqSync(v, v', uiop)
      case CompleteSyncStep() => CompleteSync(v, v', uiop)
      case FreezeJournalStep(newFrozenLSN) => FreezeJournal(v, v', uiop, newFrozenLSN)
      case FreezeMapAdtStep() => FreezeMapAdt(v, v', uiop)
      case CommitStartStep(seqBoundary) => CommitStart(v, v', uiop, seqBoundary)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
