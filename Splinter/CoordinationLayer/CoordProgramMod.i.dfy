// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "JournalInterp.i.dfy"
include "../../Spec/Interp.s.dfy"
include "../../lib/Base/KeyType.s.dfy"

module ProgramMachineMod {
  import opened Options
  import InterpMod
  import JournalInterpTypeMod
  import opened CrashTolerantMapSpecMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
//  import opened SequenceSetsMod
//  import D = AsyncDisk  // Importing for the interface, not the entire disk

  type UIOp = CrashTolerantMapSpecMod.UIOp
  type Journal = JournalInterpTypeMod.Variables
  type MapAdt = InterpMod.Interp

  // Persistent state of disk
  datatype Superblock = Superblock(
    journal: Journal,
    mapadt: MapAdt)
  {
    predicate WF()
    {
      && journal.WF()
    }
  }

  datatype Phase = SuperblockUnknown | ReplayingJournal | Running

  function MapAdtMkfs() : MapAdt {
    InterpMod.Empty()
  }

  datatype Variables = Variables(
    phase: Phase,
    stableSuperblock: Superblock,
    journal: Journal,
    mapadt: MapAdt,
    inFlightSuperblock: Option<Superblock>
    )
  {
    predicate WF()
    {
      && stableSuperblock.WF()
      && journal.WF()
      && (inFlightSuperblock.Some? ==> inFlightSuperblock.value.WF())
    }

    // How should the disk look on first startup if we want it to act like
    // an empty K-V store?
    predicate Mkfs()
    {
      && phase == SuperblockUnknown
      && stableSuperblock == Superblock(
        JournalInterpTypeMod.Mkfs(),
        MapAdtMkfs())
      // Don't care about journal, mapadt
      && inFlightSuperblock.None?
    }

  }

  // Initialization of the program, which happens at the beginning but also after a crash.
  // Phase SuperblockUnknown means we get the interpretation straight from the disk.
  predicate Init(v: Variables)
  {
    && v.phase.SuperblockUnknown?
    // Journal and Betree get initialized once we know their superblocks
  }

  // Now we know what the disk superblock says, and we can initialize the Journal, Tree Variables.
  // They'll still not be ready to go, so they'll probably defer Interpretation to the disk,
  // but *we* don't have to know that.
  predicate LearnSuperblock(v: Variables, v': Variables)
  {
    // not sure what this means yet.
    false
  }

  predicate Recover(v: Variables, v': Variables, uiop : UIOp, puts:MsgSeq)
  {
    && v.WF()
    && v'.WF()
    && v.phase.ReplayingJournal?
    && puts.WF()
    && puts.seqStart == v.mapadt.seqEnd
    && v.journal.msgSeq.IncludesSubseq(puts)

    // NB that Recover can interleave with mapadt steps (the Betree
    // reorganizing its state, possibly flushing stuff out to disk).
    && v' == v.(mapadt := MsgHistoryMod.Concat(v.mapadt, puts))
  }

  // Once we've brought the tree up-to-date with respect to the journal,
  // we can enter normal operations.
  // Interpretation goes to the Tree's variables. (It could point to the
  // Journal, too, since their ephemeral views are kept synchronized -- but if
  // we ever want to support a mode where we abandon the Journal during long
  // periods of no sync requests, we need to use the Tree.)
  predicate CompleteRecovery(v: Variables, v': Variables)
  {
    && v.phase.ReplayingJournal?
    && v.mapadt.seqEnd == v.journal.msgSeq.seqStart

    && v' == v.(phase := Running)
  }

  predicate Query(v: Variables, v': Variables, uiop : UIOp, key: Key, val: Value)
  {
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.GetInput? // ensures that the uiop translates to a Get op
    && v.phase.Running?
    && v.WF()
    && val == v.mapadt.mi[key].value
    && v' == v  // TODO update new reqs/resps fields to record retirement of uiop
  }

  // No analog to cacheop, I think.

  predicate Put(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.PutInput? // ensures that the uiop translates to a put op
    && var key := uiop.baseOp.req.input.k;
    && var val := uiop.baseOp.req.input.v;
    // This is an invariant, but we're not allowed to even express this step
    // without so constraining it.
    && v.journal.msgSeq.seqEnd == v.mapadt.seqEnd
    && var singleton :=
        MsgHistoryMod.Singleton(v.mapadt.seqEnd, KeyedMessage(key, Define(val)));

    && v.phase.Running?
    && v.WF()
    && v' == v.(
      journal := v.journal.(msgSeq := v.journal.msgSeq.Concat(singleton)),
      mapadt := MsgHistoryMod.Concat(v.mapadt, singleton)
      )
  }

  // TODO Inteprereted data model doesn't leave much room to model Journal
  // or Betree *internal* steps, because they're noops at the interp layer.
  // Should we capture that here, maybe with a "secret" field of the mapadt,
  // representing its internal representation, that can change but the mapadt
  // interp stays unchanged?
  // One bit of mapadt internal state might be the frozen interp.
  // One bit of journal internal state might be the how much is known to be clean.

  // predicate JournalInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: JournalMachineMod.Skolem)
  // predicate SplinterTreeInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: SplinterTreeMachineMod.Skolem)

  predicate ReqSync(v: Variables, v': Variables, uiop : UIOp, syncReqId: SyncReqId)
  {
    && uiop == ReqSyncOp(syncReqId)
    && v.phase.Running?
    && v.WF()
    && JournalInterpTypeMod.ReqSync(v.journal, v'.journal, syncReqId)
    && v' == v.(journal := v'.journal)  // unchanged except journal changes as specified above
  }

  predicate CompleteSync(v: Variables, v': Variables, uiop : UIOp, syncReqId: SyncReqId)
  {
    && uiop == CompleteSyncOp(syncReqId)
    && v.phase.Running?
    && v.WF()
    && JournalInterpTypeMod.CompleteSync(v.journal, v'.journal, syncReqId)
    && v' == v.(journal := v'.journal)  // unchanged except journal changes as specified above
  }

  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, seqBoundary: LSN)
  {
    && uiop.NoopOp?
    && v.phase.Running?
    && v.inFlightSuperblock.None?
    && v'.inFlightSuperblock.Some?
    && var sb := Superblock(v.journal, v.mapadt);
    && v' == v.(inFlightSuperblock := Some(sb))
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.phase.Running?
    && v.inFlightSuperblock.Some?

    && var sb := v.inFlightSuperblock.value;
    && v' == v.(
        stableSuperblock := sb,
        // Update journal, mapadt here if modeling clean, frozen
        inFlightSuperblock := None)
  }

  datatype Step =
    | RecoverStep(puts:MsgSeq)
    | QueryStep(key: Key, val: Value)
    | PutStep()
//    | JournalInternalStep()
//    | SplinterTreeInternalStep()
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)
    | CommitStartStep(seqBoundary: LSN)
    | CommitCompleteStep()

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, step: Step) {
    && match step {
      case RecoverStep(puts) => Recover(v, v', uiop, puts)
      case QueryStep(key, val) => Query(v, v', uiop, key, val)
      case PutStep() => Put(v, v', uiop)
//      case JournalInternalStep(sk) => JournalInternal(v, v', uiop, cacheOps, sk)
//      case SplinterTreeInternalStep(sk) => SplinterTreeInternal(v, v', uiop, cacheOps, sk)
      case ReqSyncStep(syncReqId) => ReqSync(v, v', uiop, syncReqId)
      case CompleteSyncStep(syncReqId) => CompleteSync(v, v', uiop, syncReqId)
      case CommitStartStep(seqBoundary) => CommitStart(v, v', uiop, seqBoundary)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp) {
    exists step :: NextStep(v, v', uiop, step)
  }
}
