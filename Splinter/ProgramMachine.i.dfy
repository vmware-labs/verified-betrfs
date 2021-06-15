// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"
include "JournalInterp.i.dfy"
include "SplinterTree.i.dfy"
include "SplinterTreeInterp.i.dfy"
include "CacheIfc.i.dfy"

include "AsyncDisk.s.dfy"
include "AsyncDiskProgram.s.dfy"
include "IOSystem.s.dfy"

// TODO first prove that a Program with a simple-policy cache works?

// The "Program" is the complete model of the program state, with all of the components
// (Journal, Betree, Cache).
// It has an interface to a disk, but can't actually see inside the disk (that's for the IOSystem).

module ProgramMachineMod {
  import AllocationTableMod
  import AllocationTableMachineMod
  import SplinterTreeMachineMod
  import JournalMachineMod
  import opened AllocationMod
  import opened DiskTypesMod
  import opened CrashTolerantMapSpecMod
  import opened InterpMod
  import opened MessageMod
  import opened MsgSeqMod
  import opened Options
  import CacheIfc
  import D = AsyncDisk  // Importing for the interface, not the entire disk

  type UIOp = CrashTolerantMapSpecMod.UIOp
  type DiskOp = D.DiskOp

  datatype Superblock = Superblock(
    serial: nat,
    journal: JournalMachineMod.Superblock,
    betree: SplinterTreeMachineMod.Superblock)

  function parseSuperblock(b: UninterpretedDiskPage) : Option<Superblock>

  function marshalSuperblock(sb: Superblock) : (b: UninterpretedDiskPage)
    ensures parseSuperblock(b) == Some(sb)

  function SUPERBLOCK_ADDRESS(): CU
  {
    CU(0, 0)
  }

  datatype Phase = SuperblockUnknown | RecoveringJournal | Running

  datatype Variables = Variables(
    phase: Phase,
    stableSuperblock: Superblock,
    cache: CacheIfc.Variables,
    journal: JournalMachineMod.Variables,
    betree: SplinterTreeMachineMod.Variables,
    inFlightSuperblock: Option<Superblock>
    )
  {
    predicate WF() {
      true
    }
  }

  // How should the disk look on first startup if we want it to act like
  // an empty K-V store?
  predicate Mkfs(dv: DiskView)
  {
    var initsb := Superblock(
      0,  // serial
      JournalMachineMod.MkfsSuperblock(),
      SplinterTreeMachineMod.MkfsSuperblock());
    && SUPERBLOCK_ADDRESS() in dv
    && parseSuperblock(dv[SUPERBLOCK_ADDRESS()]) == Some(initsb)
  }

  // Initialization of the program, which happens at the beginning but also after a crash.
  predicate Init(v: Variables)
  {
    && v.phase.SuperblockUnknown?
    && CacheIfc.Init(v.cache)
    // Journal and Betree get initialized once we know their superblocks
  }

  predicate LearnSuperblock(v: Variables, v': Variables, rawSuperblock: UninterpretedDiskPage, sk: JournalMachineMod.InitSkolems)
  {
    && CacheIfc.Read(v.cache, SUPERBLOCK_ADDRESS(), rawSuperblock)
    && var superblock := parseSuperblock(rawSuperblock);
    && superblock.Some?

    && v'.phase.RecoveringJournal?
    && v'.stableSuperblock == superblock.value
    && v'.cache == v.cache  // no cache writes
    && JournalMachineMod.Init(v'.journal, superblock.value.journal, v.cache, sk)
    && SplinterTreeMachineMod.Start(v.betree, v'.betree, v.cache, superblock.value.betree)
    && v'.inFlightSuperblock.None?
  }

  predicate Recover(v: Variables, v': Variables, uiop : UIOp, puts:MsgSeq, newbetree: SplinterTreeMachineMod.Variables)
  {
    && v.phase.RecoveringJournal?
    && puts.WF()
    && puts.seqStart == v.betree.BetreeEndsLSNExclusive()
    && puts.seqStart + |puts.msgs| <= v.journal.JournalBeginsLSNInclusive()
    && JournalMachineMod.MessageSeqMatchesJournalAt(v.journal, puts)

    // NB that Recover can interleave with BetreeInternal steps, which push stuff into the
    // cache to flush it out of the Betree's membuffer to make room for more recovery.

    && SplinterTreeMachineMod.PutMany(v.betree, newbetree, puts)
    && v' == v.(betree := newbetree)
  }

  predicate CompleteRecovery(v: Variables, v': Variables)
  {
    && v.phase.RecoveringJournal?
    // We've brought the tree up-to-date with respect to the journal, so
    // we can enter normal operations
    && v.betree.BetreeEndsLSNExclusive() == v.journal.JournalBeginsLSNInclusive()

    && v' == v.(phase := Running)
  }

  predicate Query(v: Variables, v': Variables, uiop : UIOp, key: Key, val: Value, sk: SplinterTreeMachineMod.Skolem)
  {
    && v.phase.Running?
    && v.WF()
    && v'.journal == v.journal
    && SplinterTreeMachineMod.Query(v.betree, v'.betree, v.cache, key, val, sk)
    && v'.cache == v.cache  // no cache writes
    && v'.stableSuperblock == v.stableSuperblock
  }

  // TODO: Dops go here, cache interactions with the disk
  predicate CacheOp(v: Variables, v': Variables)
  {
    && v.WF()
    && v'.journal == v.journal
    && v'.betree == v.betree
    && true // Cache.OrganizeThyself(...)
    && v'.stableSuperblock == v.stableSuperblock
  }


  predicate Put(v: Variables, v': Variables, uiop : UIOp, sk: SplinterTreeMachineMod.Skolem)
  {
    && uiop.OperateOp?
    && uiop.baseOp.ExecuteOp?
    && uiop.baseOp.req.input.PutInput? // ensures that the uiop translates to a put op
    && var key := uiop.baseOp.req.input.k;
    && var val := uiop.baseOp.req.input.v;
    && v.phase.Running?
    && v.WF()
    && JournalMachineMod.Append(v.journal, v'.journal, MessagePut(key, val))  // only writes to heap
    && SplinterTreeMachineMod.Put(v.betree, v'.betree, key, val, sk)  // only writes to heap
    // Note that Put only adds the write to the journal's unmarshalled tail. So the cache doesn't change
    // The upddates from the unmarshalled tail are pushed into the cache in batches in a later journal internal step.
    && v'.cache == v.cache  // no cache writes
    && v'.stableSuperblock == v.stableSuperblock

  }

  // TODO move to Sets.i
  predicate SetsMutuallyDisjoint<T>(sets: seq<set<T>>) {
    forall i, j | 0<=i<|sets| && 0<=j<|sets| && i!=j :: sets[i] !! sets[j]
  }

  // Ensures that the journal's betree's allocations are dijoint ... aka use disjoint regions of the cache
  predicate AllocsDisjoint(v: Variables)
  {
    SetsMutuallyDisjoint([
      {SUPERBLOCK_ADDRESS()},
      JournalMachineMod.Alloc(v.journal),
      SplinterTreeMachineMod.Alloc(v.betree, v.cache, v.stableSuperblock.betree)
      ])
  }

  // ensures that writes are within the allcation of the specfic subsystem (journal/betree)
  predicate WritesOkay(cacheOps: CacheIfc.Ops, alloc: set<CU>)
  {
    forall op | op in cacheOps :: op.cu in alloc
  }

  // How do the subsystems negotiate for more alloc?
  // They're always free to write into their existing alloc -- Journal is going to want
  // to do that all the time, maintaining its own internal allocation tracker, to avoid
  // writing out new allocation bitmap summaries. In principle, Journal can ask to grow
  // its alloc.
  // Betree, on the other hand: it's gonna alloc all the darn time. We need to make
  // sure that when it does, the new AUs are disjoint with our alloc (the superblocks)
  // and the Journal's existing alloc.
  // So how do we record each system's current alloc?
  // Do subsystems "know" their current alloc? I guess they do, ghostily --
  // when BeTree.B+tree links a new AU into an in-progress B+tree, it claims another AU,
  // and updates its ghost alloc -- oh, that's just a function over all reachable state on
  // disk!
  // At sb time, that's the alloc it publishes to a marshalled alloc record on the disk.
  // (Do we need to do that here, if the physical thing isn't gonna do that? Hrm.)
  // So at Journal-alloc time, we just test against the betree's ghost alloc?
  //
  // The real system would have ghost views of subsystem allocs, a single physical alloc bitmap,
  // and an invariant that the physical alloc bitmap is the union of the ghosty ones.
  // NO that's not right! They need separate allocs so they can record them precisely (and
  // separately, since they update out of sync), so that crashes correctly reflect what has
  // changed.
  // Well, maybe they don't need to be recorded separately. Maybe it's okay if the sb always
  // points to a single alloc that's an precise union of the underlying subsystems.
  // When journal wants to grow, it allocates AU from the central allocator.
  // When Betree wants to grow, it allocates AU from the central allocator.
  // These only affect in-memory state.
  // When sb commits, it includes the state of ... uh oh, which betree? Ephemeral or frozen?
  // so I guess we need to track them separately, so that we can record the frozen's allocation
  // to the sb, while still tracking the ephemeral alloc in memory (for next freeze).
  // At that point we COULD write frozen-alloc UNION journal-alloc to the sb, but is that
  // a false economy? I guess not -- we have to coordinate across subsystems, and they share
  // an invariant that makes them reduntant anyway. Hrmm.

  predicate JournalInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: JournalMachineMod.Skolem)
  {
    && uiop.NoopOp?
    && v.WF()
    && !v.phase.SuperblockUnknown?  // Journal not initted until we leave this phase
    && JournalMachineMod.Internal(v.journal, v'.journal, v.cache, cacheOps, sk)
    && v'.betree == v.betree
    // Superblock constraints
    && v'.stableSuperblock == v.stableSuperblock
    && CacheIfc.ApplyWrites(v.cache, v'.cache, cacheOps)
    && WritesOkay(cacheOps, JournalMachineMod.Alloc(v'.journal))
    && AllocsDisjoint(v')
  }

  predicate BetreeInternal(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, sk: SplinterTreeMachineMod.Skolem)
  {
    && uiop.NoopOp?
    && v.WF()
    && !v.phase.SuperblockUnknown?  // Betree not initted until we leave this phase
    && v'.journal == v.journal
    && v'.stableSuperblock == v.stableSuperblock
    && SplinterTreeMachineMod.Internal(v.betree, v'.betree, v.cache, cacheOps, sk)
    && CacheIfc.ApplyWrites(v.cache, v'.cache, cacheOps)
    && AllocsDisjoint(v')
  }

  predicate ReqSync(v: Variables, v': Variables, uiop : UIOp, syncReqId: SyncReqId)
  {
    && uiop == ReqSyncOp(syncReqId)
    && v.phase.Running?
    && v.WF()
    && JournalMachineMod.ReqSync(v.journal, v'.journal, syncReqId)
    && v'.betree == v.betree
    && v'.stableSuperblock == v.stableSuperblock
  }

  predicate CompleteSync(v: Variables, v': Variables, uiop : UIOp, syncReqId: SyncReqId)
  {
    && uiop == CompleteSyncOp(syncReqId)
    && v.phase.Running?
    && v.WF()
    && JournalMachineMod.CompleteSync(v.journal, v'.journal, syncReqId)
    && v'.betree == v.betree
    && v'.stableSuperblock == v.stableSuperblock
  }

  // At some lower layer, where we duplicate the superblock to protect against disk sector
  // corruption, the Commit sequence looks like this:
  //   write sb0
  //   complete: ensure sb0 has hit the disk successfully before writing sb1, which might tear
  //   write sb1
  //   complete: Tell subsystems the commit is done. Can't acknowledge a sync dependent on this sb
  //     until sb1 commits, lest sb0 get lost before sb1 is successfully written and the "synced"
  //     data gets lost
  // At this layer, we abbreviate that to "write sb" and "write sb complete".
  predicate CommitStart(v: Variables, v': Variables, uiop : UIOp, seqBoundary: LSN)
  {
    && uiop.NoopOp?
    && v.phase.Running?
    && v.inFlightSuperblock.None?
    && v'.inFlightSuperblock.Some?
    && var sb := v'.inFlightSuperblock.value;
    && (exists alloc :: JournalMachineMod.CommitStart(v.journal, v'.journal, v.cache, sb.journal, seqBoundary, alloc))
    && SplinterTreeMachineMod.CommitStart(v.betree, v'.betree, v.cache, sb.betree, seqBoundary)
//    && sb.serial == v.stableSuperblock.serial + 1 // I think this isn't needed until duplicate-superblock code
    && CacheIfc.ApplyWrites(v.cache, v'.cache, [CacheIfc.Write(SUPERBLOCK_ADDRESS(), marshalSuperblock(sb))])
    && v'.stableSuperblock == v.stableSuperblock // only inFlightSuperblock should change at this step. stable should be well ... stable
  }

  predicate CommitComplete(v: Variables, v': Variables, uiop : UIOp)
  {
    && uiop.NoopOp?
    && v.phase.Running?
    && v.inFlightSuperblock.Some?
    && CacheIfc.IsClean(v.cache, SUPERBLOCK_ADDRESS())

    && var sb := v.inFlightSuperblock.value;
    && v'.stableSuperblock == sb
    && JournalMachineMod.CommitComplete(v.journal, v'.journal, v.cache, sb.journal)
    && SplinterTreeMachineMod.CommitComplete(v.betree, v'.betree, v.cache, sb.betree)
    && v'.cache == v.cache
    && v'.inFlightSuperblock.None?  // Yay! Done writing.
  }

  datatype Step =
    | RecoverStep(puts:MsgSeq, newbetree: SplinterTreeMachineMod.Variables)
    | QueryStep(key: Key, val: Value, bsk: SplinterTreeMachineMod.Skolem)
    | PutStep(bsk: SplinterTreeMachineMod.Skolem)
    | JournalInternalStep(jsk: JournalMachineMod.Skolem)
    | BetreeInternalStep(SplinterTreeMachineMod.Skolem)
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)
    | CommitStartStep(seqBoundary: LSN)
    | CommitCompleteStep()

  predicate NextStep(v: Variables, v': Variables, uiop : UIOp, cacheOps: CacheIfc.Ops, step: Step) {
    && match step {
      case RecoverStep(puts, newbetree) => Recover(v, v', uiop, puts, newbetree)
      case QueryStep(key, val, sk) => Query(v, v', uiop, key, val, sk)
      case PutStep(sk) => Put(v, v', uiop, sk)
      case JournalInternalStep(sk) => JournalInternal(v, v', uiop, cacheOps, sk)
      case BetreeInternalStep(sk) => BetreeInternal(v, v', uiop, cacheOps, sk)
      case ReqSyncStep(syncReqId) => ReqSync(v, v', uiop, syncReqId)
      case CompleteSyncStep(syncReqId) => CompleteSync(v, v', uiop, syncReqId)
      case CommitStartStep(seqBoundary) => CommitStart(v, v', uiop, seqBoundary)
      case CommitCompleteStep() => CommitComplete(v, v', uiop)
      // TODO: Cache doing a bunch of Disk ops
    }
  }

  predicate Next(v: Variables, v': Variables, uiop: UIOp, dop: DiskOp) {
    exists cacheOps,step ::
      && NextStep(v, v', uiop, cacheOps, step)
      //&& AllocationTableMachineMod.Disjoint(v'.journal.allocation, v'.betree.allocation)
  }
}
