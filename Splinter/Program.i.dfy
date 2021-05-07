// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"
include "JournalInterp.i.dfy"
include "Betree.i.dfy"
include "CacheIfc.i.dfy"

// TODO first prove that a Program with a simple-policy cache works?

// The "Program" is the complete model of the program state, with all of the components
// (Journal, Betree, Cache).
// It has an interface to a disk, but can't actually see inside the disk (that's for the IOSystem).

module ProgramMachineMod {
  import AllocationTableMod
  import AllocationTableMachineMod
  import BetreeMachineMod
  import JournalMachineMod
  import opened AllocationMod
  import opened DeferredWriteMapSpecMod
  import opened InterpMod
  import opened MessageMod
  import opened MsgSeqMod
  import opened Options
  import CacheIfc

  datatype Superblock = Superblock(
    serial: nat,
    journal: JournalMachineMod.Superblock,
    betree: BetreeMachineMod.Superblock)

  function parseSuperblock(b: UninterpretedDiskPage) : Option<Superblock>

  function marshalSuperblock(sb: Superblock) : (b: UninterpretedDiskPage)
    ensures parseSuperblock(b) == Some(sb)

  function SUPERBLOCK_ADDRESS(): CU
  {
    CU(0, 0)
  }

  datatype Variables = Variables(
    stableSuperblock: Superblock,
    cache: CacheIfc.Variables,
    journal: JournalMachineMod.Variables,
    betree: BetreeMachineMod.Variables,
    inFlightSuperblock: Option<Superblock>
    )
  {
    predicate WF() {
      true
    }
  }

  predicate Init(v: Variables)
  {
    false
  }

  predicate Recover(v: Variables, v': Variables)
  {
    false
  }

  predicate Query(v: Variables, v': Variables, key: Key, val: Value, sk: BetreeMachineMod.Skolem)
  {
    && v.WF()
    && v'.journal == v.journal
    && BetreeMachineMod.Query(v.betree, v'.betree, v.cache, key, val, sk)
    && v'.cache == v.cache  // no cache writes
  }

  predicate Put(v: Variables, v': Variables, key: Key, val: Value, sk: BetreeMachineMod.Skolem)
  {
    && v.WF()
    && JournalMachineMod.Append(v.journal, v'.journal, MessagePut(key, val))
    && BetreeMachineMod.Put(v.betree, v'.betree, key, val, sk)
    && v'.cache == v.cache  // no cache writes
  }

  // TODO move to Sets.i
  predicate SetsMutuallyDisjoint<T>(sets: seq<set<T>>) {
    forall i, j | 0<=i<|sets| && 0<=j<|sets| && i!=j :: sets[i] !! sets[j]
  }

  predicate AllocsDisjoint(v: Variables)
  {
    SetsMutuallyDisjoint([
      {SUPERBLOCK_ADDRESS()},
      JournalMachineMod.Alloc(v.journal),
      BetreeMachineMod.Alloc(v.betree, v.cache, v.stableSuperblock.betree)
      ])
  }

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

  predicate JournalInternal(v: Variables, v': Variables, cacheOps: CacheIfc.Ops, sk: JournalMachineMod.Skolem)
  {
    && v.WF()
    && JournalMachineMod.Internal(v.journal, v'.journal, v.cache, cacheOps, sk)
    && v'.betree == v.betree
    && CacheIfc.ApplyWrites(v.cache, v'.cache, cacheOps)
    && WritesOkay(cacheOps, JournalMachineMod.Alloc(v'.journal))
    && AllocsDisjoint(v')
  }

  predicate BetreeInternal(v: Variables, v': Variables, cacheOps: CacheIfc.Ops, sk: BetreeMachineMod.Skolem)
  {
    && v.WF()
    && v'.journal == v.journal
    && BetreeMachineMod.Internal(v.betree, v'.betree, v.cache, cacheOps, sk)
    && CacheIfc.ApplyWrites(v.cache, v'.cache, cacheOps)
  }

  predicate ReqSync(v: Variables, v': Variables, syncReqId: SyncReqId)
  {
    && v.WF()
    && JournalMachineMod.ReqSync(v.journal, v'.journal, syncReqId)
    && v'.betree == v.betree
  }
 
  predicate CompleteSync(v: Variables, v': Variables, syncReqId: SyncReqId)
  {
    && v.WF()
    && JournalMachineMod.CompleteSync(v.journal, v'.journal, syncReqId)
    && v'.betree == v.betree
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
  predicate CommitStart(v: Variables, v': Variables, seqBoundary: LSN)
  {
    && v.inFlightSuperblock.None?
    && v'.inFlightSuperblock.Some?
    && var sb := v'.inFlightSuperblock.value;
    && (exists alloc :: JournalMachineMod.CommitStart(v.journal, v'.journal, v.cache, sb.journal, seqBoundary, alloc))
    && BetreeMachineMod.CommitStart(v.betree, v'.betree, v.cache, sb.betree, seqBoundary)
//    && sb.serial == v.stableSuperblock.serial + 1 // I think this isn't needed until duplicate-superblock code
    && CacheIfc.ApplyWrites(v.cache, v'.cache, [CacheIfc.Write(SUPERBLOCK_ADDRESS(), marshalSuperblock(sb))])
  }

  predicate CommitComplete(v: Variables, v': Variables)
  {
    && v.inFlightSuperblock.Some?
    && CacheIfc.IsClean(v.cache, SUPERBLOCK_ADDRESS())

    && var sb := v.inFlightSuperblock.value;
    && v'.stableSuperblock == sb
    && JournalMachineMod.CommitComplete(v.journal, v'.journal, v.cache, sb.journal)
    && BetreeMachineMod.CommitComplete(v.betree, v'.betree, v.cache, sb.betree)
    && v'.cache == v.cache
    && v'.inFlightSuperblock.None?  // Yay! Done writing.
  }

  datatype Step =
    | RecoverStep()
    | QueryStep(key: Key, val: Value, bsk: BetreeMachineMod.Skolem)
    | PutStep(key: Key, val: Value, bsk: BetreeMachineMod.Skolem)
    | JournalInternalStep(jsk: JournalMachineMod.Skolem)
    | BetreeInternalStep(BetreeMachineMod.Skolem)
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)
    | CommitStartStep(seqBoundary: LSN)
    | CommitCompleteStep()
    
  predicate NextStep(v: Variables, v': Variables, cacheOps: CacheIfc.Ops, step: Step) {
    && match step {
      case RecoverStep() => Recover(v, v')
      case QueryStep(key, val, sk) => Query(v, v', key, val, sk)
      case PutStep(key, val, sk) => Put(v, v', key, val, sk)
      case JournalInternalStep(sk) => JournalInternal(v, v', cacheOps, sk)
      case BetreeInternalStep(sk) => BetreeInternal(v, v', cacheOps, sk)
      case ReqSyncStep(syncReqId) => ReqSync(v, v', syncReqId)
      case CompleteSyncStep(syncReqId) => CompleteSync(v, v', syncReqId)
      case CommitStartStep(seqBoundary) => CommitStart(v, v', seqBoundary)
      case CommitCompleteStep() => CommitComplete(v, v')
    }
  }

  predicate Next(v: Variables, v': Variables) {
    exists cacheOps,step ::
      && NextStep(v, v', cacheOps, step)
      //&& AllocationTableMachineMod.Disjoint(v'.journal.allocation, v'.betree.allocation)
  }
}

module ProgramInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened AllocationMod
  import opened MsgSeqMod
  import AllocationTableMod
  //import JournalMod
  import BetreeInterpMod
  import JournalInterpMod
  import opened ProgramMachineMod

  function ISuperblock(dv: DiskView) : Option<Superblock>
  {
    var bcu0 := CU(0, 0);
    var bcu1 := CU(0, 1);
    if bcu0 in dv && bcu1 in dv
    then
      var sb0 := parseSuperblock(dv[bcu0]);
      var sb1 := parseSuperblock(dv[bcu1]);
      if sb0.Some? && sb1.Some? && sb0.value.serial == sb1.value.serial
      then
        sb0
      else
        None  // Stop! Recovery should ... copy the newer one?
          // well I think I() of that should be the newer one, but we should just
          // not be allowed to write anything until we've got them back in sync.
    else
      None  // silly expression: DV has holes in it
  }

  function ISuperblockReads(dv: DiskView) : seq<AU>
  {
    [ SUPERBLOCK_ADDRESS().au ]
  }
 
  // Program will have a runtime view of what (ghost) alloc each subsystem thinks it's using,
  // and use that to filter the dvs here.
  // Those ghost views will invariantly match the IReads functions of the actual disk -- that is,
  // * if we were to recover after a crash (when the physical alloc is empty), we'd fault in
  // an alloc table for the subsystem.
  // * that alloc table would invariantly match IReads.
  //
  // IM == Interpret as InterpMod
  // TODO NEXT well actually we need a chain of Interps; see DeferredWriteMapSpecMod
  function IM(v: Variables) : (i:Interp)
    ensures i.WF()
  {
    var sb := ISuperblock(v.cache.dv);
    if sb.Some?
    then
      var betreeInterp := BetreeInterpMod.IM(v.betree, v.cache, sb.value.betree);
      var journalMsgSeq := JournalInterpMod.IM(v.journal, v.cache, sb.value.journal);
      if journalMsgSeq.Some? && betreeInterp.seqEnd == journalMsgSeq.value.seqStart
      then
        Concat(betreeInterp, journalMsgSeq.value)
      else
        InterpMod.Empty()
    else
      InterpMod.Empty()
  }

  function IMReads(v: Variables) : seq<AU> {
    var sbreads := ISuperblockReads(v.cache.dv);
    var sb := ISuperblock(v.cache.dv);
    if sb.Some?
    then
      sbreads
        + JournalInterpMod.IReads(v.journal, v.cache, sb.value.journal.core)
        + BetreeInterpMod.IReads(v.betree, v.cache, sb.value.betree)
    else
      sbreads
  }

  function IReads(v: Variables) : seq<AU> {
    IMReads(v)
  }

  lemma Framing(v0: Variables, v1: Variables)
    requires DiskViewsEquivalentForSet(v0.cache.dv, v1.cache.dv, IReads(v0))
    requires v0.betree == v1.betree
    requires v0.journal == v1.journal
    ensures IM(v0) == IM(v1)
  {
    assert ISuperblock(v0.cache.dv) == ISuperblock(v1.cache.dv);
    var sb := ISuperblock(v0.cache.dv);
    if sb.Some? {
      BetreeInterpMod.Framing(v0.betree, v0.cache, v1.cache, sb.value.betree);
      JournalInterpMod.Framing(v0.journal, v0.cache, v1.cache, sb.value.journal.core);
    }
  }

  // Next step is to write the refinement proof, using obligation placeholders
  // in Betree & Journal so we can see the outer structure -- including the
  // framing argument -- early.
  // Here's a quick and dirty approximation: it ignores crashes, but lets us
  // get to the framing issue right away.

  predicate Inv(v: Variables)
  {
    && AllocsDisjoint(v)
  }

  // Not gonna think about Init in this fakey little simulation, since we want
  // mkfs init (behavior start), not program init (crash recovery).
  lemma InvNext(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
  }

  lemma NextRefines(v: Variables, v': Variables)
    //requires Inv(v)
    requires Inv(v)
    requires Next(v, v')
DeferredWriteMapSpecMod 
    ensures Next(IM(v), IM(v'))
  {
    var cacheOps,step :| NextStep(v, v', cacheOps, step);
    match step {
      case RecoverStep() => {
        assert IM(v') == IM(v);
      }
      case QueryStep(key, val, sk) => {
        assert IM(v') == IM(v);
      }
      case PutStep(key, val, sk) => {
        // This step should be difficult. :v)
        // hah yes it's not, because IM is only looking at the cache, not the membuffer
        // (internal state machine state)
        assert IM(v') == IM(v).Put(key, val);
      }
      case JournalInternalStep(sk) => {
        assume false;
        assert IM(v') == IM(v);
      }
      case BetreeInternalStep(sk) => {
        assume false;
        assert IM(v') == IM(v);
      }
      case ReqSyncStep(syncReqId) => {
        assume false;
        assert IM(v') == IM(v);
      }
      case CompleteSyncStep(syncReqId) => {
        assume false;
        assert IM(v') == IM(v);
      }
      case CommitStartStep(seqBoundary) => {
        assume false;
        assert IM(v') == IM(v);
      }
      case CommitCompleteStep() => {
        assume false;
        assert IM(v') == IM(v);
      }
    }
  }
}

/*
Okay, so the magic is going to be that
- most of the time when we change a block in RAM we'll prove that it's
  not in use in any other view
  - that'll depend on an invariant between the allocation table
    and the IReads functions
  - And we'll need a proof that, if IReads doesn't change, I doesn't
    change, of course.
- when we write a non-superblock back to disk, we inherit that no-change
  property; the persistent view doesn't change because the thing
  we wrote back was dirty and hence outside of the IReads of the
  persistent view.
- when we update the superblock, we're creating a frozen view.
- when we write a superblock back, it's easy again, because the persistent
  view just vanishes, replaced by the frozen view.
  The vanishing old persistent view implicitly creates some free nodes,
  which can be detected because the available nodes are computed at
  runtime by reading the active AllocationTables, and one just became
  empty.
  (that is, the union of allocationTables will cover the IReads sets.)
*/
