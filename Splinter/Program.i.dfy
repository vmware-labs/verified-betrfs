include "Journal.i.dfy"
include "Betree.i.dfy"

// TODO first prove that a Program with a simple-policy cache works?

// The "Program" is the complete model of the program state, with all of the components
// (Journal, Betree, Cache).
// It has an interface to a disk, but can't actually see inside the disk (that's for the IOSystem).

module ProgramMachineMod {
  import JournalMachineMod
  import BetreeMod

  datatype Superblock = Superblock(
    serial: nat,
    journal: JournalMachineMod.Superblock,
    betree: BetreeMod.Superblock)

  datatype Variables = Variables(
    stableSuperblock: Superblock,
    cache: 
    journal: JournalMachineMod.Variables,
    betree: CachedBetreeMachine.Variables,
    inFlightSuperblock: Option<Superblock>
    )
  {
    predicate WF() {
      true
    }
  }

  predicate Init(s: Variables)
  {
    false
  }

  predicate Recover(s: Variables, s': Variables)
  {
    false
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.WF()
    && s'.journal == s.journal
    && CachedBetreeMachine.Query(s, s', k, v)
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s.WF()
    && JournalMachine.Record(s, s', JournalMachine.Put(k, v))
    && CachedBetreeMachine.Put(s, s', k, v)
  }

  predicate BetreeNoop(s: Variables, s': Variables)
  {
    && s.WF()
    && s'.journal == s.journal
    && CachedBetreeMachine.Noop(s, s')
  }

  predicate AsyncFlush(s: Variables, s': Variables)
  {
    && s.WF()
    && JournalMachine.AsyncFlush(s, s')
    && CachedBetreeMachine.Noop(s, s')
  }

  predicate ReqSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && s.WF()
    && JournalMachine.ReqSync(s, s', syncReqId)
    && CachedBetreeMachine.Noop(s, s')
  }
 
  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && s.WF()
    && JournalMachine.CompleteSync(s, s', syncReqId)
    && CachedBetreeMachine.Noop(s, s')
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
  predicate CommitStart(s: Variables, s': Variables, seqBoundary: LSN)
  {
    && s.inFlightSuperblock.None?
    && var sb := s'.inFlightSuperblock;
    && Journal.CommitStart(s.journal, s'.journal, sb.journal, seqBoundary)
    && Betree.CommitStart(s.betree, s'.betree, sb.betree, seqBoundary)
    && sb.serial == s.stableSuperblock.serial + 1
    && Disk.IssueWrite(s, s', SUPERBLOCK_ADDRESS(), sb) // TODO this stuff comes in as a binding param
  }

  predicate CommitComplete(s: Variables, s': Variables)
  {
    && Disk.CompleteWrite(s, s', ?)   // how to match the write req?
    && s.inFlightSuperblock.Some?
    && var sb := s.inFlightSuperblock.value;
    && s'.stableSuperblock == sb
    && Journal.CommitComplete(s.journal, s'.journal, sb.journal)
    && Betree.CommitComplete(s.betree, s'.betree, sb.betree)
    && s'.inFlightSuperblock.None?
  }

  predicate Next(s: Variables, s': Variables) {
    exists step ::
      && NextStep(s, s', step)
      && AllocationTablesDisjoint(s'.journal.allocation, s'.betree.allocation)
  }
}

module ProgramInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened AllocationMod
  import opened MsgSeqMod
  import AllocationTableMod
  import JournalMod
  import BetreeMod

  function parseSuperblock(b: UninterpretedDiskPage) : Option<Superblock>

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

  function ISuperblockReads(dv: DiskView) : set<AU>
  {
    {0}
  }
 
  // IM == Interpret as InterpMod
  // Oh man we're gonna have a family of IReads predicates that capture the
  // heapiness of DiskView, aren't we?
  function IM(dv: DiskView) : (i:Interp)
    ensures i.WF()
  {
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      Concat(BetreeMod.IM(dv, sb.value.betree), JournalMod.IM(dv, sb.value.journal))
    else
      InterpMod.Empty()
  }

  function IMReads(dv: DiskView) : seq<AU> {
      []
      /*
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      JournalMod.IReads(dv, sb.value.journal) + BetreeMod.IReads(dv, sb.value.betree)
    else
      set{}
      */
  }

  function IReads(dv: DiskView) : seq<AU> {
    IMReads(dv)
  }

  lemma Framing(dv0: DiskView, dv1: DiskView)
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0))
    ensures IM(dv0) == IM(dv1)
  {
    //assert forall k :: k !in I(dv0);
    //assert forall k :: IM(dv0).mi[k] == IM(dv1).mi[k];
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
