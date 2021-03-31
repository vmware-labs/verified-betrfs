include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "Spec.s.dfy"
include "MsgSeq.i.dfy"
include "Tables.i.dfy"
include "CacheIfc.i.dfy"


// NB the journal needs a smaller-sized-write primitive. If we get asked to sync
// frequently, we don't want to burn an AU on every journal write. Maybe not even
// a CU. Hrmm.
module JournalMachineMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MessageMod
  import opened InterpMod
  import opened DeferredWriteMapSpecMod
  import opened MsgSeqMod
  import opened AllocationMod
  import AllocationTableMod
  import CacheIfc
  import MarshalledSnapshot // TODO stub delete

  // The core journal superblock
  datatype CoreSuperblock = CoreSuperblock(
    freshestCU: Option<CU>,
    boundaryLSN : LSN)

  // The entire superblock we need to store: Core data plus allocation data
  datatype Superblock = Superblock(
    allocation: AllocationTableMod.Superblock,
    core: CoreSuperblock)

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    priorCU: Option<CU>   // linked list pointer
  )

  datatype Variables = Variables(
    boundaryLSN: LSN,
      // The (exclusive) upper bound of LSNs reachable from the
      // last-known-committed superblock; earlier LSNs have already been
      // garbage-collected. (There may be leftover records with smaller LSNs in
      // a journal record, but the superblock says to ignore them.)
      // We need to track this value to disallow the Betree from moving backwards,
      // which would prevent us from recovering after a crash.

    persistentLSN: LSN,
      // The (exclusive) upper bound of LSNs known to be persistent on the on-disk journal.
      // We may need to track this value to ensure commit doesn't go backwards.
      // (maybe invariant-able)

    cleanLSN: LSN,
      // The (exclusive) upper bound of LSNs that could be made persistent with
      // a superblock write. They're covered by marshalled pages that are
      // "clean" (have been written back to the disk), but aren't yet linked to
      // the superblock. These pages aren't "durable" or "persistent", because if there
      // were a crash right now, they'd be unallocated garbage after the crash.

    marshalledLSN: LSN,
      // The (exclusive) upper bound of LSNs that have been marshalled into cache
      // blocks.

    unmarshalledTail: seq<Message>,
      // The rest of the in-memory journal

    syncReqs: map<SyncReqId, LSN>,
      // The LSN each outstanding SyncRequest was created at. The sync request may be
      // completed when the corresponding LSN <= persistentLSN.

    lsnToCU: map<LSN, CU>
      // We imagine that the journal can keep track of the entire mapping from LSN to CUs.
      // That's not really how the impl will work; it'll maintain some sort of summary, and
      // we'll refine from the disk state to get this field.
  )
  {
    // The (exclusive) upper bound of LSNs that have been journaled (in this epoch;
    // after a crash we can lose LSNs that weren't made persistent).
    function unmarshalledLSN() : LSN
    {
      marshalledLSN + |unmarshalledTail|
    }

    predicate WF() {
      && boundaryLSN <= persistentLSN <= cleanLSN <= marshalledLSN
      && (forall lsn :: 0 <= lsn < unmarshalledLSN() <==> lsn in lsnToCU)
    }
  }

  // advances tailLSN forward by adding a message
  predicate Append(s: Variables, s': Variables, message: Message)
  {
    && s' == s.(unmarshalledTail := s.unmarshalledTail + [message])
  }

  function AllocateEmptyCU(s: Variables) : CU
  {
    CU(0, 0) //TODO
  }

    // TODO marshalling
  function parse(b: UninterpretedDiskPage) : Option<JournalRecord>
  function marshal(jr: JournalRecord) : UninterpretedDiskPage

  function TailToMsgSeq(s: Variables) : MsgSeq
  {
    var start := s.marshalledLSN;
    var end := start + |s.unmarshalledTail|;
    MsgSeq(map i:LSN | start <= i < end :: s.unmarshalledTail[i - start], start, end)
  }

  // advances marshalledLSN forward by marshalling a batch of messages into a dirty cache page
  predicate AdvanceMarshalled(s: Variables, s': Variables, cacheOps: CacheIfc.Ops)
  {
    && s.WF()
    && var cu := AllocateEmptyCU(s);
    // Marshal and write the current record out into the cache. (This doesn't issue
    // a disk write, it just dirties a page.)
    && var priorLSN := if s.marshalledLSN==0 then None else Some(s.lsnToCU[s.marshalledLSN-1]);
    && var jr := JournalRecord(TailToMsgSeq(s), priorLSN);
    && cacheOps == [CacheIfc.Write(cu, marshal(jr))]
    && s' == s.(
      // Open a new, empty record to absorb future journal Appends
      unmarshalledTail := [])
  }

  // advances cleanLSN forward by learning that the cache has written back a contiguous
  // sequence of pages starting at last cleanLSN
  predicate AdvanceClean(s: Variables, s': Variables, cache: CacheIfc.Variables, newClean: nat)
  {
    && s.WF()
    && s.cleanLSN < newClean <= s.marshalledLSN
    && (forall lsn | s.cleanLSN <= lsn < newClean :: && CacheIfc.IsClean(cache, s.lsnToCU[lsn]))
    && s' == s.(cleanLSN := newClean)
  }

  predicate Reallocate(s: Variables, s': Variables)
  {
    false // does something with allocation table?
  }

  function ParseCachedRecord(cache: CacheIfc.Variables, cu: CU) : Option<JournalRecord>
  {
    var raw := CacheIfc.ReadValue(cache, cu);
    if raw.Some? then parse(raw.value) else None
  }

  // Agrees to advance persistentLSN (to cleanLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN)
  {
    && s.WF()
    // This is the stuff we'll get to garbage collect when the sb commit completes.
    && s.boundaryLSN <= newBoundaryLSN // presumably provable from Inv

    // These are the LSNs whose syncs will complete when the sb commit completes.
    && s.persistentLSN <= s.cleanLSN  // presumably provable from Inv

    // This is the superblock that's going to become persistent.
    && var allocationInfo := AllocationTableMod.Superblock(AllocationTableMod.SnapshotSuperblock(CU(0, 0))); // TODO
    && var freshestCU := if s.cleanLSN == 0 then None else Some(s.lsnToCU[s.cleanLSN-1]);
    && sb == Superblock(allocationInfo, CoreSuperblock(freshestCU, newBoundaryLSN))
      // TODO what f s.cleanLSN is zero or ... no priorCU?
    && s' == s
  }

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, sb: Superblock)
  {
    && s.WF()

    && s'.boundaryLSN == sb.core.boundaryLSN

    // Update s'.persistentLSN so that it reflects a persisted LSN (something in the last block,
    // ideally the last LSN in that block). NB This gives impl freedom to not
    // record the latest persistent LSN in the freshestCU block, which would be
    // kind of dumb (it would hold up syncs for no reason), but not unsafe.
    && (if sb.core.freshestCU.None?
        then s'.persistentLSN == sb.core.boundaryLSN
        else 
          && s'.persistentLSN -1 in s.lsnToCU
          && s.lsnToCU[s'.persistentLSN - 1] == sb.core.freshestCU.value
        )
    && s'.cleanLSN == s.cleanLSN
    && s'.marshalledLSN == s.marshalledLSN
    && s'.unmarshalledTail == s.unmarshalledTail
    && s'.syncReqs == s.syncReqs
  }

  predicate ReqSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && 0 < s.unmarshalledLSN()
    && syncReqId !in s.syncReqs.Keys
    && s' == s.(syncReqs := s.syncReqs[syncReqId := s.unmarshalledLSN()-1])
  }

  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && syncReqId in s.syncReqs.Keys
    && s.syncReqs[syncReqId] < s.persistentLSN
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, syncReqId))
  }

  datatype Step =
    | AppendStep(message: Message)
    | AdvanceMarshalledStep(cacheOps: CacheIfc.Ops)
    | AdvanceCleanStep(cache: CacheIfc.Variables, newClean: nat)
    | ReallocateStep()
    | CommitStartStep(cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN)
    | CommitCompleteStep(sb: Superblock)
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)

  predicate NextStep(s: Variables, s': Variables, step: Step) {
    match step {
      case AppendStep(message) => Append(s, s', message)
      case AdvanceMarshalledStep(cacheOps) => AdvanceMarshalled(s, s', cacheOps)
      case AdvanceCleanStep(cache, newClean) => AdvanceClean(s, s', cache, newClean)
      case ReallocateStep => Reallocate(s, s')
      case CommitStartStep(cache, sb, newBoundaryLSN) => CommitStart(s, s', cache, sb, newBoundaryLSN)
      case CommitCompleteStep(sb) => CommitComplete(s, s', sb)
      case ReqSyncStep(syncReqId) => ReqSync(s, s', syncReqId)
      case CompleteSyncStep(syncReqId) => CompleteSync(s, s', syncReqId)
    }
  }

  predicate Next(s: Variables, s': Variables) {
    exists step :: NextStep(s, s', step)
  }
}
