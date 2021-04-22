include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "Spec.s.dfy"
include "MsgSeq.i.dfy"
include "Tables.i.dfy"


/*
Okay I think we need to just talk about DiskViews at this layer. Well, no, a cache that
always has CanRead true. We still need to negotiate disjoint write Ops.
At this layer, in the IOSystem machine, we'll need a model for how crashes replace the
cache contents.
This is all good; it's just an infinitely-big cache that never needs to evict.

At the next layer down, we'll talk about interactions betwixt the Cache and the Disk.
So the trick there will be showing that transitions obey constraints that require testing
pages that aren't in the cache. That is, we know some sufficient predicate on those
pages that lets us ghostily know that the transition is valid despite not being
able to evaluate it directly at runtime. Let's enumerate the affected transitions.
*/

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
  import AllocationTableMachineMod
  import CacheIfc

  // The core journal superblock
  datatype CoreSuperblock = CoreSuperblock(
    freshestCU: Option<CU>,
    boundaryLSN : LSN)

  // The entire superblock we need to store: Core data plus allocation data
  datatype Superblock = Superblock(
    allocation: AllocationTableMachineMod.Superblock, // TODO This should go down a layer!
    core: CoreSuperblock)

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    priorCU: Option<CU>   // linked list pointer
  )
  {
    function priorSB(sb: CoreSuperblock) : CoreSuperblock
    {
      CoreSuperblock(priorCU, sb.boundaryLSN)
    }
  }

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
      && (forall lsn :: boundaryLSN <= lsn < marshalledLSN <==> lsn in lsnToCU)
    }
  }

  // advances tailLSN forward by adding a message
  predicate Append(s: Variables, s': Variables, message: Message)
  {
    && s' == s.(unmarshalledTail := s.unmarshalledTail + [message])
  }

  // TODO marshalling
  function parse(b: UninterpretedDiskPage) : Option<JournalRecord>
  function marshal(jr: JournalRecord) : UninterpretedDiskPage

  function TailToMsgSeq(s: Variables) : MsgSeq
  {
    var start := s.marshalledLSN;
    var end := s.unmarshalledLSN();
    MsgSeq(map i:LSN | start <= i < end :: s.unmarshalledTail[i - start], start, end)
  }

  // advances marshalledLSN forward by marshalling a batch of messages into a dirty cache page
  predicate AdvanceMarshalled(s: Variables, s': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, newCU: CU)
  {
    && s.WF()

    // newCU is an unused CU.
    // That could be because the impl has freshly reserved a chunk of CUs from the outer
    // program, or because it's using up a CU from a prior reserved chunk. The impl will
    // batch allocations so it can avoid needing to rewrite the marshaled allocation before
    // commiting a fresh superblock (on sync). Thus "unused" may be computed as "reserved
    // but known not to be in use in the current JournalChain".

    // Marshal and write the current record out into the cache. (This doesn't issue
    // a disk write, it just dirties a page.)
    && var priorCU := if s.marshalledLSN == s.boundaryLSN then None else Some(s.lsnToCU[s.marshalledLSN-1]);
    && var jr := JournalRecord(TailToMsgSeq(s), priorCU);
    && cacheOps == [CacheIfc.Write(newCU, marshal(jr))]

    // Record the changes to the marshalled, unmarshalled regions, and update the allocation.
    && s' == s.(
      // Open a new, empty record to absorb future journal Appends
      marshalledLSN := s.unmarshalledLSN(),
      unmarshalledTail := [],
      lsnToCU := s'.lsnToCU  // Tautology to defer this constraint to next predicate
      )
    // constructive: (map lsn:LSN | 0 <= lsn < s.unmarshalledLSN() :: if lsn < s.marshalledLSN then s.lsnToCU[lsn] else newCU),
    // predicate:
    && CorrectMapping(cache, Some(newCU), s'.lsnToCU)
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
    // TODO Allocation isn't what we want, yet. It's tight, so we have to write
    // a new allocation table every time we change the superblock. That's no
    // good!
    && false // does something with allocation table?
  }

  // Agrees to advance persistentLSN (to cleanLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN, alloc: AllocationTableMachineMod.Variables)
  {
    && s.WF()
    // This is the stuff we'll get to garbage collect when the sb commit completes.
    && s.boundaryLSN <= newBoundaryLSN // presumably provable from Inv

    // These are the LSNs whose syncs will complete when the sb commit completes.
    && s.persistentLSN <= s.cleanLSN  // presumably provable from Inv

    // The allocation we actually commit to is a superset of the allocation we're using.
    && (forall cu | cu in s.lsnToCU.Values :: cu in alloc.table)

    // This is the superblock that's going to become persistent.
    && AllocationTableMachineMod.DurableAt(alloc, cache, sb.allocation)
    && var freshestCU := if s.cleanLSN == s.boundaryLSN then None else Some(s.lsnToCU[s.cleanLSN-1]);
    && sb.core == CoreSuperblock(freshestCU, newBoundaryLSN)
    && s' == s
  }

  //////////////////////////////////////////////////////////////////////////////
  // JournalChain

  // Monoid-friendly (quantified-list) definition
  datatype JournalChain = JournalChain(sb: CoreSuperblock, recs:seq<JournalRecord>)
  {
    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along boundaryLSN.
    function priorSB() : CoreSuperblock
      requires 0<|recs|
    {
      recs[0].priorSB(sb)
    }
  }

  predicate IsLastLink(i: nat, chain: JournalChain)
    requires 0<=i<|chain.recs|
  {
    // stop if nothing more available
    || chain.recs[i].priorCU.None?
    // stop if nothing more needed
    || chain.sb.boundaryLSN >= chain.recs[i].messageSeq.seqStart
  }

  predicate WFChainBasic(chain: JournalChain)
  {
    && (chain.sb.freshestCU.None? <==> 0 == |chain.recs|)
    && (forall i | 0<=i<|chain.recs| :: i==|chain.recs|-1 <==> IsLastLink(i, chain))
    && (forall i | 0<=i<|chain.recs|-1 :: chain.recs[i].priorCU.Some?)
  }

  predicate {:opaque} WFChainInner(chain: JournalChain)
    requires WFChainBasic(chain)
  {
    && (forall i | 0<=i<|chain.recs|-1 ::
      chain.recs[i].messageSeq.seqStart == chain.recs[i+1].messageSeq.seqEnd)
  }

  predicate WFChain(chain: JournalChain)
  {
    && WFChainBasic(chain)
    && WFChainInner(chain)
  }

  function CUsForChain(chain: JournalChain) : (cus: seq<CU>)
    requires WFChain(chain)
    ensures |cus| == |chain.recs|
  {
    if chain.sb.freshestCU.None?
    then []
    else [chain.sb.freshestCU.value] + seq(|chain.recs|-1,
        i requires 0<=i<|chain.recs|-1 => chain.recs[i].priorCU.value)
  }

  predicate RecordOnDisk(dv: DiskView, cu: CU, journalRecord: JournalRecord)
  {
    && cu in dv
    && parse(dv[cu]) == Some(journalRecord)
  }

  predicate {:opaque} ChainMatchesDiskView(dv: DiskView, chain: JournalChain)
    requires WFChain(chain)
  {
    // chain corresponds to stuff in the DiskView starting at freshestCU.
    && var cus := CUsForChain(chain);
    && (forall i | 0<=i<|chain.recs| :: RecordOnDisk(dv, cus[i], chain.recs[i]))
  }

  // Describe a valid chain.
  predicate ValidJournalChain(dv: DiskView, chain: JournalChain)
  {
    && WFChain(chain)
    && ChainMatchesDiskView(dv, chain)
  }

  lemma ValidEmptyChain(dv: DiskView, sb: CoreSuperblock)
    requires sb.freshestCU.None?
    ensures ValidJournalChain(dv, JournalChain(sb, []))
  {
    reveal_WFChainInner();
    reveal_ChainMatchesDiskView();
  }

  function ExtendChain(sb: CoreSuperblock, rec: JournalRecord, innerchain: JournalChain)
    : (chain: JournalChain)
    requires sb.freshestCU.Some?
    requires rec.priorCU.Some? ==> sb.boundaryLSN < rec.messageSeq.seqStart; // proves !IsLastLink(0, chain)
    requires innerchain.sb == rec.priorSB(sb);
    requires 0<|innerchain.recs| ==> rec.messageSeq.seqStart == innerchain.recs[0].messageSeq.seqEnd;
    requires WFChain(innerchain)
    ensures WFChain(chain)
  {
    var chain := JournalChain(sb, [rec] + innerchain.recs);
    assert WFChainBasic(chain) by {
      forall i | 0<=i<|chain.recs| ensures i==|chain.recs|-1 <==> IsLastLink(i, chain)
      {
        if 0<i {
          assert IsLastLink(i-1, innerchain) == IsLastLink(i, chain);
        }
      }
    }
    assert WFChainInner(chain) by { reveal_WFChainInner(); }
    chain
  }

  // Define reading a chain recursively. Returns None if any of the
  // CUs point to missing blocks from the dv, or if the block can't
  // be parsed.
  // Return the set of readCUs visited. We may read six CUs before returning
  // a None chain. We have to know that to show how related dvs produce identical
  // results (even when they're broken).
  datatype ChainResult = ChainResult(chain: Option<JournalChain>, readCUs:seq<CU>)

  function ChainFrom(dv: DiskView, sb: CoreSuperblock) : (r:ChainResult)
    ensures r.chain.Some? ==>
      && ValidJournalChain(dv, r.chain.value)
      && r.chain.value.sb == sb
    decreases |dv.Keys|
  {
    if sb.freshestCU.None? then
      // Superblock told the whole story; nothing to read.
      ValidEmptyChain(dv, sb);
      ChainResult(Some(JournalChain(sb, [])), [])
    else if sb.freshestCU.value !in dv then
      // !RecordOnDisk: tried to read freshestCU and failed
      ChainResult(None, [sb.freshestCU.value])
    else
      var firstRec := parse(dv[sb.freshestCU.value]);
      if firstRec.None? then
        // !RecordOnDisk: read freshestCU, but it was borked
        ChainResult(None, [sb.freshestCU.value])
      else if firstRec.value.messageSeq.seqEnd <= sb.boundaryLSN then
        // This isn't an invariant disk state: if we're in the initial call,
        // the superblock shouldn't point to a useless JournalRecord; if we're
        // in a recursive call with correctly-chained records, we should have
        // already ignored this case.
        ChainResult(None, [sb.freshestCU.value])
      else if firstRec.value.messageSeq.seqStart == sb.boundaryLSN then
        // Glad we read this record, but we don't need to read anything beyond.
        var r := ChainResult(Some(JournalChain(sb, [firstRec.value])), [sb.freshestCU.value]);
        assert ValidJournalChain(dv, r.chain.value) by {
          reveal_WFChainInner();
          reveal_ChainMatchesDiskView();
        }
        r
      else
        var inner := ChainFrom(MapRemove1(dv, sb.freshestCU.value), firstRec.value.priorSB(sb));
        if inner.chain.None? // tail didn't decode or
          // tail decoded but head doesn't stitch to it (a cross-crash invariant)
          || (0<|inner.chain.value.recs|
              && firstRec.value.messageSeq.seqStart != inner.chain.value.recs[0].messageSeq.seqEnd)
        then
          // failure in recursive call.
          // We read our cu plus however far the recursive call reached.
          ChainResult(None, [sb.freshestCU.value] + inner.readCUs)
        else
          assert firstRec.value.priorCU.Some? ==> sb.boundaryLSN < firstRec.value.messageSeq.seqStart;
          var chain := ExtendChain(sb, firstRec.value, inner.chain.value);
          //var chain := JournalChain(sb, [firstRec.value] + inner.chain.value.recs);
          assert ValidJournalChain(dv, chain) by {
            reveal_ChainMatchesDiskView();
            var cus := CUsForChain(chain);
            assert forall i | 0<=i<|chain.recs| :: RecordOnDisk(dv, cus[i], chain.recs[i]); // trigger
          }
          ChainResult(Some(chain), [sb.freshestCU.value] + inner.readCUs)
  }

  // JournalChain
  //////////////////////////////////////////////////////////////////////////////

  // lsnToCU reflects a correct reading of the sb chain, I guess?
  // TODO It's broken to be demanding that we actually can read this stuff out
  // of the cache; we really want this to be a ghosty property in the next
  // layer down. Not sure yet how to make that work.
  predicate CorrectMapping(cache: CacheIfc.Variables, freshestCU: Option<CU>, lsnToCU: map<LSN, CU>)
  {
    //var ChainFrom(dv: DiskView, sb: CoreSuperblock) : (r:ChainResult)
    // TODO We should build up a JournalChain here and confirm it justifies the mapping.
    true
  }

  // TODO recovery time action!

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock)
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
          && s'.persistentLSN - 1 in s.lsnToCU
          && s.lsnToCU[s'.persistentLSN - 1] == sb.core.freshestCU.value
        )
    && s'.cleanLSN == s.cleanLSN
    && s'.marshalledLSN == s.marshalledLSN
    && s'.unmarshalledTail == s.unmarshalledTail
    && s'.syncReqs == s.syncReqs
    && CorrectMapping(cache, sb.core.freshestCU, s'.lsnToCU)
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
    | AdvanceMarshalledStep(cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, newCU: CU)
    | AdvanceCleanStep(cache: CacheIfc.Variables, newClean: nat)
    | CommitStartStep(cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN, alloc: AllocationTableMachineMod.Variables)
    | CommitCompleteStep(cache: CacheIfc.Variables, sb: Superblock)
    | ReqSyncStep(syncReqId: SyncReqId)
    | CompleteSyncStep(syncReqId: SyncReqId)

  predicate NextStep(s: Variables, s': Variables, step: Step) {
    match step {
      case AppendStep(message) => Append(s, s', message)
      case AdvanceMarshalledStep(cache, cacheOps, newCU) => AdvanceMarshalled(s, s', cache, cacheOps, newCU)
      case AdvanceCleanStep(cache, newClean) => AdvanceClean(s, s', cache, newClean)
      case CommitStartStep(cache, sb, newBoundaryLSN, alloc) => CommitStart(s, s', cache, sb, newBoundaryLSN, alloc)
      case CommitCompleteStep(cache, sb) => CommitComplete(s, s', cache, sb)
      case ReqSyncStep(syncReqId) => ReqSync(s, s', syncReqId)
      case CompleteSyncStep(syncReqId) => CompleteSync(s, s', syncReqId)
    }
  }

  predicate Internal(s: Variables, s': Variables) {
    exists step ::
      && NextStep(s, s', step)
      && (
        || step.AdvanceMarshalledStep?
        || step.AdvanceCleanStep?
        )
  }

  predicate Next(s: Variables, s': Variables) {
    exists step :: NextStep(s, s', step)
  }
}
