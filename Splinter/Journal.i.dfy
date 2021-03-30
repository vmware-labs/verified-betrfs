include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "Spec.s.dfy"
include "MsgSeq.i.dfy"
include "Tables.i.dfy"


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

  // The core journal superblock
  datatype CoreSuperblock = CoreSuperblock(
    freshestCU: Option<CU>,
    firstValidLSN : LSN)

  // The entire superblock we need to store: Core data plus allocation data
  datatype Superblock = Superblock(
    allocation: AllocationTableMod.Superblock,
    core: CoreSuperblock)

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    priorCU: Option<CU>   // linked list pointer
  )

  // This little record tells us if we're in the middle of a
  // CommitStart...CommitComplete sequence.
  datatype WriteState =
    | Idle
    | WritingJournal(count: nat)  // Writing seqStart .. seqStart + count

  datatype Variables = Variables(
    firstValidLSN: LSN,
      // Smaller LSNs are unreachable from the last-known-committed superblock;
      // they have already been garbage-collected. (There may be leftover
      // records with smaller LSNs in a journal record, but they should be
      // ignored).

    durableTailCU: Option<CU>,
      // pointer to the freshest CU that's durable (okay to commit in SB)

    seqStart: LSN,  // in-memory records start here
    journal: seq<MemJournalRecord>, // in memory records
    seqToAU: map<LSN, AU>,  // Which AU each seq number is stored in.
    syncReqs: map<SyncReqId, LSN>
  )
  {
    predicate seqToAuValid() {
      && forall seqno :: firstValidLSN <= seqno < seqStart <==> seqno in seqToAU.Keys
    }

    predicate WF() {
      && seqToAuValid()
    }
  }

//////////////////////////////////////////////////////////////////////////////
/*
Journal operations include:
- Append(Message): find the open CU and concat the message (cache write)
- Advance(): the open CU is full. Open a new one with a back-pointer. (cache write)
  Depends on being able to identify an unutilized CU, which requires knowing which CUs
  in the disk journal are allocated.
- Reallocate(): allocate or free AUs
- CommitStart(sb): sb becomes eligible to be the next superblock
  - PagesAreClean(lastCUexcl): the pages for CUs from sb.freshestCU to lastCUexcl are clean
    (what to do when sb.freshestCU is None?
- CommitComplete(sb): sb is definitely the next superblock
- Replay(): needed at recovery time

A completely empty journal has firstCU.None?, firstValidLSN==0
A fully-garbage-collected journal has firstCU.None?, firstValidLSN positive

Invariants:
- I think we need a ghost relation between journal cus and LSNs
- Only pages "between" durableCU and tailCU are dirty in cache

*/

  // advances tailLSN forward by adding a message
  predicate Append(s: Variables, s': Variables, message: Message)
  {
    && s' == s.(openRecord := s.openRecord.Extend(message))
  }

  // advances marshalledLSN forward by marshalling a batch of messages into a dirty cache page
  predicate AdvanceMarshalled(s: Variables, s': Variables, cop: CacheIfc.Ops)
  {
    && var cu := AllocateEmptyCU(s);
    // Marshal and write the current record out into the cache. (This doesn't issue
    // a disk write, it just dirties a page.)
    && var jr := JournalRecord(s.openRecord, s.tailCU)
    && cop == [CacheIfc.Write(cu, marshal(jr))]
    && s' == s.(
      // Open a new, empty record to absorb future journal Appends
      openRecord := MsgSeq([], s.openRecord.seqEnd, s.openRecord.seqEnd)
      seqToAU := MergeAu(s.seqToAU, cu.au, s.openRecord))
  }

  // advances durableLSN forward by learning that the cache has written back a contiguous
  // sequence of pages starting at last durableCU
  predicate AdvanceDurable(s: Variables, s': Variables, int k, cache: CacheIfc.Variables)
  {
    && var jc := JournalChain(marshalledCU, durableCU, cache);
    && (forall i | 0<i<k :: cache.IsClean(jc[i]))
    && s' == s.(durableCU := jc[k])
  }

  predicate Reallocate(s: Variables, s': Variables)
  {
    false // does something with allocation table?
  }

  function ParseCachedRecord(cache: CacheIfc.Variables, cu: CU) : Option<JournalRecord>
  {
    var raw := CacheIfc.ReadValue(s, cu);
    if raw.Some? then parse(raw.value) else None
  }

  // Agrees to advance persistentLSN (to durableLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundary: LSN)
  {
    // Boundary advances from oldBoundary to newBoundary (maybe zero)
    && var oldBoundary := s.firstValidLSN;
    && oldBoundary <= newBoundary // presumably provable from Inv

    // Persistent advances from oldPersistent to durableLSN
    && var oldPersistent := /*s.persistentTailLSN computable from cur sb*/;
    && var newPersistent := s.durableLSN; // TODO compute from durableCU and LSN<->cu relation?
    && oldPersistent <= newPersistent;

    //
    && sb == Superblock(CoreSuperblock(s.durableTailCU, newBoundary), allocationInfo)
    && s' == s
  }

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, sb: Superblock)
  {
    && s.WF()
    && s'.firstValidLSN == sb.core.firstValidLSN  // bump the boundary forward now.
    && s'.durableTailCU == s.durableTailCU
    && s'.seqStart == s.seqStart
    && s'.journal == s.journal
    && s'.seqToAU == (map seqno | s'.firstValidLSN <= seqno < s'.seqStart :: s.seqToAU[seqno])
    && s'.syncReqs == s.syncReqs
  }


//////////////////////////////////////////////////////////////////////////////

  predicate SeqsCoveredByAllocation(s:Variables, seqStart: LSN, seqEndExclusive: LSN, allocation: AllocationTableMod.Superblock)
  {
    false
  }

  predicate Record(s: Variables, s': Variables, message: Message)
  {
    && s' == s.(journal := s.journal + [Message(message)])
  }

  predicate InitiateJournalWriteNoop(s: Variables, s': Variables)
  {
    false
  }

  predicate CompleteJournalWriteNoop(s: Variables, s': Variables)
  {
    false
  }

  predicate InitiateSuperblockWriteNoop(s: Variables, s': Variables)
  {
    false
  }

  predicate AsyncFlush(s: Variables, s': Variables)
  {
    false
    // Complete superblock write
    // a superblock write hits the disk and commits seqStart .. seqStart + inFlightWriteCount
  }

  function endLSNExclusive(firstValidLSN: LSN, cu: Option<CU>) : LSN
  {
    0 //TODO
  }

  // Program keeps track of the "in-flight" superblock. CommitStart(sb) means that sb
  // is being sent to disk, and CommitComplete(sb) is confirmation that sb is now the
  // persistent sb.
  // startBoundary is a binding variable between betree and journal: we should constrain
  // our part of sb to garbage collect the log before startBoundary.
  predicate CommitStart(s: Variables, s': Variables, sb: Superblock, startBoundary: LSN)
  {
    && startBoundary <= s.firstValidLSN
    && SeqsCoveredByAllocation(s, startBoundary, endLSNExclusive(sb.core.firstValidLSN, sb.core.freshestCU), sb.allocation)
    && sb.core.freshestCU == s.durableTailCU
    && sb.core.firstValidLSN == startBoundary
    && s' == s
  }

  predicate CommitComplete(s: Variables, s': Variables, sb: Superblock)
  {
    && s.WF()
    && s.firstValidLSN <= sb.core.firstValidLSN
      // guaranteed inductively -- we don't update s.firstValidLSN except here,
      // CommitStart establishes this relation
      // and Program carries sb from there to here.
    && s'.firstValidLSN == sb.core.firstValidLSN
    && s'.durableTailCU == s.durableTailCU
    && s'.seqStart == s.seqStart
    && s'.journal == s.journal
    && s'.seqToAU == (map seqno | s'.firstValidLSN <= seqno < s'.seqStart :: s.seqToAU[seqno])
    && s'.syncReqs == s.syncReqs
  }

  predicate ReqSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && syncReqId !in s.syncReqs.Keys
    && s' == s.(syncReqs := s.syncReqs[syncReqId := s.seqStart + |s.journal|])
  }

  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && syncReqId in s.syncReqs.Keys
    && s.syncReqs[syncReqId] < endLSNExclusive(s.firstValidLSN, s.durableTailCU)
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, syncReqId))
  }
}

module JournalMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import opened AllocationMod
  import opened JournalMachineMod

  // Synthesize a superblock that reflects the tail of the chain (cutting
  // off the first rec), propagating along firstValidLSN.
  function priorSB(jr:JournalRecord, sb: CoreSuperblock) : CoreSuperblock
  {
    CoreSuperblock(jr.priorCU, sb.firstValidLSN)
  }

  // Monoid-friendly (quantified-list) definition
  datatype JournalChain = JournalChain(sb: CoreSuperblock, recs:seq<JournalRecord>)
  {
    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along firstValidLSN.
    function priorSB() : CoreSuperblock
      requires 0<|recs|
    {
      recs[0].priorSB(sb)
    }
  }

  function parse(b: UninterpretedDiskPage) : Option<JournalRecord>
    // TODO marshalling

  predicate IsLastLink(i: nat, chain: JournalChain)
    requires 0<=i<|chain.recs|
  {
    // stop if nothing more available
    || chain.recs[i].priorCU.None?
    // stop if nothing more needed
    || chain.sb.firstValidLSN >= chain.recs[i].messageSeq.seqStart
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
    requires rec.priorCU.Some? ==> sb.firstValidLSN < rec.messageSeq.seqStart; // proves !IsLastLink(0, chain)
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
      else if firstRec.value.messageSeq.seqEnd <= sb.firstValidLSN then
        // This isn't an invariant disk state: if we're in the initial call,
        // the superblock shouldn't point to a useless JournalRecord; if we're
        // in a recursive call with correctly-chained records, we should have
        // already ignored this case.
        ChainResult(None, [sb.freshestCU.value])
      else if firstRec.value.messageSeq.seqStart == sb.firstValidLSN then
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
          assert firstRec.value.priorCU.Some? ==> sb.firstValidLSN < firstRec.value.messageSeq.seqStart;
          var chain := ExtendChain(sb, firstRec.value, inner.chain.value);
          //var chain := JournalChain(sb, [firstRec.value] + inner.chain.value.recs);
          assert ValidJournalChain(dv, chain) by {
            reveal_ChainMatchesDiskView();
            var cus := CUsForChain(chain);
            assert forall i | 0<=i<|chain.recs| :: RecordOnDisk(dv, cus[i], chain.recs[i]); // trigger
          }
          ChainResult(Some(chain), [sb.freshestCU.value] + inner.readCUs)
  }

  // TODO redo: return a seq of Message, with a prefix of None.
  function MessageMaps(journalChain: JournalChain) : seq<MsgSeq> {
    seq(|journalChain.recs|,
      i requires 0<=i<|journalChain.recs|
        => var mm := journalChain.recs[i].messageSeq; mm)
  }

  // TODO(jonh): collapse to return MsgSeq
  function IM(dv: DiskView, sb: CoreSuperblock) : seq<MsgSeq>
  {
    var chain := ChainFrom(dv, sb).chain;
    if chain.Some?
    then
      MessageMaps(chain.value)
    else
      []
  }

  function ReadAt(cus: seq<CU>, i: nat) : AU
    requires i<|cus|
  {
    cus[i].au
  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(dv: DiskView, sb: CoreSuperblock) : seq<AU>
  {
    var cus := ChainFrom(dv, sb).readCUs;
    // wanted to write:
    // seq(|cus|, i requires 0<=i<|cus| => cus[i].au)
    // but Dafny bug, so:
    seq(|cus|, i requires 0<=i<|cus| => ReadAt(cus, i))
  }

  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }

  lemma DiskViewsEquivalentAfterRemove(dv0: DiskView, dv1: DiskView, aus: seq<AU>, removedCU: CU, ausr: seq<AU>)
    requires DiskViewsEquivalentForSet(dv0, dv1, aus)
    requires SequenceSubset(ausr, aus)
    ensures DiskViewsEquivalentForSet(MapRemove1(dv0, removedCU), MapRemove1(dv1, removedCU), ausr)
  {
  }

  // TODO(jonh): delete chain parameter.
  lemma FrameOneChain(dv0: DiskView, dv1: DiskView, sb: CoreSuperblock, chain: Option<JournalChain>)
    requires chain == ChainFrom(dv0, sb).chain
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures chain == ChainFrom(dv1, sb).chain
    // ensures ChainFrom(dv0, sb).chain == ChainFrom(dv1, sb).chain
  {
    if sb.freshestCU.Some? {
      assert IReads(dv0, sb)[0] == sb.freshestCU.value.au; // trigger
      if sb.freshestCU.value in dv0 {
        var firstRec := parse(dv0[sb.freshestCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.messageSeq.seqEnd <= sb.firstValidLSN {
          } else if firstRec.value.messageSeq.seqStart == sb.firstValidLSN {
          } else {
            var dv0r := MapRemove1(dv0, sb.freshestCU.value);
            var priorCU := firstRec.value.priorCU;
            var priorSB := firstRec.value.priorSB(sb);
            var aus := IReads(dv0, sb);
            var ausr := if priorCU.Some?
              then IReads(dv0r, priorSB)
              else [];

            forall i | 0<=i<|ausr| ensures ausr[i] in aus {
              assert aus[i+1] == ausr[i]; // witness to SequenceSubset(ausr, aus)
            }
            DiskViewsEquivalentAfterRemove(dv0, dv1, aus, sb.freshestCU.value, ausr);
            FrameOneChain(dv0r, MapRemove1(dv1, sb.freshestCU.value),
              priorSB, ChainFrom(dv0r, priorSB).chain);
          }
        }
      }
    }
  }

  lemma Framing(sb:CoreSuperblock, dv0: DiskView, dv1: DiskView)
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures IM(dv0, sb) == IM(dv1, sb)
  {
    FrameOneChain(dv0, dv1, sb, ChainFrom(dv0, sb).chain);
  }
}
