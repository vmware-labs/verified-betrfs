include "Tables.i.dfy"

// NB the journal needs a smaller-sized-write primitive. If we get asked to sync
// frequently, we don't want to burn an AU on every journal write. Maybe not even
// a CU. Hrmm.
module JournalMachineMod {
  import AllocationTableMachineMod

  type LSN = nat // Log sequence number
    
  datatype Superblock = Superblock(
    allocation: AllocationTableMod.Superblock,
    freshestCU: Option<CU>,
    firstValidLSN : LSN)

  datatype MemJournalRecord = Message(m: Message)

  datatype WriteState =
    | Idle
    | WritingJournal(count: nat)  // Writing seqStart .. seqStart + count

  datatype Variables = Variables(
    firstValidLSN: LSN,
    syncedLSNBoundary: LSN, // Smaller LSNs are reachable from the superblock, i.e. they are safe in the event of a crash
    inFlightSyncedLSNBoundary: Option<LSN>, // Also indicates whether a superblock is currently being written to disk
    durableTailCU: CU, // pointer to the freshest CU that's durable (okay to commit in SB)
    durableTailLSN: LSN, // last durable log sequence number
    inFlightTailCU: Option<CU> // pointer to the CU where record.seqEnd == seqStart
    seqStart: LSN,  // in-memory records start here
    journal: seq<MemJournalRecord>, // in memory records
    seqToAU: map<LSN, AU>,  // Which AU each seq number is stored in.
    syncReqs: map<SyncReqId, LSN>
  )
  {
    predicate seqToAuValid() {
      && forall seqno :: firstValidSeq <= seqno < seqStart <==> seqno in seqToAu.Keys
    }

    predicate WF() {
      && seqToAuValid()
    }
  }

  function AllocationForSeqs(s:Variables, seqStart: LSN, seqEndExclusive: LSN) : multiset<AU>
  {
    multiset seqNum | seqStart <= seqNum < seqEndExclusive :: s.seqToAU[seqNum]
  }

  predicate Record(s: Variables, s': Variables, message: Message)
  {
    && s' == s.(journal := s.journal + [Message(message)])
  }

  predicate InitiateJournalWriteNoop(s: Variables, s': Variables)
  {
  }

  predicate CompleteJournalWriteNoop(s: Variables, s': Variables)
  {
  }

  predicate InitiateSuperblockWriteNoop(s: Variables, s': Variables)
  {
  }

  predicate AsyncFlush(s: Variables, s': Variables)
  {
    // Complete superblock write
    // a superblock write hits the disk and commits seqStart .. seqStart + inFlightWriteCount
  }

  predicate CommitStart(s: Variables, s': Variables, sb: Superblock, startBoundary: nat)
  {
    && s.inFlightSyncedLSNBoundary == None
    && sb.allocation == AllocationForSeqs(s, startBoundary, durableTailLSN)
    && sb.freshestCU == s.durableTailCU
    && sb.firstValidSeq == startBoundary
    && s' == s.(inFlightSyncedLSNBoundary := Some(s.durableTailLSN))
  }

  predicate CommitComplete(s: Variables, s': Variables, sb: Superblock)
  {
    && s.inFlightSyncedLSNBoundary.Some?
    && s'.firstValidSeq             == sb.firstValidSeq
    && s'.syncedLSNBoundary         == s.inFlightSyncedLSNBoundary.value
    && s'.inFlightSyncedLSNBoundary == None
    && s'.durableTailCU             == s.durableTailCU
    && s'.durableTailSeq            == s.durableTailSeq
    && s'.inFlightTailCU            == s.inFlightTailCU
    && s'.seqStart                  == s.seqStart
    && s'.journal                   == s.journal
    && s'.seqToAU                   == map seqno | s'.firstValidSeq <= seqno < s'.seqStart :: s.seqToAU[seqno]
  }

  predicate ReqSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && syncReqId !in s.syncReqs.Keys
    && s' == s.(syncReqs := syncReqs[syncReqs := s.seqStart + |s.journal|])
  }

  predicate CompleteSync(s: Variables, s': Variables, syncReqId: SyncReqId)
  {
    && syncReqId in s.syncReqs.Keys
    && s.syncReqs[syncReqId] < s.syncedLSNBoundary
    && s' == s.(syncReqs := MapRemove(s.syncReqs, syncReqId))
  }
}

module JournalMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import opened AllocationMod

  // Monoid-friendly (quantified-list) definition
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    priorCU: Option<CU>   // linked list pointer
  ) {

    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along firstValidSeq.
    function priorSB(sb: Superblock) : Superblock
    {
      Superblock(priorCU, sb.firstValidSeq)
    }
  }
  datatype JournalChain = JournalChain(sb: Superblock, recs:seq<JournalRecord>)
  {
    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along firstValidSeq.
    function priorSB() : Superblock
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
    || chain.sb.firstValidSeq >= chain.recs[i].seqStart
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
      chain.recs[i].seqStart == chain.recs[i+1].messageSeq.seqEnd)
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

  lemma ValidEmptyChain(dv: DiskView, sb: Superblock)
    requires sb.freshestCU.None?
    ensures ValidJournalChain(dv, JournalChain(sb, []))
  {
    reveal_WFChainInner();
    reveal_ChainMatchesDiskView();
  }

  function ExtendChain(sb: Superblock, rec: JournalRecord, innerchain: JournalChain)
    : (chain: JournalChain)
    requires sb.freshestCU.Some?
    requires rec.priorCU.Some? ==> sb.firstValidSeq < rec.seqStart; // proves !IsLastLink(0, chain)
    requires innerchain.sb == rec.priorSB(sb);
    requires 0<|innerchain.recs| ==> rec.seqStart == innerchain.recs[0].messageSeq.seqEnd;
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

  function ChainFrom(dv: DiskView, sb: Superblock) : (r:ChainResult)
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
      else if firstRec.value.messageSeq.seqEnd <= sb.firstValidSeq then
        // This isn't an invariant disk state: if we're in the initial call,
        // the superblock shouldn't point to a useless JournalRecord; if we're
        // in a recursive call with correctly-chained records, we should have
        // already ignored this case.
        ChainResult(None, [sb.freshestCU.value])
      else if firstRec.value.seqStart == sb.firstValidSeq then
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
              && firstRec.value.seqStart != inner.chain.value.recs[0].messageSeq.seqEnd)
        then
          // failure in recursive call.
          // We read our cu plus however far the recursive call reached.
          ChainResult(None, [sb.freshestCU.value] + inner.readCUs)
        else
          assert firstRec.value.priorCU.Some? ==> sb.firstValidSeq < firstRec.value.seqStart;
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
  function IM(dv: DiskView, sb: Superblock) : seq<MsgSeq>
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

  function IReads(dv: DiskView, sb: Superblock) : seq<AU>
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
  lemma FrameOneChain(dv0: DiskView, dv1: DiskView, sb: Superblock, chain: Option<JournalChain>)
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
          if firstRec.value.messageSeq.seqEnd <= sb.firstValidSeq {
          } else if firstRec.value.seqStart == sb.firstValidSeq {
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

  lemma Framing(sb:Superblock, dv0: DiskView, dv1: DiskView)
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures IM(dv0, sb) == IM(dv1, sb)
  {
    FrameOneChain(dv0, dv1, sb, ChainFrom(dv0, sb).chain);
  }
}
