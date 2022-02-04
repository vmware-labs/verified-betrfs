include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/KeyType.s.dfy"
include "../CoordinationLayer/MsgHistory.i.dfy"

module PagedJournalMod {
  // This module constructs a journal out of a chain of page-sized journal records.
  // We'll show it's equivalent to the abstract MsgHistory in CoordinationLayer.
  import opened Options
  import opened Sequences
  import opened Maps
  import opened ValueMessage
  import opened KeyType
  import opened StampedMapMod
  import opened MsgHistoryMod

  // TODO(jonh): no wait we were not going to represent pointers at all! not at this layer.
  // In the implementation, the PagePointer is a CU. But here we don't know
  // about a storage, all we know is that there's some mapping from PagePointer
  // to our pages.
  type PagePointer(==,!new)
  function ArbitraryPointer() : PagePointer {
    var ptr :| true; ptr
  }

  datatype Superblock = Superblock(
    freshestPtr: Option<PagePointer>,
    boundaryLSN : LSN)  // exclusive: lsns <= boundaryLSN are discarded

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgHistory,
    priorPtr: Option<PagePointer>   // linked list pointer
  )
  {
    predicate WF()
    {
      && messageSeq.WF()

      // Disallow empty records. Means we can always talk about seqEnd
      && messageSeq.MsgHistory?
    }

    function priorSB(sb: Superblock) : Superblock
    {
      Superblock(priorPtr, sb.boundaryLSN)
    }
  }

  // This journal is made up of JournalRecord-typed pages, indexed by PagePointer.
  // A Storage corresponds to the partition of the storage "owned" by the journal, and hence
  // all of those pages hold JournalRecords.
  // An unparseable UninterpretedPage at the level below interprets to just a
  // missing key in this Storage map.
  type Storage = imap<PagePointer, JournalRecord>
  predicate AnyPointer(ptr: PagePointer)
  {
    true
  }
  predicate FullStorage(storage: Storage) {
    forall ptr :: AnyPointer(ptr) <==> ptr in storage
  }

  function EmptyLSNMap() : map<LSN, PagePointer>
  {
    var empty:set<LSN> := {};
    map lsn | lsn in empty :: ArbitraryPointer()
  }

  datatype ChainResult =
    | ChainFailed // missing blocks, or parse failures, or records that don't stitch.

    | ChainSuccess( // the disk had a parseable journal chain on it.
        records: seq<JournalRecord>,
        interp: MsgHistory)
  {
    predicate WF()
    {
      && (ChainSuccess? ==> interp.WF())
    }

    predicate Concatable(next: ChainResult)
    {
      && WF()
      && next.WF()
      // next has at most one record
      && (next.ChainSuccess? ==> |next.records| <= 1)
      // this and next both success => they have linking LSNs
      && (&& ChainSuccess?
          && next.ChainSuccess?
          ==>
          && next.interp.MsgHistory?
          && interp.CanFollow(next.interp.seqEnd))
    }

    // Stitch another single-record result onto this one.
    function Concat(next: ChainResult) : ChainResult
      requires Concatable(next)
      ensures Concat(next).WF()
    {
      if ChainFailed? || next.ChainFailed?
      then ChainFailed
      else if 0 == |next.records|
      then this
      else ChainSuccess(records + next.records, next.interp.Concat(interp))
    }

    function lsnMap(cu: Option<PagePointer>) : map<LSN, PagePointer>
    {
      if ChainFailed? || cu.None?
      then
        EmptyLSNMap()
      else
        map lsn | lsn in interp.LSNSet() :: cu.value
    }
  }

  datatype ChainLookupRow = ChainLookupRow(
    sb: Superblock, // The bounds definition -- first PagePointer, boundaryLSN.
    expectedEnd: LSN,     // if hasRecord() && seqEnd != expectedEnd, rowResult.ChainFailed.
      // This is how we can have two chains, one that Successes and one that Faileds, even though
      // they're looking at the same journalRecord. Note that, if !hasRecord(), expectedEnd can
      // be anything, to satisfy the ValidSuccessorTo coming from the next row.
    journalRecord: Option<JournalRecord>,  // The page's if sb.freshestCU.Some?
    rowResult: ChainResult,        // Can we parse this row and stitch the JournalRecord?
    cumulativeResult: ChainResult, // only ChainSuccess if prior rows also succeed
    cumulativeReadPtrs: seq<PagePointer>,    // All the PagePointers we've read up to this row.
    cumulativeLsnMap: map<LSN, PagePointer> // Which PagePointer explains each LSN in result
    )
  {
    function newReadPtrs() : seq<PagePointer> {
      if sb.freshestPtr.None? then [] else [sb.freshestPtr.value]
    }
    predicate WF() {
      && cumulativeResult.WF()
      // Note: WF doesn't say anything about values of cumulative fields; those get
      // defined in ValidSuccessorTo

      && (journalRecord.Some? ==> sb.freshestPtr.Some?)
      && (journalRecord.Some? ==> journalRecord.value.WF())

      && (
        if sb.freshestPtr.None?          // sb doesn't need anything
        then
          && journalRecord.None?
          && rowResult == ChainSuccess([], EmptyHistory)
        else if journalRecord.None?
        then rowResult == ChainFailed // Expected journal record, didn't have one
        else
          if expectedEnd != journalRecord.value.messageSeq.seqEnd
            // and we're expecting a particular end value and record didn't stitch
          then rowResult == ChainFailed
          else if journalRecord.value.messageSeq.seqEnd <= sb.boundaryLSN
            // parsed journal record but don't need any of its entries
          then rowResult == ChainSuccess([], EmptyHistory)
          else rowResult == ChainSuccess([journalRecord.value], journalRecord.value.messageSeq)
            // NB that the PagePointer is in our readPtrs in either case, whether
            // the journalRecord is in .records or not. TODO document where that's enforced.
        )
    }

    predicate hasRecord()
      requires WF()
    {
      && journalRecord.Some?
    }

    function journalRec() : JournalRecord
      requires WF() && hasRecord()
    {
      journalRecord.value
    }

    function readPtrs() : seq<PagePointer>
      requires WF()
    {
      if sb.freshestPtr.Some? then [sb.freshestPtr.value] else []
    }

    function rowLsnMap() : map<LSN, PagePointer>
      requires WF()
    {
      rowResult.lsnMap(sb.freshestPtr)
    }

    function priorSB() : Superblock
      requires WF() && hasRecord()
    {
      if
        // We read a JournalRecord
        && sb.freshestPtr.Some?
        // and needed more than it had to offer
        && sb.boundaryLSN < journalRec().messageSeq.seqEnd
        // and it had a prior pointer
        && journalRec().priorPtr.Some?
      then
        journalRec().priorSB(sb)
      else
        Superblock(None, sb.boundaryLSN)
    }

    predicate FirstRow()
      requires WF()
    {
      || sb.freshestPtr.None?
      || rowResult.ChainFailed?
      || journalRec().messageSeq.seqEnd <= sb.boundaryLSN
    }

    predicate ValidSuccessorTo(prev: Option<ChainLookupRow>)
      requires WF()
    {
      if FirstRow()
      then
        && prev.None?
        // Accumulators start out correctly
        && cumulativeResult == rowResult
        && cumulativeReadPtrs == readPtrs()
        && cumulativeLsnMap == rowLsnMap()
      else
        && prev.Some?
        && prev.value.WF()
        // superblock defines the row; those should link as expected
        && prev.value.sb == priorSB()
        // if prior has a journalRec, its LSNs stitch seamlessly with this one
        && prev.value.expectedEnd == journalRec().messageSeq.seqStart
        // result success bit accumulates correctly
        && cumulativeResult.ChainSuccess?
          == (rowResult.ChainSuccess? && prev.value.cumulativeResult.ChainSuccess?)
        // result interpretations concatenate correctly
        && (cumulativeResult.ChainSuccess? ==>
            && prev.value.cumulativeResult.Concatable(rowResult)
            && cumulativeResult == prev.value.cumulativeResult.Concat(rowResult)
          )
        // readPtrs accumulate correctly
        && cumulativeReadPtrs == prev.value.cumulativeReadPtrs + readPtrs()
        // lsnMaps accumulate correctly
        // (The union is disjoint, but that knowledge requires an inductive proof)
        && cumulativeLsnMap == MapUnionPreferA(prev.value.cumulativeLsnMap, rowLsnMap())
    }

    predicate RespectsDisk(storage: Storage)
      requires WF()
    {
      sb.freshestPtr.Some? ==>
        && sb.freshestPtr.value in storage
        && journalRecord == Some(storage[sb.freshestPtr.value])
    }
  }

  datatype ChainLookup = ChainLookup(rows:seq<ChainLookupRow>) {
    predicate WF()
    {
      && 0 < |rows|
      && (forall idx | 0 <= idx < |rows| :: rows[idx].WF())
    }

    // Just a syntactic trigger target.
    predicate Linked(idx: nat)
      requires WF()
      requires 0 <= idx < |rows|
    {
      rows[idx].ValidSuccessorTo(if idx==0 then None else Some(rows[idx-1]))
    }

    predicate Chained()
      requires WF()
    {
      forall idx | 0 <= idx < |rows| :: Linked(idx)
    }

    predicate RespectsDisk(storage: Storage)
      requires WF()
    {
      forall idx | 0 <= idx < |rows| :: rows[idx].RespectsDisk(storage)
    }

    predicate Valid(storage: Storage) {
      && WF()
      && Chained()
      && RespectsDisk(storage)
    }

    predicate ForSB(sb: Superblock)
      requires WF()
    {
      && Last(rows).sb == sb
    }

    predicate ValidForSB(storage: Storage, sb: Superblock) {
      && WF()
      && Valid(storage)
      && ForSB(sb)
    }

    // Clients only care about the last row; the previous rows are all proof fodder.
    function last() : ChainLookupRow
      requires WF()
    {
      Last(rows)
    }

    predicate success()
      requires WF()
    {
      && Chained()
      && last().cumulativeResult.ChainSuccess?
    }

    function interp() : MsgHistory
      requires WF()
      requires success()
    {
      last().cumulativeResult.interp
    }

    function lsnMap() : map<LSN, PagePointer>
      requires WF()
    {
      last().cumulativeLsnMap
    }

    lemma SuccessTransitivity()
      requires WF() && success()
      ensures forall i | 0<=i<|rows| :: rows[i].cumulativeResult.ChainSuccess?;
    {
      assert Chained();
      // prove inductively, working down.
      var idx := |rows|-1;
      while 0 < idx
        invariant 0 <= idx
        invariant forall i | idx<=i<|rows| :: rows[i].cumulativeResult.ChainSuccess?
      {
        assert Linked(idx);
        idx := idx - 1;
      }
    }

    lemma LsnMapDomain()
      requires WF() && success()
      ensures lsnMap().Keys == interp().LSNSet()
    {
      SuccessTransitivity();

      var idx := 0;
      while idx < |rows|
        invariant idx <= |rows|
        invariant forall i | 0 <= i < idx :: rows[i].cumulativeLsnMap.Keys == rows[i].cumulativeResult.interp.LSNSet()
      {
        assert Linked(idx);
        idx := idx + 1;
      }
    }

    function DropLast() : ChainLookup
      requires WF()
      requires 1 < |rows| // Have something extra to drop
    {
      ChainLookup(Sequences.DropLast(rows))
    }

    // A "complete" chain lookup is what you get from ChainFrom, when you're not expecting a particular end
    // value. You can't get a ChainFailed due to a mismatched expectedEnd (since you weren't expecting one),
    // and if you don't have a journalRec(), we use a canonical value for expectedEnd.
    // Note that "interior" (non-last()) rows can still have mismatches, because that's how we explain
    // a lookup that Failed due to mismatched records.
    predicate Complete()
      requires WF()
    {
      if last().hasRecord()
      then last().expectedEnd == last().journalRec().messageSeq.seqEnd
      else last().expectedEnd == 0
    }
  }

  function EmptyChainLookup(sb: Superblock, expectedEnd: LSN) : (cl: ChainLookup)
    requires sb.freshestPtr.None?
    ensures cl.WF()
  {
    var emptyResult := ChainSuccess([], EmptyHistory);
    var clrow := ChainLookupRow(sb, expectedEnd, None, emptyResult, emptyResult, [], EmptyLSNMap());
    assert clrow.WF();
    ChainLookup([clrow])
  }

  // There's only one answer to chain.Valid for a given Cache. Construct it.
  // This looks a lot like WF(), but also tests RespectsDisk (storage contents).
  // Need a sub-function that's recursive, so we need a decreases.
  // expectedEnd is an Option, because, when the entry point ChainFrom calls
  // us, it doesn't know (or care) what expectedEnd value we need; we should
  // supply whatever the journalRec says.
  function ChainFromRecursive(storage: Storage, sb: Superblock, expectedEnd: Option<LSN>) : (cl:ChainLookup)
    ensures cl.ValidForSB(storage, sb)
    ensures expectedEnd.Some? ==> cl.last().expectedEnd == expectedEnd.value
    decreases if expectedEnd.Some? then 0 else 1, if expectedEnd.Some? then expectedEnd.value else 0
  {
    var expectedEndValue := match expectedEnd case Some(lsn) => lsn case None => 0;
    if sb.freshestPtr.None?
    then
      var cl := EmptyChainLookup(sb, expectedEndValue);
      assert cl.WF();
      assert cl.ValidForSB(storage, sb);
      cl
    else
      var ptr := sb.freshestPtr.value;
      if ptr !in storage
      then
        var row := ChainLookupRow(sb, expectedEndValue, None, ChainFailed, ChainFailed, [ptr], EmptyLSNMap());
        var cl := ChainLookup([row]);
        assert row.WF();
        assert cl.WF();
        assert cl.Valid(storage);
        assert cl.ValidForSB(storage, sb);
        cl
      else
        var journalRecord := storage[sb.freshestPtr.value];
        if expectedEnd.Some? && expectedEndValue != journalRecord.messageSeq.seqEnd
          // we're expecting a particular end value and record didn't stitch
        then
          var row := ChainLookupRow(sb, expectedEndValue, Some(journalRecord), ChainFailed, ChainFailed, [ptr], EmptyLSNMap());
          var cl := ChainLookup([row]);
          assert cl.WF();
          assert cl.ValidForSB(storage, sb);
          cl
        else if journalRecord.messageSeq.seqEnd <= sb.boundaryLSN
        then // parsed journal record but don't need any of its entries
          var rowResult := ChainSuccess([], EmptyHistory);
          var cl := ChainLookup([ChainLookupRow(sb, journalRecord.messageSeq.seqEnd, Some(journalRecord), rowResult, rowResult, [ptr], EmptyLSNMap())]);
          assert cl.WF();
          assert cl.ValidForSB(storage, sb);
          cl
        else
          var rowResult := ChainSuccess([journalRecord], journalRecord.messageSeq);
          var remainder := ChainFromRecursive(storage, journalRecord.priorSB(sb), Some(journalRecord.messageSeq.seqStart));
          var cl := ChainLookup(remainder.rows + [ChainLookupRow(
            sb,
            journalRecord.messageSeq.seqEnd,
            Some(journalRecord),
            rowResult,
            remainder.last().cumulativeResult.Concat(rowResult),
            remainder.last().cumulativeReadPtrs+[ptr],
            MapUnionPreferA(remainder.lsnMap(), rowResult.lsnMap(sb.freshestPtr))
          )]);
          assert cl.Chained() by {
            forall idx | 0 <= idx < |cl.rows| ensures cl.Linked(idx) {
              if idx < |cl.rows|-1 {
                assert remainder.Linked(idx);  // trigger
              }
            }
          }
          assert cl.WF();
          assert cl.ValidForSB(storage, sb);
          cl
  }

  lemma ChainedPrior(cl: ChainLookup)
    requires cl.WF()
    requires cl.Chained()
    requires 1 < |cl.rows|
    ensures cl.DropLast().Chained()
  {
    var dl := cl.DropLast();
    forall idx | 0 <= idx < |dl.rows| ensures dl.Linked(idx) {
      assert cl.Linked(idx);
    }
  }

  lemma UniqueChainLookup(storage: Storage, cla: ChainLookup, clb: ChainLookup)
    requires cla.Valid(storage)
    requires clb.Valid(storage)
    requires cla.last().sb == clb.last().sb
    requires cla.last().expectedEnd == clb.last().expectedEnd
    ensures cla == clb
    decreases |cla.rows|
  {
    // These triggers establish that the two chainlookups have the same number of rows.
    assert cla.Linked(|cla.rows|-1);  // trigger
    assert clb.Linked(|clb.rows|-1);  // trigger

    if 1 < |cla.rows| {
      ChainedPrior(cla);
      ChainedPrior(clb);
      UniqueChainLookup(storage, cla.DropLast(), clb.DropLast()); // recurse
    }
  }

  function {:opaque} ChainFrom(storage: Storage, sb: Superblock) : (cl:ChainLookup)
    ensures cl.ValidForSB(storage, sb)
    ensures cl.Complete()
    ensures forall ocl:ChainLookup | ocl.ValidForSB(storage, sb) && ocl.Complete() :: ocl == cl
  {
    var cl := ChainFromRecursive(storage, sb, None);
    assert forall ocl:ChainLookup | ocl.ValidForSB(storage, sb) && ocl.Complete() :: ocl == cl by {
      forall ocl:ChainLookup | ocl.ValidForSB(storage, sb) && ocl.Complete() ensures ocl == cl {
      // TODO(jonh): clean up unneeded proof
        assert cl.Complete();
        assert ocl.Complete();
        if cl.last().hasRecord() {
          assert cl.last().sb.freshestPtr.Some?;
          assert ocl.last().sb.freshestPtr.Some?;
          assert cl.last().journalRecord.Some?;
          assert ocl.last().journalRecord.Some?;

          assert cl.last().expectedEnd == cl.last().journalRec().messageSeq.seqEnd;
          assert ocl.Complete();
          assert ocl.last().expectedEnd == ocl.last().journalRec().messageSeq.seqEnd;
          assert ocl.last().rowResult.ChainSuccess?;
          assert ocl.last().hasRecord();
          calc {
            ocl.last().expectedEnd;
            ocl.last().journalRec().messageSeq.seqEnd;
            cl.last().journalRec().messageSeq.seqEnd;
            cl.last().expectedEnd;
          }
        } else {
          assert !ocl.last().hasRecord();
          calc {
            ocl.last().expectedEnd;
            0;
            cl.last().expectedEnd;
          }
        }
        UniqueChainLookup(storage, cl, ocl);
      }
    }
    cl
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
      // The (exclusive) upper bound of LSNs that have been marshalled into storage
      // blocks.

    unmarshalledTail: seq<KeyedMessage>,
      // The rest of the in-memory journal

    marshalledLookup: ChainLookup
      // We imagine that the journal can keep track of the entire mapping from LSN to Ptrs
      // (which we're grabbing here as the cumulativeLsnMap).
      // That's not really how the impl will work; it'll maintain some sort of summary, and
      // we'll refine from the disk state to get this field.
  )
  {
    // A "public" method for Program to inquire where Journal begins
    function JournalBeginsLSNInclusive() : LSN { boundaryLSN }

    // The (exclusive) upper bound of LSNs that have been journaled (in this epoch;
    // after a crash we can lose LSNs that weren't made persistent).
    function unmarshalledLSN() : LSN
    {
      marshalledLSN + |unmarshalledTail|
    }

    predicate WF() {
      && boundaryLSN <= persistentLSN <= cleanLSN <= marshalledLSN
      && marshalledLookup.WF()
      && marshalledLookup.success()
      && marshalledLookup.interp().CanFollow(boundaryLSN)
      && marshalledLookup.interp().SeqEndFor(boundaryLSN) == marshalledLSN
    }

    function FreshestMarshalledPtr() : Option<PagePointer>
      requires WF()
    {
      marshalledLookup.LsnMapDomain();

      if marshalledLSN == boundaryLSN
      then None
      else Some(marshalledLookup.lsnMap()[marshalledLSN-1])
    }

    // This is the superblock that v would use if it all the marshalled stuff were clean
    function CurrentSuperblock() : Superblock
      requires WF()
    {
      Superblock(FreshestMarshalledPtr(), boundaryLSN)
    }

    function lsnMap() : map<LSN, PagePointer>
      requires WF()
    {
      marshalledLookup.last().cumulativeLsnMap
    }
  }

  datatype InitSkolems = InitSkolems(sbJournalRec: JournalRecord)

  function MkfsSuperblock() : Superblock
  {
    Superblock(None, 0)
  }

  predicate Init(v: Variables, sb: Superblock, storage: Storage, sk: InitSkolems)
  {
    // Can't proceed if there's a freshestPtr but there's not a journal page
    // there in the storage.
    && sb.freshestPtr.Some? ==> (
      && sb.freshestPtr.value in storage
      && storage[sb.freshestPtr.value] == sk.sbJournalRec
      )

    // Figure out where journal ends
    && var lastLSN :=
      if sb.freshestPtr.None?
      then
        sb.boundaryLSN
      else
        sk.sbJournalRec.messageSeq.seqEnd;

    && v.boundaryLSN == sb.boundaryLSN == 0
    && v.persistentLSN == v.cleanLSN == v.marshalledLSN == lastLSN == 0
    && v.unmarshalledTail == []

    // TODO this fails WF! And will require storage to decode
    && v.marshalledLookup == EmptyChainLookup(Superblock(None, 0), 0)
  }

  // Recovery coordination
  predicate MessageSeqMatchesJournalAt(v: Variables, puts: MsgHistory)
    requires v.WF()
    requires puts.WF()
  {
    // NB elsewhere in the state machine, we rely only on v.marshalledLookup
    // containing an accurate mapping between LSNs and Ptrs; here, we care about
    // the message seq interpretation as well. So the refined implementation, in
    // addition to maintaining location information, will need to fault in a
    // range of marshalled pages to confirm these contents match during recovery.
    // NB we only consider the marshalledLookup because, during recovery, there
    // had best not be anything in the unmarshalledTail!
    && v.marshalledLookup.interp().IncludesSubseq(puts)
  }

  // advances tailLSN forward by adding a message
  predicate Append(v: Variables, v': Variables, message: KeyedMessage)
  {
    && v' == v.(unmarshalledTail := v.unmarshalledTail + [message])
  }

  function TailToMsgSeq(v: Variables) : (result : MsgHistory)
    ensures result.WF()
  {
    var start := v.marshalledLSN;
    var end := v.unmarshalledLSN();
    if start==end
    then EmptyHistory
    else MsgHistory(map i: LSN | start <= i < end :: v.unmarshalledTail[i - start], start, end)
  }

  // advances marshalledLSN forward by marshalling a batch of messages into a dirty storage page
  predicate AdvanceMarshalled(v: Variables, v': Variables, storage: Storage, storage': Storage, newPtr: PagePointer)
  {
    && v.WF()

    // Not allowed to append empty journal records.
    && 0 < |v.unmarshalledTail|

    // newPtr is an unused PagePointer.
    // That could be because the impl has freshly reserved a chunk of Ptrs from the outer
    // program, or because it's using up a PagePointer from a prior reserved chunk. The impl will
    // batch allocations so it can avoid needing to rewrite the marshaled allocation before
    // commiting a fresh superblock (on sync). Thus "unused" may be computed as "reserved
    // but known not to be in use in the current JournalChain".
    && newPtr !in ChainFrom(storage, v.CurrentSuperblock()).last().cumulativeReadPtrs

    // Marshal and write the current record out into the storage. (This doesn't issue
    // a disk write, it just dirties a page.)
    && var priorPtr := (v.marshalledLookup.LsnMapDomain(); if v.marshalledLSN == v.boundaryLSN then None else Some(v.lsnMap()[v.marshalledLSN-1]));
    && var newRec := JournalRecord(TailToMsgSeq(v), priorPtr);
    && storage' == storage[newPtr := newRec]

    // Record the changes to the marshalled, unmarshalled regions, and update the allocation.
    && v' == v.(
      // Open a new, empty record to absorb future journal Appends
      marshalledLSN := v.unmarshalledLSN(),
      unmarshalledTail := [],
      marshalledLookup := v'.marshalledLookup  // Tautology to defer this constraint to next predicate
      )
    // constructive: (map lsn:LSN | 0 <= lsn < v.unmarshalledLSN() :: if lsn < v.marshalledLSN then v.marshalledLookup[lsn] else newPtr),
    // predicate:
    && FullStorage(storage)
    &&
      //reveal_ChainFrom();
      v'.marshalledLookup == ChainFrom(storage', Superblock(Some(newPtr), v.boundaryLSN))
  }

  // advances cleanLSN forward by learning that the storage has written back a contiguous
  // sequence of pages starting at last cleanLSN
  predicate AdvanceClean(v: Variables, v': Variables, storage: Storage, storage': Storage, newClean: nat)
  {
    && v.WF()
    && v.cleanLSN < newClean <= v.marshalledLSN

    // true conjunct here stands for a cache-clean condition from a layer below.
    // TODO(jonh) Suggests maybe we should remove this state & transition from this model.
    && true

    && v' == v.(cleanLSN := newClean)
    && storage' == storage
  }

  predicate Reallocate(v: Variables, v': Variables)
  {
    // TODO Allocation isn't what we want, yet. It's tight, so we have to write
    // a new allocation table every time we change the superblock. That's no
    // good!
    && false // does something with allocation table?
  }

  function FreshestCleanPtr(v: Variables) : Option<PagePointer>
    requires v.WF()
  {
    v.marshalledLookup.LsnMapDomain();

    if v.cleanLSN == v.boundaryLSN
    then None
    else Some(v.lsnMap()[v.cleanLSN-1])
  }

  // Agrees to advance persistentLSN (to cleanLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(v: Variables, v': Variables, storage: Storage, sb: Superblock, newBoundaryLSN: LSN)
  {
    && v.WF()
    // This is the stuff we'll get to garbage collect when the sb commit completes.
    && v.boundaryLSN <= newBoundaryLSN // presumably provable from Inv

    // These are the LSNs whose syncs will complete when the sb commit completes.
    && v.persistentLSN <= v.cleanLSN  // presumably provable from Inv

    // everything we're proposing to commit is cleaned
    && newBoundaryLSN <= v.cleanLSN

    // This is the superblock that's going to become persistent.
    && sb == Superblock(FreshestCleanPtr(v), newBoundaryLSN)
    && v' == v
  }

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, storage: Storage, sb: Superblock)
  {
    && s.WF()

    && s'.boundaryLSN == sb.boundaryLSN

    // Update s'.persistentLSN so that it reflects a persisted LSN (something in the last block,
    // ideally the last LSN in that block). NB This gives impl freedom to not
    // record the latest persistent LSN in the freshestPtr block, which would be
    // kind of dumb (it would hold up syncs for no reason), but not unsafe.
    && (if sb.freshestPtr.None?
        then s'.persistentLSN == sb.boundaryLSN
        else
          && s'.persistentLSN - 1 in s.lsnMap()
          && s.lsnMap()[s'.persistentLSN - 1] == sb.freshestPtr.value
        )
    && s'.cleanLSN == s.cleanLSN
    && s'.marshalledLSN == s.marshalledLSN
    && s'.unmarshalledTail == s.unmarshalledTail
    && s'.marshalledLookup == ChainFrom(storage, sb)
  }

  datatype Skolem =
    | AdvanceMarshalledStep(newPtr: PagePointer)
    | AdvanceCleanStep(newClean: nat)

  predicate Internal(s: Variables, s': Variables, storage: Storage, storage': Storage, sk: Skolem) {
    match sk {
      case AdvanceMarshalledStep(newPtr) => AdvanceMarshalled(s, s', storage, storage', newPtr)
      case AdvanceCleanStep(newClean) => AdvanceClean(s, s', storage, storage', newClean)
//      case _ => false
    }
  }

  function Alloc(s: Variables) : set<PagePointer> {
    {} // TODO
  }
}

