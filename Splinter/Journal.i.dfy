// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../Spec/MapSpec.s.dfy"
include "MsgHistory.i.dfy"
include "IndirectionTable.i.dfy"
include "AllocationTable.i.dfy"
include "AllocationTableMachine.i.dfy"
include "../lib/Base/KeyType.s.dfy"

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
  import opened ValueMessage
  import opened KeyType
  import opened InterpMod
  import opened CrashTolerantMapSpecMod
  import opened MsgHistoryMod
  import opened DiskTypesMod
  import opened AllocationMod
  import AllocationTableMachineMod
  import CacheIfc

  datatype Superblock = Superblock(
    freshestCU: Option<CU>,
    boundaryLSN : LSN)  // exclusive: lsns <= boundaryLSN are discarded

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    priorCU: Option<CU>   // linked list pointer
  )
  {
    predicate WF()
    {
      messageSeq.WF()
    }

    function priorSB(sb: Superblock) : Superblock
    {
      Superblock(priorCU, sb.boundaryLSN)
    }
  }

  datatype ChainResult =
    | ChainFailed // missing blocks, or parse failures, or records that don't stitch.

    | ChainSuccess( // the disk had a parseable journal chain on it.
        records: seq<JournalRecord>,
        interp: MsgSeq)
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
      && (ChainSuccess? && !interp.IsEmpty() && next.ChainSuccess? ==> interp.seqEnd == next.interp.seqStart)
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
      else ChainSuccess(records + next.records, interp.Concat(next.interp))
    }

    function lsnMap(cu: Option<CU>) : map<LSN, CU>
    {
      if ChainFailed? || cu.None?
      then
        var empty:set<LSN> := {}; map lsn | lsn in empty :: CU(0, 0)
      else
        map lsn | lsn in interp.LSNSet() :: cu.value
    }
  }

  datatype ChainLookupRow = ChainLookupRow(
    sb: Superblock, // The bounds definition -- first CU, boundaryLSN.
    expectedEnd: Option<LSN>,     // if Some, can't Success if record end doesn't match
    rawPage: Option<UninterpretedDiskPage>, // The page we read from the cache if sb.freshestCU.Some?
    rowResult: ChainResult,        // Can we parse this row and stitch the JournalRecord?
    cumulativeResult: ChainResult, // only ChainSuccess if prior rows also succeed
    cumulativeReadCUs: seq<CU>,    // All the CUs we've read up to this row.
    cumulativeLsnMap: map<LSN, CU> // Which CU explains each LSN in result
    )
  {
    function newReadCUs() : seq<CU> {
      if sb.freshestCU.None? then [] else [sb.freshestCU.value]
    }
    predicate WF() {
      && cumulativeResult.WF()
      // Note: WF doesn't say anything about values of cumulative fields; those get
      // defined in ValidSuccessorTo

      && (
        if sb.freshestCU.None?          // sb doesn't need anything
        then
          && rawPage.None?              // and we didn't read anything
          && rowResult == ChainSuccess([], MsgHistoryMod.Empty())
        else if rawPage.None?           // sb points at a page but we couldn't read it
        then rowResult == ChainFailed
        else if parse(rawPage.value).None? // we couldn't parse the page
        then rowResult == ChainFailed
        else
          var journalRecord := parse(rawPage.value).value;
          if expectedEnd.Some? && expectedEnd.value != journalRecord.messageSeq.seqEnd
            // and we're expecting a particular end value and record didn't stitch
          then rowResult == ChainFailed
          else if journalRecord.messageSeq.seqEnd <= sb.boundaryLSN
            // parsed journal record but don't need any of its entries
          then rowResult == ChainSuccess([], MsgHistoryMod.Empty())
          else rowResult == ChainSuccess([journalRecord], journalRecord.messageSeq)
            // NB that the CU is in our readCUs in either case, whether
            // the journalRecord is in .records or not. TODO document where that's enforced.
        )
    }

    predicate hasRecord()
      requires WF()
    {
      && rowResult.ChainSuccess?
      && sb.freshestCU.Some?
    }

    function journalRec() : JournalRecord
      requires WF() && hasRecord()
    {
      parse(rawPage.value).value
    }

    function readCUs() : seq<CU>
      requires WF()
    {
      if sb.freshestCU.Some? then [sb.freshestCU.value] else []
    }

    function rowLsnMap() : map<LSN, CU>
      requires WF()
    {
      rowResult.lsnMap(sb.freshestCU)
    }

    function priorSB() : Superblock
      requires WF() && hasRecord()
    {
      if
        // We read a JournalRecord
        && sb.freshestCU.Some?
        // and needed more than it had to offer
        && sb.boundaryLSN < journalRec().messageSeq.seqEnd
        // and it had a prior pointer
        && journalRec().priorCU.Some?
      then
        journalRec().priorSB(sb)
      else
        Superblock(None, sb.boundaryLSN)
    }

    predicate FirstRow()
      requires WF()
    {
      || !hasRecord()
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
        && cumulativeReadCUs == readCUs()
        && cumulativeLsnMap == rowLsnMap()
      else
        && prev.Some?
        && prev.value.WF()
        // superblock defines the row; those should link as expected
        && prev.value.sb == priorSB()
        // if prior has a journalRec, its LSNs stitch seamlessly with this one
        && prev.value.expectedEnd == Some(journalRec().messageSeq.seqStart)
        // result success bit accumulates correctly
        && cumulativeResult.ChainSuccess?
          == (rowResult.ChainSuccess? && prev.value.cumulativeResult.ChainSuccess?)
        // result interpretations concatenate correctly
        && (cumulativeResult.ChainSuccess? ==>
            && prev.value.cumulativeResult.Concatable(rowResult)
            && cumulativeResult == prev.value.cumulativeResult.Concat(rowResult)
          )
        // readCUs accumulate correctly
        && cumulativeReadCUs == prev.value.cumulativeReadCUs + readCUs()
        // lsnMaps accumulate correctly
        // (The union is disjoint, but that knowledge requires an inductive proof)
        && cumulativeLsnMap == MapUnionPreferA(prev.value.cumulativeLsnMap, rowLsnMap())
    }

    predicate RespectsDisk(cache: CacheIfc.Variables)
      requires WF()
    {
      sb.freshestCU.Some? ==> rawPage == CacheIfc.ReadValue(cache, sb.freshestCU.value)
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

    predicate RespectsDisk(cache: CacheIfc.Variables)
      requires WF()
    {
      forall idx | 0 <= idx < |rows| :: rows[idx].RespectsDisk(cache)
    }

    predicate Valid(cache: CacheIfc.Variables) {
      && WF()
      && Chained()
      && RespectsDisk(cache)
    }

    predicate ForSB(sb: Superblock)
      requires WF()
    {
      && Last(rows).sb == sb
    }

    predicate ValidForSB(cache: CacheIfc.Variables, sb: Superblock) {
      && WF()
      && Valid(cache)
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

    function interp() : MsgSeq
      requires WF()
      requires success()
    {
      last().cumulativeResult.interp
    }

    function lsnMap() : map<LSN, CU>
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
  }

  function EmptyLSNMap() : map<LSN, CU>
  {
    var empty:set<LSN> := {};
    map lsn | lsn in empty :: CU(0, 0)
  }

  function EmptyChainLookup(sb: Superblock, expectedEnd: Option<LSN>) : (cl: ChainLookup)
    requires sb.freshestCU.None?
    ensures cl.WF()
  {
    var emptyResult := ChainSuccess([], MsgHistoryMod.Empty());
    var clrow := ChainLookupRow(sb, expectedEnd, None, emptyResult, emptyResult, [], EmptyLSNMap());
    assert clrow.WF();
    ChainLookup([clrow])
  }

  // There's only one answer to chain.Valid for a given Cache. Construct it.
  // This looks a lot like WF(), but also tests RespectsDisk (cache contents).
  // Need a sub-function that's recursive, so we need a decreases.
  function ChainFromRecursive(cache: CacheIfc.Variables, sb: Superblock, expectedEnd: Option<LSN>) : (cl:ChainLookup)
    ensures cl.ValidForSB(cache, sb)
    ensures cl.last().expectedEnd == expectedEnd
//    ensures expectedEnd.Some? && cl.success() && !cl.interp().IsEmpty() ==> cl.interp().seqEnd == expectedEnd.value
    decreases if expectedEnd.Some? then 0 else 1, if expectedEnd.Some? then expectedEnd.value else 0
  {
    if sb.freshestCU.None?
    then
      var cl := EmptyChainLookup(sb, expectedEnd);
      //assert cl.interp().seqEnd == maxLsn;
      assert cl.last().expectedEnd == expectedEnd;  // TODO can delete?
      assert cl.WF();
      cl
    else
      var cu := sb.freshestCU.value;
      var rawPage := CacheIfc.ReadValue(cache, cu);
      if rawPage.None?
      then var cl := ChainLookup([ChainLookupRow(sb, expectedEnd, None, ChainFailed, ChainFailed, [cu], EmptyLSNMap())]);
        assert cl.WF(); cl
      else if parse(rawPage.value).None?
      then var cl := ChainLookup([ChainLookupRow(sb, expectedEnd, rawPage, ChainFailed, ChainFailed, [cu], EmptyLSNMap())]);
        assert cl.WF(); cl
      else
        var journalRecord := parse(rawPage.value).value;
        if expectedEnd.Some? && expectedEnd.value != journalRecord.messageSeq.seqEnd
          // we're expecting a particular end value and record didn't stitch
        then var cl := ChainLookup([ChainLookupRow(sb, expectedEnd, rawPage, ChainFailed, ChainFailed, [cu], EmptyLSNMap())]);
          assert cl.WF(); cl
        else if journalRecord.messageSeq.seqEnd <= sb.boundaryLSN
        then // parsed journal record but don't need any of its entries
          var rowResult := ChainSuccess([], MsgHistoryMod.Empty());
          var cl := ChainLookup([ChainLookupRow(sb, expectedEnd, rawPage, rowResult, rowResult, [cu], EmptyLSNMap())]);
          assert cl.WF(); cl
        else
          var rowResult := ChainSuccess([journalRecord], journalRecord.messageSeq);
          var remainder := ChainFromRecursive(cache, journalRecord.priorSB(sb), Some(journalRecord.messageSeq.seqStart));
          var cl := ChainLookup(remainder.rows + [ChainLookupRow(
            sb,
            expectedEnd,
            rawPage,
            rowResult,
            remainder.last().cumulativeResult.Concat(rowResult),
            remainder.last().cumulativeReadCUs+[cu],
            MapUnionPreferA(remainder.lsnMap(), rowResult.lsnMap(sb.freshestCU))
          )]);
          assert cl.Chained() by {
            forall idx | 0 <= idx < |cl.rows| ensures cl.Linked(idx) {
              if idx < |cl.rows|-1 {
                assert remainder.Linked(idx);  // trigger
              }
            }
          }
          assert cl.WF(); // TODO delete
          cl
  }

  lemma ValidPrior(cache: CacheIfc.Variables, cl: ChainLookup)
    requires cl.Valid(cache)
    requires 1 < |cl.rows|
    ensures cl.DropLast().Valid(cache)
  {
    var dl := cl.DropLast();
    forall idx | 0 <= idx < |dl.rows| ensures dl.Linked(idx) {
      assert cl.Linked(idx);
    }
  }

  lemma UniqueChainLookup(cache: CacheIfc.Variables, cla: ChainLookup, clb: ChainLookup)
    requires cla.Valid(cache)
    requires clb.Valid(cache)
    requires cla.last().sb == clb.last().sb
    requires cla.last().expectedEnd == clb.last().expectedEnd
    ensures cla == clb
    decreases |cla.rows|
  {
    // These triggers establish that the two chainlookups have the same number of rows.
    assert cla.Linked(|cla.rows|-1);  // trigger
    assert clb.Linked(|clb.rows|-1);  // trigger

    if 1 < |cla.rows| {
      ValidPrior(cache, cla);
      ValidPrior(cache, clb);
      UniqueChainLookup(cache, cla.DropLast(), clb.DropLast()); // recurse
    }
  }

  function ChainFrom(cache: CacheIfc.Variables, sb: Superblock) : (cl:ChainLookup)
    ensures cl.ValidForSB(cache, sb)
    ensures cl.last().expectedEnd.None?
    ensures forall ocl:ChainLookup | ocl.ValidForSB(cache, sb) && ocl.last().expectedEnd.None? :: ocl == cl
  {
    var cl := ChainFromRecursive(cache, sb, None);
    assert forall ocl:ChainLookup | ocl.ValidForSB(cache, sb) && ocl.last().expectedEnd.None? :: ocl == cl by {
      forall ocl:ChainLookup | ocl.ValidForSB(cache, sb) && ocl.last().expectedEnd.None? ensures ocl == cl {
        UniqueChainLookup(cache, cl, ocl);
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
      // The (exclusive) upper bound of LSNs that have been marshalled into cache
      // blocks.

    unmarshalledTail: seq<KeyedMessage>,
      // The rest of the in-memory journal

    syncReqs: map<SyncReqId, LSN>,
      // The LSN each outstanding SyncRequest was created at. The sync request may be
      // completed when the corresponding LSN <= persistentLSN.

    marshalledLookup: ChainLookup
      // We imagine that the journal can keep track of the entire mapping from LSN to CUs
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
      && marshalledLookup.interp().seqStart == boundaryLSN
      && marshalledLookup.interp().seqEnd == marshalledLSN
    }

    function FreshestMarshalledCU() : Option<CU>
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
      Superblock(FreshestMarshalledCU(), boundaryLSN)
    }

    function lsnMap() : map<LSN, CU>
      requires WF()
    {
      marshalledLookup.last().cumulativeLsnMap
    }
  }

  datatype InitSkolems = InitSkolems(rawJournalRec: UninterpretedDiskPage)

  function MkfsSuperblock() : Superblock
  {
    Superblock(None, 0)
  }

  predicate Init(v: Variables, sb: Superblock, cacheIfc: CacheIfc.Variables, sk: InitSkolems)
  {
    // Can't proceed if there's a freshestCU but we can't read or parse it
    && sb.freshestCU.Some? ==> (
      && CacheIfc.Read(cacheIfc, sb.freshestCU.value, sk.rawJournalRec)
      && parse(sk.rawJournalRec).Some?
      )

    // Figure out where journal ends
    && var lastLSN :=
      if sb.freshestCU.None?
      then
        sb.boundaryLSN
      else
        parse(sk.rawJournalRec).value.messageSeq.seqEnd;

    && v.boundaryLSN == sb.boundaryLSN == 0
    && v.persistentLSN == v.cleanLSN == v.marshalledLSN == lastLSN == 0
    && v.unmarshalledTail == []
    && v.syncReqs == map[]

    // TODO this fails WF! And will require cache to decode
    && v.marshalledLookup == EmptyChainLookup(Superblock(None, 0), None)
  }

  // Recovery coordination
  predicate MessageSeqMatchesJournalAt(v: Variables, puts: MsgSeq)
  {
    true  // TODO THAT'S not likely to prove :)
  }

  // advances tailLSN forward by adding a message
  predicate Append(v: Variables, v': Variables, message: KeyedMessage)
  {
    && v' == v.(unmarshalledTail := v.unmarshalledTail + [message])
  }

  // TODO marshalling
  function parse(b: UninterpretedDiskPage) : (jr: Option<JournalRecord>)
    ensures jr.Some? ==> jr.value.WF()
  function marshal(jr: JournalRecord) : UninterpretedDiskPage

  function TailToMsgSeq(v: Variables) : (result : MsgSeq)
    ensures result.WF()
  {
    var start := v.marshalledLSN;
    var end := v.unmarshalledLSN();
    if start==end
    then MsgHistoryMod.Empty()
    else MsgSeq(map i: LSN | start <= i < end :: v.unmarshalledTail[i - start], start, end)
  }

  // advances marshalledLSN forward by marshalling a batch of messages into a dirty cache page
  predicate AdvanceMarshalled(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, newCU: CU)
  {
    && v.WF()

    // newCU is an unused CU.
    // That could be because the impl has freshly reserved a chunk of CUs from the outer
    // program, or because it's using up a CU from a prior reserved chunk. The impl will
    // batch allocations so it can avoid needing to rewrite the marshaled allocation before
    // commiting a fresh superblock (on sync). Thus "unused" may be computed as "reserved
    // but known not to be in use in the current JournalChain".
    && newCU !in ChainFrom(cache, v.CurrentSuperblock()).last().cumulativeReadCUs

    // Marshal and write the current record out into the cache. (This doesn't issue
    // a disk write, it just dirties a page.)
    && var priorCU := (v.marshalledLookup.LsnMapDomain(); if v.marshalledLSN == v.boundaryLSN then None else Some(v.lsnMap()[v.marshalledLSN-1]));
    && var jr := JournalRecord(TailToMsgSeq(v), priorCU);
    && cacheOps == [CacheIfc.Write(newCU, marshal(jr))]

    // Record the changes to the marshalled, unmarshalled regions, and update the allocation.
    && v' == v.(
      // Open a new, empty record to absorb future journal Appends
      marshalledLSN := v.unmarshalledLSN(),
      unmarshalledTail := [],
      marshalledLookup := v'.marshalledLookup  // Tautology to defer this constraint to next predicate
      )
    // constructive: (map lsn:LSN | 0 <= lsn < v.unmarshalledLSN() :: if lsn < v.marshalledLSN then v.marshalledLookup[lsn] else newCU),
    // predicate:
    && var cache' := CacheIfc.ApplyWrites(cache, cacheOps);
      v'.marshalledLookup == ChainFrom(cache', Superblock(Some(newCU), v.boundaryLSN))
  }

  // advances cleanLSN forward by learning that the cache has written back a contiguous
  // sequence of pages starting at last cleanLSN
  predicate AdvanceClean(v: Variables, v': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, newClean: nat)
  {
    && v.WF()
    && v.cleanLSN < newClean <= v.marshalledLSN
    && (v.marshalledLookup.LsnMapDomain();
       (forall lsn | v.cleanLSN <= lsn < newClean :: && CacheIfc.IsClean(cache, v.lsnMap()[lsn]))
       )
    && v' == v.(cleanLSN := newClean)
    && cacheOps == []
  }

  predicate Reallocate(v: Variables, v': Variables)
  {
    // TODO Allocation isn't what we want, yet. It's tight, so we have to write
    // a new allocation table every time we change the superblock. That's no
    // good!
    && false // does something with allocation table?
  }

  function FreshestCleanCU(v: Variables) : Option<CU>
    requires v.WF()
  {
    v.marshalledLookup.LsnMapDomain();

    if v.cleanLSN == v.boundaryLSN
    then None
    else Some(v.lsnMap()[v.cleanLSN-1])
  }

  // Agrees to advance persistentLSN (to cleanLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(v: Variables, v': Variables, cache: CacheIfc.Variables, sb: Superblock, newBoundaryLSN: LSN, alloc: AllocationTableMachineMod.Variables)
  {
    && v.WF()
    // This is the stuff we'll get to garbage collect when the sb commit completes.
    && v.boundaryLSN <= newBoundaryLSN // presumably provable from Inv

    // These are the LSNs whose syncs will complete when the sb commit completes.
    && v.persistentLSN <= v.cleanLSN  // presumably provable from Inv

    // The allocation we actually commit to is a superset of the allocation we're using.
    && (forall cu | cu in v.lsnMap().Values :: cu in alloc.table)

    // This is the superblock that's going to become persistent.
    && sb == Superblock(FreshestCleanCU(v), newBoundaryLSN)
    && v' == v
  }

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
    && s.WF()

    && s'.boundaryLSN == sb.boundaryLSN

    // Update s'.persistentLSN so that it reflects a persisted LSN (something in the last block,
    // ideally the last LSN in that block). NB This gives impl freedom to not
    // record the latest persistent LSN in the freshestCU block, which would be
    // kind of dumb (it would hold up syncs for no reason), but not unsafe.
    && (if sb.freshestCU.None?
        then s'.persistentLSN == sb.boundaryLSN
        else
          && s'.persistentLSN - 1 in s.lsnMap()
          && s.lsnMap()[s'.persistentLSN - 1] == sb.freshestCU.value
        )
    && s'.cleanLSN == s.cleanLSN
    && s'.marshalledLSN == s.marshalledLSN
    && s'.unmarshalledTail == s.unmarshalledTail
    && s'.syncReqs == s.syncReqs
    && s'.marshalledLookup == ChainFrom(cache, sb)
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

  datatype Skolem =
    | AdvanceMarshalledStep(newCU: CU)
    | AdvanceCleanStep(newClean: nat)

  predicate Internal(s: Variables, s': Variables, cache: CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem) {
    match sk {
      case AdvanceMarshalledStep(newCU) => AdvanceMarshalled(s, s', cache, cacheOps, newCU)
      case AdvanceCleanStep(newClean) => AdvanceClean(s, s', cache, cacheOps, newClean)
//      case _ => false
    }
  }

  function Alloc(s: Variables) : set<CU> {
    {} // TODO
  }
}
