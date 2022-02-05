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

  // On-disk JournalRecords
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgHistory,
    priorRec: Option<JournalRecord>
  )
  {
    predicate WF()
    {
      && messageSeq.WF()

      // Disallow empty records. Means we can always talk about seqEnd
      && messageSeq.MsgHistory?
    }

    // priorSB(tj: TruncatedJournal) : TruncatedJournal
    // ports to tj.prior()
  }

  // A TruncatedJournal is some long chain but which we ignore beyond the boundaryLSN
  // (because we have a map telling us that part of the history).
  // In the refinement layer below, we'll have some situations where the disk has extra
  // journal records, but we'll ignore them in the refinement (since we never read them)
  // and instead supply a None? for the interpretation at this layer.
  // That's what keeps us out of trouble when those un-read pages get reclaimed -- we don't
  // want to have to say we can interpret them.
  datatype TruncatedJournal = TruncatedJournal(
    freshestRec: Option<JournalRecord>,
    boundaryLSN : LSN)  // exclusive: lsns <= boundaryLSN are discarded
  {
    function prior() : TruncatedJournal
      requires freshestRec.Some?
    {
      TruncatedJournal(freshestRec.value.priorRec, boundaryLSN)
    }
  }

  datatype ChainResult =
    | ChainFailed // Records that don't stitch correctly.
      // (In the layer below, missing or unparseable blocks will interpret to None?s here,
      // and those won't stitch.)

    | ChainSuccess( // the chain stitches together.
        records: seq<JournalRecord>,
        interp: MsgHistory)
  {
    predicate WF()
    {
      && (ChainSuccess? ==> interp.WF())
    }

    // 'earlier' is the remainder of our linked list, which should contain earlier LSNs.
    predicate Concatable(earlier: ChainResult)
    {
      && WF()
      && earlier.WF()
      // earlier has at most one record
      && (earlier.ChainSuccess? ==> |earlier.records| <= 1)
    }

    // Stitch another single-record result onto this one.
    function Concat(earlier: ChainResult) : ChainResult
      requires Concatable(earlier)
      ensures Concat(earlier).WF()
    {
      if ChainFailed? || earlier.ChainFailed?
      then ChainFailed
      else if 0 == |earlier.records|
      then this
      else ChainSuccess(records + earlier.records, earlier.interp.Concat(interp))
    }
  }

  datatype ChainLookupRow = ChainLookupRow(
    tj: TruncatedJournal,  // The bounds definition -- boundaryLSN plus the journal it bounds.
    expectedEnd: LSN,     // if hasRecord() && seqEnd != expectedEnd, rowResult.ChainFailed.
      // This is how we can have two chains, one that Successes and one that Faileds, even though
      // they're looking at the same journalRecord. Note that, if !hasRecord(), expectedEnd can
      // be anything, to satisfy the ValidSuccessorTo coming from the next row.
    journalRecord: Option<JournalRecord>,  // The page's if tj.freshestCU.Some?
    rowResult: ChainResult,                // Can we parse this row and stitch the JournalRecord?
    cumulativeResult: ChainResult          // only ChainSuccess if prior rows also succeed
    )
  {
    predicate WF() {
      && cumulativeResult.WF()
      // Note: WF doesn't say anything about values of cumulative fields; those get
      // defined in ValidSuccessorTo

      && (journalRecord.Some? ==> tj.freshestRec.Some?)
      && (journalRecord.Some? ==> journalRecord.value.WF())

      && (
        if tj.freshestRec.None?          // tj doesn't need anything
        then
          && journalRecord.None?
          && rowResult == ChainSuccess([], EmptyHistory)
        else if journalRecord.None?
        then rowResult == ChainFailed // Expected initial journal record, didn't have one
        else
          if expectedEnd != journalRecord.value.messageSeq.seqEnd
            // and we're expecting a particular end value and record didn't stitch
          then rowResult == ChainFailed
          else if journalRecord.value.messageSeq.seqEnd <= tj.boundaryLSN
            // parsed journal record but don't need any of its entries
          then rowResult == ChainSuccess([], EmptyHistory)
          else rowResult == ChainSuccess([journalRecord.value], journalRecord.value.messageSeq)
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

    function priorTJ() : TruncatedJournal
      requires WF() && hasRecord()
    {
      if
        // We read a JournalRecord
        && tj.freshestRec.Some?
        // and needed more than it had to offer
        && tj.boundaryLSN < journalRec().messageSeq.seqEnd
        // and it had a prior pointer
        && journalRec().priorRec.Some?
      then
        tj.prior()
      else
        TruncatedJournal(None, tj.boundaryLSN)
    }

    predicate FirstRow()
      requires WF()
    {
      || tj.freshestRec.None?
      || rowResult.ChainFailed?
      || journalRec().messageSeq.seqEnd <= tj.boundaryLSN
    }

    predicate ValidSuccessorTo(prev: Option<ChainLookupRow>)
      requires WF()
    {
      if FirstRow()
      then
        && prev.None?
        // Accumulators start out correctly
        && cumulativeResult == rowResult
      else
        && prev.Some?
        && prev.value.WF()
        // superblock defines the row; those should link as expected
        && prev.value.tj == tj.prior()
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

    predicate Valid() {
      && WF()
      && Chained()
    }

    predicate ForSB(tj: TruncatedJournal)
      requires WF()
    {
      && Last(rows).tj == tj
    }

    predicate ValidForSB(tj: TruncatedJournal) {
      && Valid()
      && ForSB(tj)
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

  function EmptyChainLookup(tj: TruncatedJournal, expectedEnd: LSN) : (cl: ChainLookup)
    requires tj.freshestRec.None?
    ensures cl.WF()
  {
    var emptyResult := ChainSuccess([], EmptyHistory);
    var clrow := ChainLookupRow(tj, expectedEnd, None, emptyResult, emptyResult);
    assert clrow.WF();
    ChainLookup([clrow])
  }

  // There's only one answer to chain.Valid for a given Cache. Construct it.
  // This looks a lot like WF(), but also tests RespectsDisk (storage contents).
  // Need a sub-function that's recursive, so we need a decreases.
  // expectedEnd is an Option, because, when the entry point ChainFrom calls
  // us, it doesn't know (or care) what expectedEnd value we need; we should
  // supply whatever the journalRec says.
  function ChainFromRecursive(tj: TruncatedJournal, expectedEnd: Option<LSN>) : (cl:ChainLookup)
    ensures cl.ValidForSB(tj)
    ensures expectedEnd.Some? ==> cl.last().expectedEnd == expectedEnd.value
    decreases if expectedEnd.Some? then 0 else 1, if expectedEnd.Some? then expectedEnd.value else 0
  {
    var expectedEndValue := match expectedEnd case Some(lsn) => lsn case None => 0;
    if tj.freshestRec.None?
    then
      var cl := EmptyChainLookup(tj, expectedEndValue);
      assert cl.WF();
      assert cl.ValidForSB(tj);
      cl
    else
      var journalRecord := tj.freshestRec.value;

        if && expectedEnd.Some?
           && (journalRecord.messageSeq.EmptyHistory? || expectedEndValue != journalRecord.messageSeq.seqEnd)
          // we're expecting a particular end value and record didn't stitch
        then
          var row := ChainLookupRow(tj, expectedEndValue, Some(journalRecord), ChainFailed, ChainFailed);
          var cl := ChainLookup([row]);
          assert cl.WF();
          cl
        else if journalRecord.messageSeq.seqEnd <= tj.boundaryLSN
        then // parsed journal record but don't need any of its entries
          var rowResult := ChainSuccess([], EmptyHistory);
          var cl := ChainLookup([ChainLookupRow(tj, journalRecord.messageSeq.seqEnd, Some(journalRecord), rowResult, rowResult)]);
          assert cl.WF();
          cl
        else
          var rowResult := ChainSuccess([journalRecord], journalRecord.messageSeq);
          var remainder := ChainFromRecursive(tj.prior(), Some(journalRecord.messageSeq.seqStart));
          var cl := ChainLookup(remainder.rows + [ChainLookupRow(
            tj,
            journalRecord.messageSeq.seqEnd,
            Some(journalRecord),
            rowResult,
            remainder.last().cumulativeResult.Concat(rowResult)
          )]);
          assert cl.Chained() by {
            forall idx | 0 <= idx < |cl.rows| ensures cl.Linked(idx) {
              if idx < |cl.rows|-1 {
                assert remainder.Linked(idx);  // trigger
              }
            }
          }
          assert cl.WF();
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

  lemma UniqueChainLookup(cla: ChainLookup, clb: ChainLookup)
    requires cla.Valid()
    requires clb.Valid()
    requires cla.last().tj == clb.last().tj
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
      UniqueChainLookup(cla.DropLast(), clb.DropLast()); // recurse
    }
  }

  function {:opaque} ChainFrom(tj: TruncatedJournal) : (cl:ChainLookup)
    ensures cl.Valid()
    ensures cl.Complete()
    ensures forall ocl:ChainLookup | ocl.Valid() && ocl.Complete() :: ocl == cl // TODO um no must share tj
  {
    var cl := ChainFromRecursive(tj, None);
    assert forall ocl:ChainLookup | ocl.Valid() && ocl.Complete() :: ocl == cl by {
      forall ocl:ChainLookup | ocl.Valid() && ocl.Complete() ensures ocl == cl {
      // TODO(jonh): clean up unneeded proof
        assert cl.Complete();
        assert ocl.Complete();
        if cl.last().hasRecord() {
          assert cl.last().tj.freshestRec.Some?;
          assert ocl.last().tj.freshestRec.Some?;
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
        UniqueChainLookup(cl, ocl);
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

    truncatedJournal: TruncatedJournal
      // The linked list of journal pages
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
    }
  }

  datatype InitSkolems = InitSkolems(sbJournalRec: JournalRecord)

  function MkfsTruncatedJournal() : TruncatedJournal
  {
    TruncatedJournal(None, 0)
  }

  predicate Init(v: Variables, tj: TruncatedJournal, sk: InitSkolems)
  {
    // Figure out where journal ends
    && var lastLSN :=
      if tj.freshestRec.None?
      then
        tj.boundaryLSN
      else
        sk.sbJournalRec.messageSeq.seqEnd;

    && v.boundaryLSN == tj.boundaryLSN == 0
    && v.persistentLSN == v.cleanLSN == v.marshalledLSN == lastLSN == 0
    && v.unmarshalledTail == []
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

  // Agrees to advance persistentLSN (to cleanLSN) and firstLSN (to newBoundary, coordinated
  // with BeTree) as part of superblock writeback.
  predicate CommitStart(v: Variables, v': Variables, tj: TruncatedJournal, newBoundaryLSN: LSN)
  {
    && v.WF()
    // This is the stuff we'll get to garbage collect when the tj commit completes.
    && v.boundaryLSN <= newBoundaryLSN // presumably provable from Inv

    // These are the LSNs whose syncs will complete when the tj commit completes.
    && v.persistentLSN <= v.cleanLSN  // presumably provable from Inv

    // everything we're proposing to commit is cleaned
    && newBoundaryLSN <= v.cleanLSN

    // This is the superblock that's going to become persistent.
    // TODO(jonh): this is too strong; we need to separate clean from marshalled, I think, to
    // allow prefix commits.
    && tj == v.truncatedJournal
    && v' == v
  }

  // Learns that coordinated superblock writeback is complete; updates persistentLSN & firstLSN.
  predicate CommitComplete(s: Variables, s': Variables, tj: TruncatedJournal)
  {
    && s.WF()

    && s'.boundaryLSN == tj.boundaryLSN

    && s'.cleanLSN == s.cleanLSN
    && s'.marshalledLSN == s.marshalledLSN
    && s'.unmarshalledTail == s.unmarshalledTail
  }
}

