// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"

module PagedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened JournalLabels

  // This PagedJournal module constructs a journal out of a chain of page-sized
  // (immutable, algebraic) journal records.

  /////////////////////////////////////////////////////////////////////////////
  // A journal is a linked list of these JournalRecords.
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
  }

  // A TruncatedJournal is some long chain but which we ignore beyond the boundaryLSN
  // (because we have a map telling us that part of the history).
  // In the refinement layer below, we'll have some situations where the disk has extra
  // journal records, but we'll ignore them in the refinement (since we never read them)
  // and instead supply a None? for the interpretation at this layer.
  // That's what keeps us out of trouble when those un-read pages get reclaimed -- we don't
  // want to have to say we can interpret them.
  datatype TruncatedJournal = TruncatedJournal(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Option<JournalRecord>)
  {
    function prior() : TruncatedJournal
      requires freshestRec.Some?
    {
      TruncatedJournal(boundaryLSN, freshestRec.value.priorRec)
    }

    function BuildReceiptTJ() : Receipt
    {
      BuildReceipt(boundaryLSN, freshestRec)
    }

    predicate WF() {
      && var receipt := BuildReceiptTJ();
      && receipt.TJValid()
    }

    predicate Empty()
      requires WF()
    {
      freshestRec.None?
    }

    function SeqEnd() : LSN
      requires WF()
      requires !Empty()
    {
      freshestRec.value.messageSeq.seqEnd
    }

    function MaybeSeqEnd() : (out: Option<LSN>)
      requires WF()
    {
      if
        || freshestRec.None?
        || boundaryLSN == freshestRec.value.messageSeq.seqEnd
      then None
      else Some(freshestRec.value.messageSeq.seqEnd)
    }

    function I() : MsgHistory
      requires WF()
    {
      BuildReceiptTJ().I()
    }

    function DiscardOldDefn(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires I().CanDiscardTo(lsn)
    {
      if freshestRec.None? || lsn == freshestRec.value.messageSeq.seqEnd
      then TruncatedJournal(lsn, None)
      else TruncatedJournal(lsn, freshestRec)
    }

    function DiscardOld(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires I().CanDiscardTo(lsn)
      ensures out.WF()
      ensures out.I() == I().DiscardOld(lsn)
    {
      var out := DiscardOldDefn(lsn);
      assert out.WF() && out.I() == I().DiscardOld(lsn) by {
        var discardReceipt := BuildReceiptTJ().DiscardOld(lsn);
        out.BuildReceiptTJ().ReceiptsUnique(discardReceipt);
      }
      out
    }

    // msgs appears as the (boundary-truncated) contents of the i'th entry in the
    // receipt
    predicate IncludesSubseqAt(msgs: MsgHistory, i: nat)
      requires WF()
      requires msgs.WF()
    {
      && i < |BuildReceiptTJ().lines|
      // TODO(jonh): Wait, this allows non-truncated inclusions.
      && BuildReceiptTJ().MessageSeqAt(i).IncludesSubseq(msgs)
    }

    lemma SubseqOfEntireInterpretation(msgs: MsgHistory, i: nat)
      requires WF()
      requires msgs.WF()
      requires IncludesSubseqAt(msgs, i)
      ensures I().IncludesSubseq(msgs)
    {
      // Propagate subseq relation inductively down the receipt
      var receipt := BuildReceiptTJ();
      receipt.TJFacts();
      var j:=i;
      assert receipt.OneLinkedInterpretation(j) by { receipt.reveal_LinkedInterpretations(); }

      while j<|receipt.lines|-1
        invariant j<|receipt.lines|
        invariant var jint := receipt.lines[j].interpretation;
              && jint.Some?  && jint.value.WF() && jint.value.IncludesSubseq(msgs)
      {
        assert receipt.OneLinkedInterpretation(j+1) by { receipt.reveal_LinkedInterpretations(); }
        j:=j+1;
      }
    }

    lemma LsnBelongs(lsn: LSN)
      requires BuildReceiptTJ().TJValid()
      requires !Empty()
      requires boundaryLSN <= lsn < SeqEnd()
      ensures lsn in BuildReceiptTJ().I().LSNSet()
      decreases freshestRec
    {
      if lsn < Last(BuildReceiptTJ().lines).journalRec.messageSeq.seqStart {
        // If it's not it in the last journal record, it's gotta be in here
        // somewhere. Look upstream.
        prior().LsnBelongs(lsn);
      }
    }

    function AppendRecord(msgs: MsgHistory) : (out: TruncatedJournal)
      requires WF()
      requires msgs.WF()
      requires msgs.MsgHistory?
    {
      var newBoundary := if freshestRec.None? then msgs.seqStart else boundaryLSN;
      TruncatedJournal(newBoundary, Some(JournalRecord(msgs, freshestRec)))
    }
  } // datatype TruncatedJournal

  ////////////////////////////////////////////////////////////////////////////
  // Receipt framework
  //
  // A Valid() Receipt is evidence that a JournalRecord does or does not
  // contain a sensible linked list.
  //
  // A TJValid() Receipt is evidence that the JournalRecord DOES contain
  // a sensible linked list.
  //
  // BuildReceipt is evidence that every TruncatedJournal has a Valid receipt.
  //
  // ReceiptsUnique says that any two Valid receipts for the same
  //   TruncatedJournal are identical, so the one you Build matches the
  //   one you get by snipping a line off of another receipt.
  ////////////////////////////////////////////////////////////////////////////

  datatype ReceiptLine = ReceiptLine(
    journalRec: JournalRecord,
    // None means the JournalRecord was malformed, at least with respect to the
    // boundaryLSN.
    interpretation: Option<MsgHistory>)
  {
    predicate WF() {
      && journalRec.WF()
      && (interpretation.Some? ==> interpretation.value.WF())
    }

    function Truncated(boundaryLSN: LSN) : MsgHistory
      requires WF()
    {
      if journalRec.messageSeq.CanDiscardTo(boundaryLSN)
      then journalRec.messageSeq.DiscardOld(boundaryLSN)
      else journalRec.messageSeq
    }

    predicate Borked() { !journalRec.WF() }
    predicate Unused(boundaryLSN: LSN) {
      && journalRec.messageSeq.MsgHistory?
      && journalRec.messageSeq.seqEnd <= boundaryLSN
    }
    predicate ListEnd() { journalRec.priorRec.None? }
    predicate LineTJValid(boundaryLSN: LSN) {
      // The record is well-formed, is a history, and includes the boundaryLSN.
      && journalRec.WF()
      && journalRec.messageSeq.MsgHistory?
      && journalRec.messageSeq.seqStart <= boundaryLSN < journalRec.messageSeq.seqEnd
    }

    // A valid receipt either shows a valid TJ, or shows that the TJ starts in
    // an invalid way.
    predicate ValidFirstLine(boundaryLSN: LSN) {
      || Borked()
      || Unused(boundaryLSN)
      || ListEnd()
      || LineTJValid(boundaryLSN)
    }

    // A valid receipt doesn't have broken stuff in the middle. If something is
    // wrong, it should be wrong at the top of the receipt
    predicate ValidLaterLine(boundaryLSN: LSN) {
      && journalRec.WF()
      && journalRec.messageSeq.MsgHistory?
      && boundaryLSN < journalRec.messageSeq.seqStart
    }
  }

  datatype Receipt = Receipt(boundaryLSN: LSN, lines: seq<ReceiptLine>)
  {
    predicate LineRespectsLinkedList(i: nat)
      requires 0<i<|lines|
    {
      && lines[i].journalRec.priorRec == Some(lines[i-1].journalRec)
    }

    predicate LinesRespectLinkedList()
    {
      forall i | 0<i<|lines| :: LineRespectsLinkedList(i)
    }

    predicate ValidLine(i: nat)
      requires 0<=i<|lines|
    {
      if i==0 then lines[i].ValidFirstLine(boundaryLSN) else lines[i].ValidLaterLine(boundaryLSN)
    }

    predicate ValidLines()
    {
      forall i | 0<=i<|lines| :: ValidLine(i)
    }

    predicate InterpretationWF(i: nat)
      requires i<|lines|
    {
      lines[i].interpretation.Some? ==> lines[i].interpretation.value.WF()
    }

    predicate InterpretationsWF()
    {
      forall i | 0<=i<|lines| :: InterpretationWF(i)
    }

    predicate FirstLineTJValid() {
      0<|lines| ==> lines[0].LineTJValid(boundaryLSN)
    }

    function LinkedInterpretation(i: nat) : Option<MsgHistory>
      requires InterpretationsWF()
      requires i<|lines|
    {
      if !lines[i].WF()
      then None // Bogus line
      else if i==0
      then (
        if !FirstLineTJValid() then None else Some(lines[i].Truncated(boundaryLSN))
      )
      else if lines[i-1].interpretation.None?
      then None // previous line already bogus
      else if
        assert InterpretationWF(i-1); // trigger
        !lines[i-1].interpretation.value.CanConcat(lines[i].journalRec.messageSeq)
      then None // adjacent lines don't stitch
      else Some(lines[i-1].interpretation.value.Concat(lines[i].journalRec.messageSeq))
    }

    predicate OneLinkedInterpretation(i: nat)
      requires InterpretationsWF()
      requires i<|lines|
    {
      lines[i].interpretation == LinkedInterpretation(i)
    }

    predicate {:opaque} LinkedInterpretations() // TODO(jonh): can probably remove opaque now?
      requires InterpretationsWF()
    {
      forall i | 0<=i<|lines| :: OneLinkedInterpretation(i)
    }

    // Valid means this receipt correctly explains the fate of the
    // TruncatedJournal it represents, whether that be its interpretation
    // or the fact that it's uninterpretable.
    predicate Valid()
    {
      && LinesRespectLinkedList()
      && ValidLines()
      && InterpretationsWF()
      && LinkedInterpretations()
    }

    // TJValid means the TruncatedJournal this receipt represents is itself
    // valid -- it has a valid interpretation.
    predicate TJValid()
    {
      && Valid()
      // Final interpretation is happy.
      && (0 < |lines| ==> && Last(lines).interpretation.Some?)
    }

    lemma SomeInterpretation(j: nat)
      requires TJValid()
      requires j <= |lines|
      ensures forall i | j <= i < |lines| :: lines[i].interpretation.Some?
      decreases |lines|-j
    {
      forall i | j <= i < |lines| ensures lines[i].interpretation.Some? {
        if i < |lines|-1 {
          SomeInterpretation(i + 1);  // i+1 is some by induction hypothesis
          assert OneLinkedInterpretation(i+1) by { // if i were None, contradiction!
            reveal_LinkedInterpretations();
          }
        }
      }
    }

    lemma JournalRecsAllWF()
      requires TJValid()
      ensures forall i | 0<=i<|lines| :: lines[i].journalRec.WF()
    {
      SomeInterpretation(0);
      forall i | 0<=i<|lines| ensures lines[i].journalRec.WF() {
        assert InterpretationWF(i); // trigger
        assert OneLinkedInterpretation(i) by { reveal_LinkedInterpretations(); }
      }
    }

    // A package of popular facts about TJValid receipts.
    lemma TJFacts()
      requires TJValid()
      ensures forall i | 0<=i<|lines| :: lines[i].interpretation.Some?
      ensures forall i | 0<=i<|lines| :: lines[i].interpretation.value.MsgHistory?
      ensures forall i | 0<=i<|lines| :: lines[i].journalRec.WF()
      ensures forall i | 0<=i<|lines| :: lines[i].interpretation.value.seqEnd == lines[i].journalRec.messageSeq.seqEnd
      ensures FirstLineTJValid()
      ensures I().WF()
    {
      SomeInterpretation(0);
      JournalRecsAllWF();
      if 0 < |lines| {
        assert OneLinkedInterpretation(0) by { reveal_LinkedInterpretations(); }
      }
      forall i | 0<=i<|lines|
        ensures lines[i].interpretation.value.MsgHistory?
        ensures lines[i].interpretation.value.seqEnd == lines[i].journalRec.messageSeq.seqEnd
      {
        if i>0 {
          assert OneLinkedInterpretation(i) by { reveal_LinkedInterpretations(); }
          assert InterpretationWF(i-1);
        }
      }
      if 0<|lines| { assert InterpretationWF(|lines|-1); } // trigger to get I().WF()
    }

    function I() : MsgHistory
      requires TJValid()
    {
      if |lines|==0
      then EmptyHistory
      else Last(lines).interpretation.value
    }

    // Returns the message history represented by journal page i in this receipt
    function MessageSeqAt(i: nat) : (out:MsgHistory)
      requires i < |lines|
      requires TJValid()  // maybe?
      ensures out.WF()
    {
      var rec := lines[i].journalRec;
      JournalRecsAllWF();
      if rec.messageSeq.CanDiscardTo(boundaryLSN)
      then rec.messageSeq.DiscardOld(boundaryLSN)
      else rec.messageSeq
    }

    function SnipLast() : Receipt
      requires 0 < |lines|
    {
      Receipt(boundaryLSN, DropLast(lines))
    }

    lemma SnippedReceiptValid()
      requires Valid()
      requires 0 < |lines|
      ensures SnipLast().Valid()
    {
      // trigger party.
      forall i | 0<i<|lines|-1 ensures SnipLast().LineRespectsLinkedList(i) {
        assert LineRespectsLinkedList(i);
      }
      reveal_LinkedInterpretations();
      forall i | 0<=i<|lines|-1
        ensures SnipLast().ValidLine(i)
        ensures SnipLast().InterpretationWF(i)
        ensures SnipLast().OneLinkedInterpretation(i)
      {
        assert ValidLine(i);
        assert InterpretationWF(i);
        assert OneLinkedInterpretation(i);
      }
    }

    // You can snip the end off of a TJValid receipt and what's left is still valid.
    // (This is a way to construct a TJValid receipt other than BuildReceipt.)
    lemma SnippedReceiptTJValid()
      requires TJValid()
      requires 0 < |lines|
      ensures SnipLast().TJValid()
    {
      SnippedReceiptValid();
      assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
    }

    function FreshestRec() : Option<JournalRecord>
    {
      if |lines|==0 then None else Some(Last(lines).journalRec)
    }

    function TJ() : TruncatedJournal
    {
      TruncatedJournal(boundaryLSN, FreshestRec())
    }

    lemma ReceiptsUnique(r2: Receipt)
      requires Valid()
      requires r2.Valid()
      requires TJ() == r2.TJ()
      ensures this == r2
      decreases |lines|
    {
      if |lines| == 0 {
        // assert this == r2;  // case boilerplate
      } else {
        SnippedReceiptValid();
        r2.SnippedReceiptValid();
        assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
        assert r2.OneLinkedInterpretation(|r2.lines|-1) by { reveal_LinkedInterpretations(); }

        if 1==|lines| && 1==|r2.lines| {
          // assert this == r2;  // case boilerplate
        } else if 1==|lines| {
          // If I'm out of records, r2 can't keep going.
          assert r2.LineRespectsLinkedList(|r2.lines|-1); // trigger
          assert ValidLine(0);  // trigger
          assert !r2.ValidLine(|r2.lines|-1); // witness to contradiction
        } else if 1==|r2.lines| {
          // symmetric impossible case
          assert LineRespectsLinkedList(|lines|-1); // trigger
          assert r2.ValidLine(0);  // trigger
          assert !ValidLine(|lines|-1); // witness to contradiction
        } else {
          // recurse
          assert r2.LineRespectsLinkedList(|r2.lines|-1); // trigger
          assert LineRespectsLinkedList(|lines|-1); // trigger
          SnipLast().ReceiptsUnique(r2.SnipLast()); // recurse
          // assert this == r2;  // case boilerplate
        }
      }
    }

    lemma AbbreviatedReceiptTJValid(i: nat, endLsn: LSN, tj: TruncatedJournal)
      requires TJValid()
      requires i < |lines|
      requires
        assert lines[i].journalRec.WF() by { TJFacts(); }
        endLsn == lines[i].journalRec.messageSeq.seqEnd
      requires tj == TruncatedJournal(boundaryLSN, Some(lines[i].journalRec))
      ensures tj.WF()
      ensures I().WF()
      ensures I().CanDiscardTo(endLsn)
      ensures tj.I() == I().DiscardRecent(endLsn)
      decreases |lines|
    {
      TJFacts();
      assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
      if i == |lines| - 1 {
        // Receipt for same TJ -> same receipt!
        ReceiptsUnique(tj.BuildReceiptTJ());
      } else if i == |lines|-2 {  
        // just dropping one row from receipt?
        SnippedReceiptTJValid();
        if 1<|lines| {
          tj.BuildReceiptTJ().ReceiptsUnique(SnipLast());
        }
      } else {
        // Dropping many rows; induct.
        SnippedReceiptTJValid();
        SnipLast().AbbreviatedReceiptTJValid(i, endLsn, tj);
      }
    }

    lemma BoundaryLSN()
      requires TJValid()
      ensures I().MsgHistory? ==> I().seqStart == boundaryLSN
      ensures I().MsgHistory? ==> FreshestRec().value.messageSeq.MsgHistory?  // just TJFacts
      ensures I().MsgHistory? ==> I().seqEnd == FreshestRec().value.messageSeq.seqEnd
    {
      TJFacts();
      if I().MsgHistory? {
        var i:nat := 0;
        while i<|lines|
          invariant i<=|lines|
          invariant forall j | 0<=j<i :: lines[j].interpretation.value.seqStart == boundaryLSN
        {
          assert OneLinkedInterpretation(i) by { reveal_LinkedInterpretations(); }
          i := i + 1;
        }
      }
    }

    lemma DiscardOld(lsn: LSN) returns (out:Receipt)
      requires TJValid()
      requires I().CanDiscardTo(lsn)
      ensures out.TJ() == TruncatedJournal(lsn, if I().EmptyHistory? || lsn==I().seqEnd then None else FreshestRec());
//      ensures out == TruncatedJournal(lsn, if I().EmptyHistory? || lsn==I().seqEnd then None else FreshestRec());
      ensures out.TJValid()
      ensures I().WF()
      ensures TJ().WF() // just TJValid + ReceiptsUnique
      ensures TJ().I().CanDiscardTo(lsn);
      ensures out.TJ() == TJ().DiscardOldDefn(lsn)
      ensures out.I() == I().DiscardOld(lsn)
      decreases |lines|
    {
      TJFacts();
      BoundaryLSN();
      ReceiptsUnique(TJ().BuildReceiptTJ());
      if I().EmptyHistory? || lsn == I().seqEnd {
        out := Receipt(lsn, []);
        assert out.TJValid() by { reveal_LinkedInterpretations(); }
        assert out.I() == I().DiscardOld(lsn);  // case boilerplate
      } else if lsn in Last(lines).journalRec.messageSeq.LSNSet() {
        var lastRec := Last(lines).journalRec;
        out := Receipt(lsn, [ReceiptLine(lastRec, Some(lastRec.messageSeq.DiscardOld(lsn)))]);
        assert out.LinkedInterpretations() by { reveal_LinkedInterpretations(); }
        // This is the top of the new receipt
        assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
        assert out.I() == I().DiscardOld(lsn);  // case boilerplate
      } else {
        // Recurse to generate all but the last line of the receipt.
        SnippedReceiptTJValid();
        assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
        var shortReceipt := SnipLast().DiscardOld(lsn); // here's the recursive call.
        // Tack on the last line.
        var lastInterp := shortReceipt.I().Concat(Last(lines).journalRec.messageSeq);
        out := Receipt(lsn, shortReceipt.lines + [ReceiptLine(Last(lines).journalRec, Some(lastInterp))]);

        // trigger party for automation-controlled Valid quantifiers
        forall i | 0<i<|out.lines| ensures out.LineRespectsLinkedList(i) {
          if i < |out.lines|-1 {
            assert shortReceipt.LineRespectsLinkedList(i);  // induction hypothesis
          } else {
            assert LineRespectsLinkedList(|lines|-1);       // new line
          }
        }
        forall i | 0<=i<|out.lines|
          ensures out.ValidLine(i)
          ensures out.InterpretationWF(i)
          ensures out.OneLinkedInterpretation(i)
        {
          if i < |out.lines|-1 {
            assert shortReceipt.ValidLine(i);
            assert shortReceipt.InterpretationWF(i);
            assert shortReceipt.OneLinkedInterpretation(i) by { reveal_LinkedInterpretations(); }
          }
        }
        assert out.Valid() by { reveal_LinkedInterpretations(); }
        assert out.I() == I().DiscardOld(lsn);  // case boilerplate
      }
    }

    lemma LsnInReceiptBelongs(i: nat)
      requires TJValid()
      requires i < |lines|
      ensures lines[i].WF()
      ensures I().CanDiscardTo(lines[i].journalRec.messageSeq.seqEnd)
      decreases |lines|
    {
      TJFacts();
      assert OneLinkedInterpretation(i) by { reveal_LinkedInterpretations(); }
      if i<|lines|-1 {
        SnippedReceiptTJValid();  // recurse
        SnipLast().LsnInReceiptBelongs(i);
        assert OneLinkedInterpretation(|lines|-1) by { reveal_LinkedInterpretations(); }
      }
    }
  } // datatype Receipt

  // Constructive evidence that a Valid receipt exists for each TJ
  function BuildReceipt(boundaryLSN: LSN, optRec: Option<JournalRecord>) : (out:Receipt)
    ensures out.Valid()
  {
    // A global Receipt(0,[]).reveal_LinkedInterpretations() makes this function
    // prove, but because this function's body is reachable from WF, pollutes
    // lots of later CheckWellformeds to run out of resource.
    if optRec.None?
    then var out := Receipt(boundaryLSN, []);
      assert out.Valid() by { Receipt(0,[]).reveal_LinkedInterpretations(); }
      out
    else
      var rec := optRec.value;
      if !rec.WF()
      then
        // Malformed record
        var out := Receipt(boundaryLSN, [ReceiptLine(rec, None)]);
        assert out.Valid() by { Receipt(0,[]).reveal_LinkedInterpretations(); }
        out
      else if rec.messageSeq.seqEnd <= boundaryLSN
      then
        // Uh, this journal record ends before boundaryLSN? Why do we have it?
        var out := Receipt(boundaryLSN, [ReceiptLine(rec, None)]);
        assert out.Valid() by { Receipt(0,[]).reveal_LinkedInterpretations(); }
        out
      else if rec.messageSeq.seqStart <= boundaryLSN
      then
        // boundaryLSN satisfied here; can stop decoding. Don't care what lies
        // beyond!
        var out := Receipt(boundaryLSN, [ReceiptLine(rec, Some(rec.messageSeq.DiscardOld(boundaryLSN)))]);
        assert out.Valid() by { Receipt(0,[]).reveal_LinkedInterpretations(); }
        out
      else if rec.priorRec.None?
      then (
        assert boundaryLSN < rec.messageSeq.seqStart;
        // Uh oh, we needed a prior rec!
        var out := Receipt(boundaryLSN, [ReceiptLine(rec, None)]);
        assert out.Valid() by { Receipt(0,[]).reveal_LinkedInterpretations(); }
        out
      )
      else
        // Recurse.
        var priorReceipt := BuildReceipt(boundaryLSN, rec.priorRec);
        var priorInterpretation := Last(priorReceipt.lines).interpretation;
        var newInterpretation :=
          if
            // Recursion was invalid
            || priorInterpretation.None?
            // Or didn't stitch.
            || !priorInterpretation.value.CanConcat(rec.messageSeq)
          then None
          else Some(priorReceipt.I().Concat(rec.messageSeq));
        var out := Receipt(boundaryLSN,
          priorReceipt.lines + [ReceiptLine(rec, newInterpretation)]);
        assert out.Valid() by {
          // trigger some features of the base case lines
          forall i | 0<=i<|out.lines|
            ensures out.InterpretationWF(i)
            ensures out.ValidLine(i)
          {
            if i<|out.lines|-1 {
              assert priorReceipt.InterpretationWF(i);
              assert priorReceipt.ValidLine(i);
            }
          }
          forall i | 0<i<|out.lines| ensures out.LineRespectsLinkedList(i) {
            if i<|out.lines|-1 {
              assert priorReceipt.LineRespectsLinkedList(i);
            }
          }
          assert out.LinkedInterpretations() by {
            out.reveal_LinkedInterpretations();
            forall i | 0<=i<|out.lines| ensures out.OneLinkedInterpretation(i) {
              if i<|out.lines|-1 {
                assert priorReceipt.OneLinkedInterpretation(i);
              }
            }
          }
        }
        out
  } // BuildReceipt

  // TruncatedJournal is the datatype "refinement" of MsgHistory; here we refine the Mkfs function.
  function Mkfs() : (out:TruncatedJournal)
    ensures out.WF()
    ensures out.I().EmptyHistory?
  {
    TruncatedJournal(0, None)
  }

  /////////////////////////////////////////////////////////////////////////////
  // EphemeralJournal is an TruncatedJournal with an extra unmarshalledTail
  // field to represent entries we have collected in memory but not marhsalled
  // into a JournalRecord yet.

  datatype Variables = Variables(
    truncatedJournal: TruncatedJournal,
    unmarshalledTail: MsgHistory
  )
  {
    predicate WF() {
      && truncatedJournal.WF()
      && unmarshalledTail.WF()
      && (unmarshalledTail.MsgHistory? ==>
          truncatedJournal.I().CanConcat(unmarshalledTail)
         )
    }

    function I() : MsgHistory
      requires WF()
    {
      truncatedJournal.I().Concat(unmarshalledTail)
    }

    predicate Empty()
      requires WF()
    {
      && truncatedJournal.freshestRec.None?
      && unmarshalledTail.EmptyHistory?
    }

    function SeqStart() : Option<LSN>
      requires WF()
      ensures !Empty() ==> SeqStart().Some? && SeqStart().value == I().seqStart
    {
      if Empty()
      then None
      else (
        var out := if truncatedJournal.freshestRec.Some?
          then truncatedJournal.boundaryLSN
          else unmarshalledTail.seqStart;
        assert out == I().seqStart by {
          if truncatedJournal.freshestRec.Some? {
            truncatedJournal.BuildReceiptTJ().BoundaryLSN();
          }
        }
        Some(out)
      )
    }

    function SeqEnd() : Option<LSN>
      requires WF()
    {
      if unmarshalledTail.MsgHistory?
      then Some(unmarshalledTail.seqEnd)
      else truncatedJournal.MaybeSeqEnd()
    }
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, receiptIndex: nat)
  {
    && v.WF()
    && lbl.ReadForRecoveryLabel?
    && lbl.messages.WF()
    && v.truncatedJournal.IncludesSubseqAt(lbl.messages, receiptIndex) // subseq appears in committed pages
    && v' == v

    // We don't bother allowing you to "find" the msgs in unmarshalledTail,
    // since the includes operation is only relevant during recovery time,
    // during which the unmarshalledTail is kept empty.
    // (I mean, we COULD allow Puts during that time, but why bother?)
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
  {
    && v.WF()
    && lbl.FreezeForCommitLabel?
    && lbl.frozenJournal.WF()
    && (v.SeqStart().Some? ==> lbl.startLsn == v.SeqStart().value)
    && (if lbl.startLsn == lbl.endLsn
        then (
          && keepReceiptLines == 0
          && lbl.frozenJournal == EmptyHistory
        ) else (
          && lbl.startLsn < lbl.endLsn
          // Can't freeze anything in unmarshalledTail, as it's certainly not clean on disk.
          // Anything we freeze must start no later than journal is already truncated.
          && v.truncatedJournal.boundaryLSN <= lbl.startLsn
          // And must end at an existing page boundary.
          // (In lower layers, that page and those before it must also be clean on disk.)
          && var receipt := v.truncatedJournal.BuildReceiptTJ();
          && 0 < keepReceiptLines <= |receipt.lines|
          && assert receipt.lines[keepReceiptLines-1].journalRec.messageSeq.MsgHistory? by { receipt.JournalRecsAllWF(); } true
          && lbl.endLsn == receipt.lines[keepReceiptLines-1].journalRec.messageSeq.seqEnd
          && assert lbl.endLsn <= v.truncatedJournal.I().seqEnd by { receipt.LsnInReceiptBelongs(keepReceiptLines-1); } true
          && lbl.frozenJournal == v.truncatedJournal.I().DiscardOld(lbl.startLsn).DiscardRecent(lbl.endLsn)
        )
      )
    && v' == v
  }

  predicate ObserveFreshJournal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.QueryEndLsnLabel?
    && (v.SeqEnd().Some? ==> lbl.endLsn == v.SeqEnd().value)
    && v' == v
  }

  /////////////////////////////////////////////////////////////////////////////
  // implementation of JournalIfc obligations

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && var msgs := lbl.messages;
    && v.WF()
    && v'.WF()
    && msgs.WF()
    && (v.SeqEnd().None? || msgs.EmptyHistory? || msgs.seqStart == v.SeqEnd().value)  // CanFollow, but without interpreting this.
    && v' == v.(unmarshalledTail := v.unmarshalledTail.Concat(msgs))
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.DiscardOldLabel?
    && var lsn := lbl.startLsn;
    && v.WF()
    && v'.WF()
    && (if v.Empty() then true else v.SeqStart().value <= lsn <= v.SeqEnd().value)
    && (if v.Empty() then true else v.SeqEnd().value == lbl.requireEnd)
    && (if v.unmarshalledTail.MsgHistory? && v.unmarshalledTail.seqStart <= lsn
        then v' == Variables(Mkfs(), v.unmarshalledTail.DiscardOld(lsn))
        else v' == v.(truncatedJournal := v.truncatedJournal.DiscardOld(lsn))
       )
  }

  // TODO(jonh): internal operation to truncate old journal garbage
  // Actually I think this only happens in the refinement. At this layer, the receipt just
  // stops when it gets to the end.

  // A prefix of the unmarshalled tail can be carted off as a new page-sized journal record
  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v'.WF()
    && v.unmarshalledTail.MsgHistory?
    && v.unmarshalledTail.seqStart < cut // Can't marshall nothing.
    && v.unmarshalledTail.CanDiscardTo(cut)
    && var marshalledMsgs := v.unmarshalledTail.DiscardRecent(cut);
    && v' == Variables(
      v.truncatedJournal.AppendRecord(marshalledMsgs),
      v.unmarshalledTail.DiscardOld(cut))
  }

  predicate Init(v: Variables, tj: TruncatedJournal)
  {
    && tj.WF()
    && v == Variables(tj, EmptyHistory)
  }

  datatype Step =
      ReadForRecoveryStep(receiptIndex: nat)
    | FreezeForCommitStep(keepReceiptLines: nat)
    | ObserveFreshJournalLabel()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN)

  // TODO(jonh): Per Wednesday meeting with oded & robj, maybe we need a local notion of uiop that
  // forces the refinement to meet the obligations of the client, CoordinationSystem.
  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(receiptIndex) => ReadForRecovery(v, v', lbl, receiptIndex)
      case FreezeForCommitStep(keepReceiptLines) => FreezeForCommit(v, v', lbl, keepReceiptLines)
      case ObserveFreshJournalLabel() => ObserveFreshJournal(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case DiscardOldStep() => DiscardOld(v, v', lbl)
      case InternalJournalMarshalStep(cut) => InternalJournalMarshal(v, v', lbl, cut)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
