include "JournalIfc.i.dfy"

module PagedJournal refines JournalIfc {
  import opened Sequences

  // This module constructs a journal out of a chain of page-sized journal records.
  // It satisfyies JournalIfc, so it can enjoy the PagedSystemRefinement result.

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

  // Does a JournalRecord begin a sensible linked list?

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
  }

  datatype Receipt = Receipt(boundaryLSN: LSN, lines: seq<ReceiptLine>)
  {
    predicate LineRespectsLinkedList(i: nat)
      requires 0<i<|lines|
    {
      lines[i].journalRec.priorRec == Some(lines[i-1].journalRec)
    }

    predicate LinesRespectLinkedList()
    {
      forall i | 0<i<|lines| :: LineRespectsLinkedList(i)
    }

    predicate FirstLineTJValid()
    {
      // The first record is well-formed, is a history, and includes the boundaryLSN.
      0<|lines| ==> (
        && var jr := lines[0].journalRec;
        && jr.WF()
        && jr.messageSeq.MsgHistory?
        && jr.messageSeq.seqStart <= boundaryLSN < jr.messageSeq.seqEnd
      )
    }

    // A valid receipt either shows a valid TJ, or shows that the TJ starts in
    // an invalid way.
    predicate FirstLineValid()
    {
      0<|lines| ==> (
        // the journalRec is borked (so !TJValid())
        || !lines[0].journalRec.WF()
        // or the first record somehow goes too far into the past (presumably
        // because that's the only record; otherwise stitching would fail first
        // in BuildReceipt).
        || (
          && lines[0].journalRec.messageSeq.MsgHistory?
          && lines[0].journalRec.messageSeq.seqEnd <= boundaryLSN
          )
        // or if we're at the end of the linked list (but perhaps didn't reach the boundaryLSN)
        || lines[0].journalRec.priorRec.None?
        // Or it's actually valid -- it provides boundaryLSN.
        || FirstLineTJValid()
      )
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
      && FirstLineValid()
      && InterpretationsWF()
      && LinkedInterpretations()
    }

    // TJValid means the TruncatedJournal this receipt represents is itself
    // valid -- it has a valid interpretation.
    predicate TJValid()
      requires Valid()
    {
      // Final interpretation is happy.
      && (0 < |lines| ==> && Last(lines).interpretation.Some?)
    }

    lemma SomeInterpretation(j: nat)
      requires Valid()
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
      requires Valid()
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
      requires Valid()
      requires TJValid()
      ensures forall i | 0<=i<|lines| :: lines[i].interpretation.Some?
      ensures forall i | 0<=i<|lines| :: lines[i].journalRec.WF()
      ensures FirstLineTJValid()
    {
      SomeInterpretation(0);
      JournalRecsAllWF();
      if 0 < |lines| {
        assert OneLinkedInterpretation(0) by { reveal_LinkedInterpretations(); }
      }
    }

    function I() : MsgHistory
      requires Valid()
      requires TJValid()
    {
      if |lines|==0
      then EmptyHistory
      else Last(lines).interpretation.value
    }

    // Returns the message history represented by journal page i in this receipt
    function MessageSeqAt(i: nat) : (out:MsgHistory)
      requires i < |lines|
      requires Valid()
      requires TJValid()  // maybe?
      ensures out.WF()
    {
      var rec := lines[i].journalRec;
      JournalRecsAllWF();
      if rec.messageSeq.CanDiscardTo(boundaryLSN)
      then rec.messageSeq.DiscardOld(boundaryLSN)
      else rec.messageSeq
    }
  }

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
          forall i | 0<=i<|out.lines| ensures out.InterpretationWF(i) {
            if i<|out.lines|-1 {
              assert priorReceipt.InterpretationWF(i);
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
      && receipt.Valid()
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

    function I() : MsgHistory
      requires WF()
    {
      BuildReceiptTJ().I()
    }

    function DiscardOld(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires I().CanDiscardTo(lsn)
      ensures out.WF()
      ensures out.I() == I().DiscardOld(lsn)
    {
      assume false;
      TruncatedJournal(lsn, freshestRec)
    }

    // TODO(jonh): We need an internal operation that replaces a chain
    // with another chain with a None instead of a dereference when the
    // links go back before boundaryLSN, to represent journal truncation.

    // msgs appears as the (boundary-truncated) contents of the i'th entry in the
    // receipt
    predicate IncludesSubseqAt(msgs: MsgHistory, i: nat)
      requires WF()
      requires msgs.WF()
    {
      && i < |BuildReceiptTJ().lines|
      //&& BuildReceiptTJ().MessageSeqAt(i) == msgs // TODO deleteme
      && BuildReceiptTJ().MessageSeqAt(i).IncludesSubseq(msgs)
    }

    lemma SubseqEntireOfInterpretation(msgs: MsgHistory, i: nat)
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
      requires BuildReceiptTJ().Valid()
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

// TODO delete
//    predicate InterpretationCanDiscardAt(lsn: LSN, i: nat)
//    {
//      && WF()
//      && i < |BuildReceiptTJ().lines|
//      && var interpi := BuildReceiptTJ().lines[i].interpretation;
//      && interpi.Some?
//      && interpi.value.CanDiscardTo(lsn)
//    }
//
//    lemma InterpretationCanDiscardTo(lsn: LSN, i: nat)
//      requires InterpretationCanDiscardAt(lsn, i)
//      ensures I().CanDiscardTo(lsn)
//    {
//      // Propagate CanDiscardTo relation inductively down the receipt
//      var receipt := BuildReceiptTJ();
//      receipt.SomeInterpretation(0);
//      var j:=i;
//      assert receipt.OneLinkedInterpretation(j) by { receipt.reveal_LinkedInterpretations(); }
//
//      while j<|receipt.lines|-1
//        invariant j<|receipt.lines|
//        invariant var jint := receipt.lines[j].interpretation;
//              && jint.Some?  && jint.value.WF() && jint.value.CanDiscardTo(lsn)
//      {
//        assert receipt.OneLinkedInterpretation(j+1) by { receipt.reveal_LinkedInterpretations(); }
//        assert receipt.lines[j+1].interpretation.value.CanDiscardTo(lsn);
//        j:=j+1;
//      }
//    }
  }

  type PersistentJournal = TruncatedJournal

  datatype EphemeralJournal = EphemeralJournal(
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
  }

  predicate PWF(pj: PersistentJournal) {
    pj.WF()
  }

  predicate EWF(ej: EphemeralJournal) {
    ej.WF()
  }

  function IPJ(pj: PersistentJournal) : (out:MsgHistory) { pj.I() }

  function IEJ(ej: EphemeralJournal) : (out:MsgHistory) { ej.I() }

  function Mkfs() : (out:PersistentJournal)
    //ensures PWF(out)
    //ensures IPJ(out).EmptyHistory?
  {
    TruncatedJournal(0, None)
  }

  function LoadJournal(pj: PersistentJournal) : (out:EphemeralJournal)
    //requires PWF(pj)
    //ensures EWF(out)
    //ensures IEJ(out) == IPJ(pj)
  {
    EphemeralJournal(pj, EmptyHistory)
  }

  function PJournalSeqEnd(pj: PersistentJournal) : Option<LSN>
    // ensures out.Some? == IPJ(pj).MsgHistory?
  {
    if
      || pj.freshestRec.None?
      || pj.boundaryLSN == pj.freshestRec.value.messageSeq.seqEnd
    then None
    else Some(pj.freshestRec.value.messageSeq.seqEnd)
  }

  predicate JournalIncludesSubseq(ej: EphemeralJournal, msgs: MsgHistory)
    //requires EWF(ej)
    //requires msgs.WF()
  {
    // subseq appears in committed pages
    var out := (exists i :: ej.truncatedJournal.IncludesSubseqAt(msgs, i));
    assert out ==> IEJ(ej).IncludesSubseq(msgs) by {
      if out {
        var i :| ej.truncatedJournal.IncludesSubseqAt(msgs, i);
        ej.truncatedJournal.SubseqEntireOfInterpretation(msgs, i);
      }
    }
    out
    // We don't bother allowing you to "find" the msgs in unmarshalledTail,
    // since the includes operation is only relevant during recovery time,
    // during which we don't allow the unmarshalledTail.
    // (I mean, we COULD allow Puts during that time, but why bother?)
  }

  function EJournalSeqEnd(ej: EphemeralJournal) : Option<LSN>
  {
    if ej.unmarshalledTail.MsgHistory?
    then Some(ej.unmarshalledTail.seqEnd)
    else PJournalSeqEnd(ej.truncatedJournal)
  }

  function JournalConcat(ej: EphemeralJournal, msgs: MsgHistory) : (out:EphemeralJournal)
    //requires EWF(ej)
    //requires msgs.WF()
    //requires msgs.EmptyHistory? || EJournalSeqEnd(ej).None? || msgs.CanFollow(EJournalSeqEnd(ej).value)
    // ensures EWF(out)
    // ensures IEJ(ej).Concat(msgs) == IEJ(out)
  {
    EphemeralJournal(ej.truncatedJournal, ej.unmarshalledTail.Concat(msgs))
  }

  // TODO(jonh): a rewrite function that marshalls (some of?) unmarshalledTail

  predicate CanDiscardOld(ej: EphemeralJournal, lsn: LSN)
  {
    // TODO(jonh): ref data structures efficiently, not via the interp
    IEJ(ej).CanDiscardTo(lsn)
  }

  function DiscardOld(ej: EphemeralJournal, lsn: LSN) : EphemeralJournal
    // requires EWF(ej)
    // requires CanDiscardOld(ej, lsn)
  {
    if ej.unmarshalledTail.MsgHistory? && ej.unmarshalledTail.seqStart <= lsn
    then
      EphemeralJournal(Mkfs(), ej.unmarshalledTail.DiscardOld(lsn))
    else
      EphemeralJournal(ej.truncatedJournal.DiscardOld(lsn), ej.unmarshalledTail)
  }

  predicate JournalCanFreezeAt(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN, i: nat)
    requires ej.WF()
  {
    // Can't freeze anything in unmarshalledTail yet!
    && var tj := ej.truncatedJournal;
    // Anything we freeze must start no later than journal is already truncated.
    && tj.boundaryLSN <= startLsn
    // And must end at an existing page boundary.
    // (In lower layers, that page and those before it must also be clean on disk.)
    && var receipt := tj.BuildReceiptTJ();
    && i < |receipt.lines|
    && assert receipt.lines[i].journalRec.messageSeq.MsgHistory? by { receipt.JournalRecsAllWF(); }
    && endLsn == receipt.lines[i].journalRec.messageSeq.seqEnd
    && startLsn <= endLsn
  }

  predicate JournalCanFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
  {
    var out := startLsn==endLsn || (exists i :: JournalCanFreezeAt(ej, startLsn, endLsn, i));
    assert out && startLsn < endLsn ==> IEJ(ej).CanDiscardTo(startLsn) && IEJ(ej).CanDiscardTo(endLsn) by {
      if out && startLsn < endLsn {
	      var i:nat :| JournalCanFreezeAt(ej, startLsn, endLsn, i);
	      var tj := ej.truncatedJournal;

        // endLsn-1 is in the interp, so we can discard to endLsn
        var receipt := tj.BuildReceiptTJ();
        receipt.TJFacts();
        tj.SubseqEntireOfInterpretation(receipt.MessageSeqAt(i), i);
        assert receipt.MessageSeqAt(i).Contains(endLsn-1);  // trigger

        // startLsn is in the interp, so we can discard to it
	      tj.LsnBelongs(startLsn);
      }
    }
    out
  }

  function JournalFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN) : PersistentJournal
    // requires EWF(ej);
    // requires JournalCanFreeze(ej, startLsn, endLsn)
    // ensures PWF(out)
    // ensures IPJ(out) == IEJ(ej).DiscardOld(startLsn).DiscardRecent(endLsn)
  {
    if startLsn==endLsn
    then
      var out := TruncatedJournal(startLsn, None);
      assert PWF(out);
      assert IPJ(out) == IEJ(ej).DiscardOld(startLsn).DiscardRecent(endLsn);
      out
    else
      var tj := ej.truncatedJournal;
      var receiptLines := BuildReceipt(tj.boundaryLSN, tj.freshestRec).lines;
      var i:nat :| JournalCanFreezeAt(ej, startLsn, endLsn, i);
      var out := TruncatedJournal(startLsn, Some(receiptLines[i].journalRec));
      assert PWF(out);
      assert IPJ(out) == IEJ(ej).DiscardOld(startLsn).DiscardRecent(endLsn);
      out
  }

  // TODO(jonh): internal operation to truncate old journal garbage
  // TODO(jonh): internal operation to marshall tail
}
