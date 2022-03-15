// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournal.i.dfy"

module PagedJournalRefinement
// TODO refines RefinementObligation(mapuiop? journaluiop?, AbstractJournal)
{
  import opened MsgHistoryMod
  import opened LSNMod
  import opened JournalLabels
  import AbstractJournal
  import opened PagedJournal

  // The user of this module is probably also going to want a lemma about LoadJournal.

  function I(v: Variables) : (out:AbstractJournal.Variables)
    requires v.WF()
    ensures out.WF()
  {
    AbstractJournal.Variables(v.I())
  }

  //////////////////////////////////////////////////////////////////////////////
  // non-state-machine function & predicate refinement lemmas

  lemma MkfsRefines()
    ensures Mkfs().I() == AbstractJournal.Mkfs()
  {
  }

  lemma SeqEndMatchesRefines(v: Variables, lsn: LSN)
    requires v.WF()
    ensures v.SeqEndMatches(lsn) <==> I(v).SeqEndMatches(lsn)
  {
  }

  lemma IncludesSubseqRefines(v: Variables, messages: MsgHistory)
    requires v.WF()
    requires messages.WF()
    ensures v.IncludesSubseq(messages) ==> I(v).IncludesSubseq(messages)
  {
    if v.IncludesSubseq(messages) {
      var i:nat :| v.truncatedJournal.IncludesSubseqAt(messages, i);
      var receipt := v.truncatedJournal.BuildReceiptTJ();
      receipt.TJFacts();

      // Base case: messages is in the interp of receipt line i
      assert receipt.OneLinkedInterpretation(i) by { receipt.reveal_LinkedInterpretations(); }

      // now induct forward to the last line
      while i<|receipt.lines|-1
        invariant i<|receipt.lines|
        invariant receipt.lines[i].interpretation.value.WF();
        invariant receipt.lines[i].interpretation.value.IncludesSubseq(messages);
      {
        i := i + 1;
        assert receipt.OneLinkedInterpretation(i) by { receipt.reveal_LinkedInterpretations(); }
      }
    }
  }

  lemma CanFreezeAsRefines(v: Variables, startLsn: LSN, endLsn: LSN, keepReceiptLines: nat) returns (messages: MsgHistory)
    requires v.WF()
    ensures v.CanFreezeAs(startLsn, endLsn, keepReceiptLines) ==> I(v).CanFreezeAs(startLsn, endLsn, messages)
  {
    if v.CanFreezeAs(startLsn, endLsn, keepReceiptLines) {
      if startLsn < endLsn {
        // endLsn-1 is in the interp, so we can discard to endLsn
        var i := keepReceiptLines - 1;
        var receipt := v.truncatedJournal.BuildReceiptTJ();
        receipt.TJFacts();
        v.truncatedJournal.SubseqOfEntireInterpretation(receipt.MessageSeqAt(i), i);
        assert receipt.MessageSeqAt(i).Contains(endLsn-1);  // trigger
      }
      messages := I(v).journal.DiscardOld(startLsn).DiscardRecent(endLsn);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // State machine refinement

  predicate Inv(v: Variables)
  {
    true
  }
  
  lemma InvInit(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {
  }

  lemma InvNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
  {
  }

  lemma InitRefines(v: Variables, tj: TruncatedJournal)
    requires Init(v, tj)
    ensures AbstractJournal.Init(I(v), tj.I())
  {
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures AbstractJournal.Next(I(v), I(v'), lbl)
  {
  }
} // module
