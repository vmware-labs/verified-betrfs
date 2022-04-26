// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournal.i.dfy"

module PagedJournalRefinement
// TODO refines RefinementObligation(JournalLabels, AbstractJournal)
{
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import AbstractJournal
  import opened PagedJournal

  // The user of this module is probably also going to want a lemma about LoadJournal.

  function I(v: Variables) : (out:AbstractJournal.Variables)
    requires v.WF()
    ensures out.WF()
  {
    AbstractJournal.Variables(v.I())
  }

  function ILbl(lbl: TransitionLabel) : AbstractJournal.TransitionLabel
    requires lbl.WF()
  {
    match lbl
      case ReadForRecoveryLabel(messages) => AbstractJournal.ReadForRecoveryLabel(messages)
      case FreezeForCommitLabel(frozenJournal) => AbstractJournal.FreezeForCommitLabel(frozenJournal.I())
      case QueryEndLsnLabel(endLsn) => AbstractJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(messages) => AbstractJournal.PutLabel(messages)
      case DiscardOldLabel(startLsn, requireEnd) => AbstractJournal.DiscardOldLabel(startLsn, requireEnd)
      case InternalLabel() => AbstractJournal.InternalLabel()
  }

  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel, receiptIndex: nat)
    requires ReadForRecovery(v, v', lbl, receiptIndex)
    ensures AbstractJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    var receipt := v.truncatedJournal.BuildReceipt();
    receipt.TJFacts();

    // Base case: messages is in the interp of receipt line i
    assert receipt.OneLinkedInterpretation(receiptIndex) by { receipt.reveal_LinkedInterpretations(); }

    // now induct forward to the last line
    var i := receiptIndex;
    assert 0<i ==> receipt.InterpretationWF(i-1);
    while i<|receipt.lines|-1
      invariant i<|receipt.lines|
      invariant receipt.lines[i].interpretation.value.WF();
      invariant receipt.lines[i].interpretation.value.IncludesSubseq(lbl.messages);
    {
      i := i + 1;
      assert receipt.OneLinkedInterpretation(i) by { receipt.reveal_LinkedInterpretations(); }
    }
  }

  lemma TJFreezeForCommit(tj: TruncatedJournal, frozen: TruncatedJournal, keepReceiptLines: nat)
    requires tj.WF()
    requires tj.FreezeForCommit(frozen, keepReceiptLines)
    ensures tj.I().IncludesSubseq(frozen.I())
  {
    var freezed := tj.FreezeOffRecent(keepReceiptLines);
    tj.BuildReceipt().BoundaryLSN();
    if 0 < keepReceiptLines {
      tj.BuildReceipt().LsnInReceiptBelongs(keepReceiptLines-1);
      tj.BuildReceipt().SnipAtTJValid(keepReceiptLines);
      freezed.BuildReceipt().ReceiptsUnique(tj.BuildReceipt().SnipAt(keepReceiptLines));
      tj.BuildReceipt().AbbreviatedReceiptTJValid(keepReceiptLines-1, freezed.SeqEnd(), freezed);
    }
  }

  lemma FreezeForCommitRefines(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
    requires FreezeForCommit(v, v', lbl, keepReceiptLines)
    ensures v'.WF();
    ensures AbstractJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    var receipt := v.truncatedJournal.BuildReceipt();
    receipt.TJFacts();
    TJFreezeForCommit(v.truncatedJournal, lbl.frozenJournal, keepReceiptLines);
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
    ensures v'.WF()
    ensures AbstractJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    var step: Step :| NextStep(v, v', lbl, step);
    if step.ReadForRecoveryStep? {
      ReadForRecoveryRefines(v, v', lbl, step.receiptIndex);
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.FreezeForCommitStep? {
      FreezeForCommitRefines(v, v', lbl, step.keepReceiptLines);
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.ObserveFreshJournalStep? {
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.PutStep? {
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.DiscardOldStep? {
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.InternalJournalMarshalStep? {
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else {
      assert false;
    }
  }
} // module
