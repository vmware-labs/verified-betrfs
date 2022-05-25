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

  function ILbl(lbl: TransitionLabel) : AbstractJournal.TransitionLabel
  requires lbl.WF()
  {
    match lbl
      case ReadForRecoveryLabel(messages) => AbstractJournal.ReadForRecoveryLabel(messages)
      case FreezeForCommitLabel(frozenJournal) => AbstractJournal.FreezeForCommitLabel(ITruncatedJournal(frozenJournal))
      case QueryEndLsnLabel(endLsn) => AbstractJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(messages) => AbstractJournal.PutLabel(messages)
      case DiscardOldLabel(startLsn, requireEnd) => AbstractJournal.DiscardOldLabel(startLsn, requireEnd)
      case InternalLabel() => AbstractJournal.InternalLabel()
  }


  function IJournalRecord(jr: JournalRecord, boundaryLSN: LSN) : (out: MsgHistory)
    requires jr.Valid(boundaryLSN)
    ensures out.WF()
    ensures out.seqStart == boundaryLSN
    ensures out.seqEnd == jr.messageSeq.seqEnd
    decreases jr, 0
  {
    if jr.messageSeq.CanDiscardTo(boundaryLSN)
    then jr.messageSeq.DiscardOld(boundaryLSN) // and don't deref the priorRec!
    else IOptionJournalRecord(jr.priorRec, boundaryLSN).Concat(jr.messageSeq)
  }


  function IOptionJournalRecord(ojr: Option<JournalRecord>, boundaryLSN: LSN) : (out: MsgHistory)
    requires ojr.Some? ==> ojr.value.Valid(boundaryLSN)
    ensures out.seqStart == boundaryLSN
    ensures out.WF()
    ensures ojr.Some? ==> out.seqEnd == ojr.value.messageSeq.seqEnd
    decreases ojr, 1
  {
      if ojr.None?
      then EmptyHistoryAt(boundaryLSN)
      else IJournalRecord(ojr.value, boundaryLSN)
  }

  function ITruncatedJournal(tj: TruncatedJournal) : (out: MsgHistory)
    requires tj.WF()
    ensures out.WF()
    ensures out.seqStart == tj.SeqStart()
    ensures out.seqEnd == tj.SeqEnd()
  {
    IOptionJournalRecord(tj.freshestRec, tj.boundaryLSN)
  }

  function I(v: Variables) : (out:AbstractJournal.Variables)
    requires v.WF()
    ensures out.WF()
  {
    AbstractJournal.Variables(ITruncatedJournal(v.truncatedJournal).Concat(v.unmarshalledTail))
  }

  lemma CantCrop(jr: JournalRecord, bdy: LSN, depth: nat) 
    requires 0 < depth
    requires jr.CanCropHeadRecords(bdy, depth-1)
    requires jr.CropHeadRecords(bdy, depth-1).Some?
    requires jr.CropHeadRecords(bdy, depth-1).value.messageSeq.CanDiscardTo(bdy)
    ensures !jr.CanCropHeadRecords(bdy, depth+1)
  {
    if 1 < depth {
      CantCrop(jr.CroppedPrior(bdy).value, bdy, depth-1);
    }
  }

  lemma CropHeadRecordsChaining(jr: JournalRecord, bdy: LSN, depth: nat) 
    requires 0 < depth
    requires jr.CanCropHeadRecords(bdy, depth-1)
    requires jr.CropHeadRecords(bdy, depth-1).Some? 
    requires jr.CanCropHeadRecords(bdy, depth)
    ensures jr.CropHeadRecords(bdy, depth-1).value.CroppedPrior(bdy) == jr.CropHeadRecords(bdy, depth)
  {
    if 1 < depth {
      CropHeadRecordsChaining(jr.CroppedPrior(bdy).value, bdy, depth-1);
    }
  }


  lemma CroppedSubseqInInterpretation(jr: JournalRecord, bdy: LSN, depth: nat, msgs: MsgHistory) 
    requires msgs.WF()
    requires jr.CanCropHeadRecords(bdy, depth+1)
    requires jr.CanCropHeadRecords(bdy, depth)
    requires jr.CropHeadRecords(bdy, depth).Some? 
    requires IJournalRecord(jr.CropHeadRecords(bdy, depth).value, bdy).IncludesSubseq(msgs)
    ensures depth > 0 ==> jr.CanCropHeadRecords(bdy, depth-1)
    ensures IJournalRecord(jr.CropHeadRecords(bdy, 0).value, bdy).IncludesSubseq(msgs)
  {
    if 0 < depth {
      jr.CanCropMonotonic(bdy, depth-1, depth);
      jr.CanCropMoreYieldsSome(bdy, depth-1, depth);
      var jrPre := jr.CropHeadRecords(bdy, depth-1).value;
      assert !jrPre.messageSeq.CanDiscardTo(bdy) by {
        if jrPre.messageSeq.CanDiscardTo(bdy) {
          CantCrop(jr, bdy, depth);
          assert false;
        }
      }
      CropHeadRecordsChaining(jr, bdy, depth); 
      CroppedSubseqInInterpretation(jr, bdy, depth-1, msgs);
    }
  }


  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
    requires ReadForRecovery(v, v', lbl, depth)
    ensures AbstractJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    var ojr := v.truncatedJournal.freshestRec;
    var bdy := v.truncatedJournal.boundaryLSN;
    var msgs := lbl.messages;
    if ojr.Some? {
      ojr.value.CanCropMonotonic(bdy, depth, depth+1);
      ojr.value.CanCropMoreYieldsSome(bdy, depth, depth+1);
      CroppedSubseqInInterpretation(ojr.value, bdy, depth, lbl.messages);
    }
  }


  lemma CanCutMore(ojr: Option<JournalRecord>, bdy: LSN, depth: nat) 
    requires 0 < depth
    requires OptRecCanCropHeadRecords(ojr, bdy, depth)
    ensures OptRecCanCropHeadRecords(ojr, bdy, depth-1)
    ensures OptRecCanCropHeadRecords(OptRecCropHeadRecords(ojr, bdy, depth-1), bdy, 1)
  {
    if 1 < depth {
      ojr.value.CanCropMonotonic(bdy, depth-1, depth);
      CanCutMore(ojr.value.priorRec, bdy, depth-1);
    }
  }


  lemma CropEquivalence(ojr: Option<JournalRecord>, bdy: LSN, depth: nat)
    requires 0 < depth 
    requires ojr.Some? ==> ojr.value.Valid(bdy)
    requires OptRecCanCropHeadRecords(ojr, bdy, depth-1)
    requires OptRecCanCropHeadRecords(ojr, bdy, depth)
    ensures OptRecCanCropHeadRecords(OptRecCropHeadRecords(ojr, bdy, depth-1), bdy, 1)
    ensures OptRecCropHeadRecords(ojr, bdy, depth) == 
      OptRecCropHeadRecords(OptRecCropHeadRecords(ojr, bdy, depth-1), bdy, 1)
    decreases depth
  {
    if 1 < depth {
      CanCutMore(ojr, bdy, depth);
      ojr.value.CanCropMoreYieldsSome(bdy, depth-1, depth);
      CropEquivalence(ojr.value.priorRec, bdy, depth-1);
    }
  }


  lemma DiscardOldMaintainsSubseq(ojr: Option<JournalRecord>, oldBdy: LSN, newBdy: LSN)  
    requires oldBdy <= newBdy
    requires ojr.None? ==> newBdy == oldBdy
    requires ojr.Some? ==> newBdy < ojr.value.messageSeq.seqEnd
    requires ojr.Some? ==> ojr.value.Valid(oldBdy)
    ensures ojr.Some? ==> ojr.value.Valid(newBdy)
    ensures IOptionJournalRecord(ojr, oldBdy).IncludesSubseq(IOptionJournalRecord(DiscardOldJournalRec(ojr, newBdy), newBdy))
  {
    OptionNewBoundaryValid(ojr, oldBdy, newBdy);
    if ojr.Some? && newBdy < ojr.value.messageSeq.seqStart {
      DiscardOldMaintainsSubseq(ojr.value.priorRec, oldBdy, newBdy);
    }
  }


  lemma CropHeadMaintainsSubseq(ojr: Option<JournalRecord>, bdy: LSN, depth: nat)
    requires ojr.Some? ==> ojr.value.Valid(bdy)
    requires OptRecCanCropHeadRecords(ojr, bdy, depth)
    ensures IOptionJournalRecord(ojr, bdy).IncludesSubseq(IOptionJournalRecord(OptRecCropHeadRecords(ojr, bdy, depth), bdy))
  {
    if depth > 0 {
      ojr.value.CanCropMonotonic(bdy, depth-1, depth);
      CropHeadMaintainsSubseq(ojr, bdy, depth-1);
      var small := OptRecCropHeadRecords(ojr, bdy, depth-1);
      var smaller := OptRecCropHeadRecords(ojr, bdy, depth);
      CropEquivalence(ojr, bdy, depth);
      assert OptRecCropHeadRecords(small, bdy, 1) == smaller;
      assert IOptionJournalRecord(small, bdy).IncludesSubseq(IOptionJournalRecord(smaller, bdy));
    }
  }

  lemma TJFreezeForCommit(tj: TruncatedJournal, frozen: TruncatedJournal, depth: nat)
    requires tj.WF()
    requires tj.FreezeForCommit(frozen, depth)
    ensures ITruncatedJournal(tj).IncludesSubseq(ITruncatedJournal(frozen))
  {
    var ctj := tj.CropHeadRecords(depth);
    if ctj.freshestRec.Some? && frozen.boundaryLSN < ctj.freshestRec.value.messageSeq.seqEnd {
      DiscardOldMaintainsSubseq(ctj.freshestRec, ctj.boundaryLSN, frozen.boundaryLSN);
    } 
    CropHeadMaintainsSubseq(tj.freshestRec, tj.boundaryLSN, depth);
  }

  lemma FreezeForCommitRefines(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
    requires FreezeForCommit(v, v', lbl, depth)
    ensures v'.WF();
    ensures AbstractJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    TJFreezeForCommit(v.truncatedJournal, lbl.frozenJournal, depth);
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
    ensures AbstractJournal.Init(I(v), ITruncatedJournal(tj))
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
      ReadForRecoveryRefines(v, v', lbl, step.depth);
      assert AbstractJournal.Next(I(v), I(v'), ILbl(lbl));
    } else if step.FreezeForCommitStep? {
      FreezeForCommitRefines(v, v', lbl, step.depth);
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
