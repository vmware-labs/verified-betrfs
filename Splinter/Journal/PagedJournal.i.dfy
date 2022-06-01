// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"

module PagedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences

  // This PagedJournal module constructs a journal out of a chain of page-sized
  // (immutable, algebraic) journal records.

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: TruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
    | InternalLabel()
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.WF())
    }
  }

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
      && (priorRec.Some? ==> 
        && priorRec.value.WF()
        && priorRec.value.messageSeq.CanConcat(messageSeq)
      )
    }

    predicate Valid(boundaryLSN: LSN) {
      && WF()
      // If you needed to truncate before you got here, you shouldn't be asking for my I()
      && boundaryLSN < messageSeq.seqEnd
      && (|| messageSeq.CanDiscardTo(boundaryLSN)
          || (priorRec.Some? && priorRec.value.Valid(boundaryLSN))
         )
    }

    lemma NewBoundaryValid(oldLSN: LSN, newLSN: LSN)
      requires Valid(oldLSN)
      requires oldLSN <= newLSN
      requires newLSN < messageSeq.seqEnd
      ensures Valid(newLSN)
    {
      if newLSN < messageSeq.seqStart {
        priorRec.value.NewBoundaryValid(oldLSN, newLSN);
      }
    }

    function CroppedPrior(boundaryLSN: LSN) : Option<JournalRecord>
    {
        if messageSeq.seqStart <= boundaryLSN then None else priorRec
    }

    predicate CanCropHeadRecords(boundaryLSN: LSN, depth: nat)
      decreases depth, 0
    {
      && Valid(boundaryLSN)
      && (if depth == 0
        then true // always okay to return self!
        else OptRecCanCropHeadRecords(CroppedPrior(boundaryLSN), boundaryLSN, depth-1)
        )
    }

    function CropHeadRecords(boundaryLSN: LSN, depth: nat) : Option<JournalRecord>
      requires CanCropHeadRecords(boundaryLSN, depth)
      decreases depth, 0
    {
      if depth == 0
      then Some(this)
      else OptRecCropHeadRecords(CroppedPrior(boundaryLSN), boundaryLSN, depth-1)
    }

    lemma CanCropMonotonic(boundaryLSN: LSN, depth: nat, more: nat)
      requires depth < more
      requires CanCropHeadRecords(boundaryLSN, more)
      ensures CanCropHeadRecords(boundaryLSN, depth)
    {
      if 0 < depth {
        CroppedPrior(boundaryLSN).value.CanCropMonotonic(boundaryLSN, depth-1, more-1);
      }
    }

    lemma CanCropMoreYieldsSome(boundaryLSN: LSN, depth: nat, more: nat)
      requires depth < more
      requires CanCropHeadRecords(boundaryLSN, more)
      ensures CanCropHeadRecords(boundaryLSN, depth)  // needed for precondition of real ensures below
      ensures CropHeadRecords(boundaryLSN, depth).Some?
    {
      CanCropMonotonic(boundaryLSN, depth, more);
      if 0 < depth {
        CroppedPrior(boundaryLSN).value.CanCropMoreYieldsSome(boundaryLSN, depth-1, more-1);
      }
    }


    function MessageSeqAfterCrop(boundaryLSN: LSN, depth: nat) : MsgHistory
      requires Valid(boundaryLSN)
      requires CanCropHeadRecords(boundaryLSN, depth+1)
    {
      CanCropMoreYieldsSome(boundaryLSN, depth, depth+1);
      CropHeadRecords(boundaryLSN, depth).value.messageSeq.MaybeDiscardOld(boundaryLSN)
    }
  }

  predicate OptRecCanCropHeadRecords(ojr: Option<JournalRecord>, boundaryLSN: LSN, depth: nat)
    decreases depth, 1
  {
    if ojr.None?
    then depth == 0
    else ojr.value.CanCropHeadRecords(boundaryLSN, depth)
  }

  function OptRecCropHeadRecords(ojr: Option<JournalRecord>, boundaryLSN: LSN, depth: nat) : (out: Option<JournalRecord>)
    requires OptRecCanCropHeadRecords(ojr, boundaryLSN, depth)
    ensures out.Some? ==> out.value.Valid(boundaryLSN)
    decreases depth, 1
  {
    if ojr.None?
    then None
    else ojr.value.CropHeadRecords(boundaryLSN, depth)
  }

  lemma OptionNewBoundaryValid(ojr: Option<JournalRecord>, oldLSN: LSN, newLSN: LSN)
    requires ojr.Some? ==> && ojr.value.Valid(oldLSN)
    requires ojr.Some? ==> newLSN < ojr.value.messageSeq.seqEnd
    requires oldLSN <= newLSN
    ensures ojr.Some? ==> ojr.value.Valid(newLSN)
  {
    if ojr.Some? {
      ojr.value.NewBoundaryValid(oldLSN, newLSN);
    }
  }

  // Recursive "ignorant" discard: throws away old records, but doesn't really
  // have any idea if the records are meaningfully chained; we'll need to assume
  // TJValid later to prove anything about the output of this function.
  function DiscardOldJournalRec(rec: Option<JournalRecord>, lsn: LSN) : (out: Option<JournalRecord>)
    requires rec.Some? ==> rec.value.Valid(lsn)
    ensures out.Some? ==> out.value.Valid(lsn)
  {
    if rec.None?
    then None
    else
      var priorRec := 
        if rec.value.messageSeq.seqStart <= lsn
        then None
        else DiscardOldJournalRec(rec.value.priorRec, lsn);
      Some(JournalRecord(rec.value.messageSeq, priorRec))
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

    predicate WF() {
      && freshestRec.Some? ==> freshestRec.value.Valid(boundaryLSN)
    }

    predicate IsEmpty()
      requires WF()
    {
      freshestRec.None?
    }

    function SeqEnd() : LSN
      requires WF()
    {
      if freshestRec.Some? then freshestRec.value.messageSeq.seqEnd else boundaryLSN
    }

    function SeqStart() : LSN
      requires WF()
    {
      boundaryLSN
    }

    predicate CanDiscardTo(lsn: LSN) 
      requires WF()
    {
      SeqStart() <= lsn <= SeqEnd()
    }

    function DiscardOldDefn(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires CanDiscardTo(lsn)
      ensures out.WF()
    {
      TruncatedJournal(lsn,
        if SeqEnd() == lsn then None
        else
          OptionNewBoundaryValid(freshestRec, boundaryLSN, lsn);
          DiscardOldJournalRec(freshestRec, lsn)
      )
    }

    // msgs appears as the (boundary-truncated) contents of the i'th entry in the
    // chain of JournalRecords
    predicate HasMessagesAtDepth(msgs: MsgHistory, depth: nat)
      requires WF()
      requires msgs.WF()
    {
      && freshestRec.Some?
      && freshestRec.value.CanCropHeadRecords(boundaryLSN, depth+1)
      && freshestRec.value.MessageSeqAfterCrop(boundaryLSN, depth) == msgs
    }

    function AppendRecord(msgs: MsgHistory) : (out: TruncatedJournal)
      requires WF()
      requires msgs.WF()
    {
      this.(freshestRec := Some(JournalRecord(msgs, freshestRec)))
    }

    function CropHeadRecords(depth: nat) : (out: TruncatedJournal)
      requires OptRecCanCropHeadRecords(freshestRec, boundaryLSN, depth)
      ensures out.WF()
    {
      TruncatedJournal(boundaryLSN, OptRecCropHeadRecords(freshestRec, boundaryLSN, depth))
    }

    predicate FreezeForCommit(frozenJournal: TruncatedJournal, depth: nat)
      requires WF()
    {
      && frozenJournal.WF()
      && OptRecCanCropHeadRecords(freshestRec, boundaryLSN, depth)
      && CropHeadRecords(depth).CanDiscardTo(frozenJournal.boundaryLSN)
      // probably want: CropHeadRecords(depth).seqStart <= frozenJournal.boundaryLSN
      && frozenJournal == CropHeadRecords(depth).DiscardOldDefn(frozenJournal.boundaryLSN)
    }
  } // datatype TruncatedJournal

  // TruncatedJournal is the datatype "refinement" of MsgHistory; here we refine the Mkfs function.
  function Mkfs() : (out:TruncatedJournal)
    ensures out.WF()
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
      && truncatedJournal.SeqEnd() == unmarshalledTail.seqStart
    }

    function SeqStart() : LSN
      requires WF()
    {
      truncatedJournal.boundaryLSN
    }

    function SeqEnd() : LSN
      requires WF()
    {
      unmarshalledTail.seqEnd
    }
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && v.WF()
    && lbl.ReadForRecoveryLabel?
    && lbl.messages.WF()
    && v.truncatedJournal.HasMessagesAtDepth(lbl.messages, depth) // subseq appears in committed pages
    && v' == v

    // We don't bother allowing you to "find" the msgs in unmarshalledTail,
    // since the includes operation is only relevant during recovery time,
    // during which the unmarshalledTail is kept empty.
    // (I mean, we COULD allow Puts during that time, but why bother?)
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && v.WF()
    && lbl.FreezeForCommitLabel?
    && v.truncatedJournal.FreezeForCommit(lbl.frozenJournal, depth)
    && v' == v
  }

  predicate ObserveFreshJournal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && lbl.QueryEndLsnLabel?
    && lbl.endLsn == v.SeqEnd()
    && v' == v
  }

  /////////////////////////////////////////////////////////////////////////////
  // implementation of JournalIfc obligations

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && var msgs := lbl.messages;
    && v.WF()
    && msgs.WF()
    && msgs.seqStart == v.SeqEnd()  // CanFollow, but without interpreting this.
    && v' == v.(unmarshalledTail := v.unmarshalledTail.Concat(msgs))
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.DiscardOldLabel?
    && var lsn := lbl.startLsn;
    && v.WF()
    && v.SeqStart() <= lsn <= v.SeqEnd()
    && v.SeqEnd() == lbl.requireEnd
    && v' == (
        if v.unmarshalledTail.seqStart <= lsn
        then
          // NB this branch is goofy -- the policy we've expressed in
          // CoordinationSystem only ever calls this function from
          // CommitComplete, when we've learned that some part of the journal
          // is persistent. No way that could gobble up any of the unmarshalled
          // tail! But we write it out for completeness. (But could have simply
          // excluded this case via an enabling condition, and the lower
          // refinement layers wouldn't have objected.)
          assert lsn <= v.unmarshalledTail.seqEnd;
          Variables(TruncatedJournal(lsn, None), v.unmarshalledTail.DiscardOld(lsn))
        else
          v.(truncatedJournal := v.truncatedJournal.DiscardOldDefn(lsn))
       )
  }

  // A prefix of the unmarshalled tail can be carted off as a new page-sized journal record
  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && lbl.InternalLabel?
    && v.WF()
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
    && v == Variables(tj, EmptyHistoryAt(tj.SeqEnd()))
  }

  datatype Step =
      ReadForRecoveryStep(depth: nat)
    | FreezeForCommitStep(depth: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(depth) => ReadForRecovery(v, v', lbl, depth)
      case FreezeForCommitStep(depth) => FreezeForCommit(v, v', lbl, depth)
      case ObserveFreshJournalStep() => ObserveFreshJournal(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case DiscardOldStep() => DiscardOld(v, v', lbl)
      case InternalJournalMarshalStep(cut) => InternalJournalMarshal(v, v', lbl, cut)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
