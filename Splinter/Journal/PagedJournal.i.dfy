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

    function I(boundaryLSN: LSN) : (out: MsgHistory)
      requires Valid(boundaryLSN)
      ensures out.WF()
      ensures out.seqStart == boundaryLSN
      decreases this, 0
    {
      if messageSeq.CanDiscardTo(boundaryLSN)
      then messageSeq.DiscardOld(boundaryLSN) // and don't deref the priorRec!
      else IOptionJournalRecord(boundaryLSN, priorRec).Concat(messageSeq)
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

    predicate CanCropHeadRecords(boundaryLSN: LSN, depth: nat)
    {
      && Valid(boundaryLSN)
      && (if depth == 0
        then true // always okay to return self!
        else
          && !(boundaryLSN < messageSeq.seqStart)           // my record isn't last due to boundaryLSN
          && OptRecCanCropHeadRecords(priorRec, boundaryLSN, depth-1) // I have a priorRec
        )
    }

    function CropHeadRecords(boundaryLSN: LSN, depth: nat) : Option<JournalRecord>
      requires CanCropHeadRecords(boundaryLSN, depth)
    {
      if depth == 0
      then Some(this)
      else OptRecCropHeadRecords(priorRec, boundaryLSN, depth-1)
    }

    function MessageSeqAfterCrop(boundaryLSN: LSN, depth: nat) : MsgHistory
      requires Valid(boundaryLSN)
      requires CanCropHeadRecords(boundaryLSN, depth+1)
    {
      CropHeadRecords(boundaryLSN, depth).value.messageSeq
    }
  }

  predicate OptRecCanCropHeadRecords(ojr: Option<JournalRecord>, boundaryLSN: LSN, depth: nat)
  {
    if ojr.None?
    then depth==0
    else ojr.value.CanCropHeadRecords(boundaryLSN, depth)
  }

  function OptRecCropHeadRecords(ojr: Option<JournalRecord>, boundaryLSN: LSN, depth: nat) : Option<JournalRecord>
    requires OptRecCanCropHeadRecords(ojr, boundaryLSN, depth)
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

  function IOptionJournalRecord(boundaryLSN: LSN, ojr: Option<JournalRecord>) : (out: MsgHistory)
    requires ojr.Some? ==> ojr.value.Valid(boundaryLSN)
    ensures out.seqStart == boundaryLSN
    ensures out.seqEnd == if ojr.Some? then ojr.value.messageSeq.seqEnd else boundaryLSN
    ensures out.WF()
    decreases ojr, 1
  {
      if ojr.None?
      then EmptyHistoryAt(boundaryLSN)
      else ojr.value.I(boundaryLSN)
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

    // TODO(tony): LET'S GET I() OUT OF THIS FILE!!!
    function I() : MsgHistory
      requires WF()
      ensures I().WF()
    {
      IOptionJournalRecord(boundaryLSN, freshestRec)
    }

    function DiscardOldDefn(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires I().CanDiscardTo(lsn)  // TODO(tony) replace with condition on boundaryLSN / SeqEnd()
      ensures out.WF()
    {
      TruncatedJournal(lsn,
        if SeqEnd() <= lsn then None
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
      && freshestRec.value.CanCropHeadRecords(boundaryLSN, depth)
      && freshestRec.value.MessageSeqAfterCrop(boundaryLSN, depth) == msgs
    }

    function AppendRecord(msgs: MsgHistory) : (out: TruncatedJournal)
      requires WF()
      requires msgs.WF()
    {
      this.(freshestRec := Some(JournalRecord(msgs, freshestRec)))
    }

    function CropHeadRecords(depth: nat) : TruncatedJournal
    {
      TruncatedJournal(boundaryLSN, OptRecCropHeadRecords(freshestRec, boundaryLSN, depth))
    }

    predicate FreezeForCommit(frozenJournal: TruncatedJournal, depth: nat)
      requires WF()
    {
      && frozenJournal.WF()
      && OptRecCanCropHeadRecords(freshestRec, boundaryLSN, depth)
      && CropHeadRecords(depth).I().CanDiscardTo(frozenJournal.boundaryLSN) // TODO(tony) remove I() here; replace with local condition
      // probably want: CropHeadRecords(depth).seqStart <= frozenJournal.boundaryLSN
      && frozenJournal == CropHeadRecords(depth).DiscardOldDefn(frozenJournal.boundaryLSN)
    }
  } // datatype TruncatedJournal

  // TruncatedJournal is the datatype "refinement" of MsgHistory; here we refine the Mkfs function.
  function Mkfs() : (out:TruncatedJournal)
    ensures out.WF()
    ensures out.I().IsEmpty()
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

    function I() : MsgHistory
      requires WF()
    {
      truncatedJournal.I().Concat(unmarshalledTail)
    }

    function SeqStart() : LSN
      requires WF()
      ensures SeqStart() == I().seqStart
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

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
  {
    && v.WF()
    && lbl.FreezeForCommitLabel?
    && v.truncatedJournal.FreezeForCommit(lbl.frozenJournal, keepReceiptLines)
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
      ReadForRecoveryStep(receiptIndex: nat)
    | FreezeForCommitStep(keepReceiptLines: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(receiptIndex) => ReadForRecovery(v, v', lbl, receiptIndex)
      case FreezeForCommitStep(keepReceiptLines) => FreezeForCommit(v, v', lbl, keepReceiptLines)
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
