// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import PagedJournal

  type Address(!new, ==)
  type Pointer = Option<Address>

  // TODO(robj): where does this go?
  datatype DiskView = DiskView(entries: map<Address, JournalRecord>) {
  }

  datatype JournalRecord = JournalRecord(messageSeq: MsgHistory, priorRec: Pointer)
  {
    predicate WF()
    {
      messageSeq.WF()
    }
  }
    
  datatype TruncatedJournal = TruncatedJournal(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Pointer,
    cacheView: DiskView)

  function Mkfs() : (out:TruncatedJournal)
  {
    // TODO(jonh): Just making up DiskViews seems like trouble for lower in the stack.
    TruncatedJournal(0, None, DiskView(map[]))
  }

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
  }

  predicate Put(v: Variables, v': Variables, msgs: MsgHistory)
  {
    && v.WF()
    && v'.WF()
    && msgs.WF()
    && (v.SeqEnd().None? || msgs.EmptyHistory? || msgs.seqStart == v.SeqEnd().value)  // CanFollow, but without interpreting this.
    && v' == v.(unmarshalledTail := v.unmarshalledTail.Concat(msgs))
  }

  predicate DiscardOld(v: Variables, v': Variables, lsn: LSN)
  {
    && v.WF()
    && v'.WF()
    && (if v.Empty() then true else v.SeqStart() <= lsn <= v.SeqEnd().value)
    && (if v.unmarshalledTail.MsgHistory? && v.unmarshalledTail.seqStart <= lsn
        then v' == Variables(Mkfs(), v.unmarshalledTail.DiscardOld(lsn))
        else v' == v.(truncatedJournal := v.truncatedJournal.DiscardOld(lsn))
       )
  }

  predicate JournalMarshal(v: Variables, v': Variables, cut: LSN)
  {
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

  predicate Init(v: Variables)
  {
    && v == Variables(Mkfs(), EmptyHistory)
  }

  datatype Step =
      ReadForRecoveryStep(receiptIndex: nat)
    | FreezeForCommitStep(keepReceiptLines: nat)
    | ObserveFreshJournalLabel()
    | PutStep(msgs: MsgHistory)
    | DiscardOldStep(lsn: LSN)
    | InternalJournalMarshalStep(cut: LSN)

  predicate NextStep(v: Variables, v': Variables, step: Step)
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
}
