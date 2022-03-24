// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened JournalLabels
  import PagedJournal

  type Address(!new, ==)
  type Pointer = Option<Address>

  type Ranking = map<Address, nat>

  // TODO(robj): where does this go?
  // The DiskView in this module is a tightly-populated mapping:
  // every record the journal needs is present in the mapping,
  // and every address is "important" to the journal.
  datatype DiskView = DiskView(entries: map<Address, JournalRecord>) {
    predicate EntriesWF()
    {
      (forall addr | addr in entries :: entries[addr].WF())
    }

    predicate NondanglingPointer(ptr: Pointer)
    {
      ptr.Some? ==> ptr.value in entries
    }

    predicate NondanglingPointers()
    {
      (forall addr | addr in entries :: NondanglingPointer(entries[addr].priorRec))
    }

    predicate WF()
    {
      && EntriesWF()
      && NondanglingPointers()
    }

    predicate PointersRespectRank(ranking: Ranking)
      requires WF()
    {
      && ranking.Keys == entries.Keys
      && (forall address | address in entries && entries[address].priorRec.Some? ::
          && ranking[entries[address].priorRec.value] < ranking[address]
         )
    }

    predicate Acyclic()
      requires WF()
    {
      && exists ranking :: PointersRespectRank(ranking)
    }

    function TheRanking() : Ranking
      requires WF()
      requires Acyclic()
    {
      // Make CHOOSE deterministic as Leslie and Hilbert intended
      var ranking :| PointersRespectRank(ranking); ranking
    }

    function RankedIPtr(ptr: Pointer, ranking: Ranking) : Option<PagedJournal.JournalRecord>
      requires WF()
      requires NondanglingPointer(ptr)
      requires PointersRespectRank(ranking)
      decreases if ptr.Some? then ranking[ptr.value] else -1 // I can't believe this works, Rustan!
    {
      if ptr.None?
      then None
      else
        var jr := entries[ptr.value];
        Some(PagedJournal.JournalRecord(jr.messageSeq, RankedIPtr(jr.priorRec, ranking)))
    }

    function IPtr(ptr: Pointer) : Option<PagedJournal.JournalRecord>
      requires WF()
      requires Acyclic()
      requires NondanglingPointer(ptr)
    {
      RankedIPtr(ptr, TheRanking())
    }
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
    diskView: DiskView)
  {
    predicate WF() {
      && diskView.WF()
      && diskView.NondanglingPointer(freshestRec)
    }

    function SeqStart() : LSN
    {
      boundaryLSN
    }

    function SeqEnd() : LSN
      requires WF()
    {
      if freshestRec.None?  // normal case with empty TJ
      then boundaryLSN
      else diskView.entries[freshestRec.value].messageSeq.seqEnd
    }

    // TODO(jonh): this function doesn't yet correctly maintain the "DiskView
    // tightness" property; it leaks pages. We'll probably need a receipt to locate
    // the subset of addresses we want to keep.
    function DiscardOld(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
    {
      if freshestRec.None? || lsn == diskView.entries[freshestRec.value].messageSeq.seqEnd
      then TruncatedJournal(lsn, None, diskView)
      else TruncatedJournal(lsn, freshestRec, diskView)
    }

    function AppendRecord(addr: Address, msgs: MsgHistory) : (out: TruncatedJournal)
      requires addr !in diskView.entries
    {
      this.(
        diskView := diskView.(entries := diskView.entries[addr := JournalRecord(msgs, freshestRec)]),
        freshestRec := Some(addr))
    }

    function I() : PagedJournal.TruncatedJournal
      requires WF()
      requires diskView.Acyclic()
    {
      PagedJournal.TruncatedJournal(boundaryLSN, diskView.IPtr(freshestRec))
    }

    predicate Decodable()
    {
      && WF()
      && diskView.Acyclic()
      && I().WF()
    }
  }

  function Mkfs() : (out:TruncatedJournal)
  {
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

    function SeqStart() : LSN
    {
      truncatedJournal.SeqStart()
    }

    function SeqEnd() : LSN
      requires WF()
    {
      unmarshalledTail.seqEnd
    }

    predicate UnusedAddr(addr: Address)
    {
      // TODO reaching into truncatedJournal to find the diskView feels skeezy
      addr !in truncatedJournal.diskView.entries
    }
  }

  // NB We need both rank and receipts to concisely write this predicate, which is why they
  // get defined here in the state machine instead of deferred to the refinement module.
  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, receiptIndex: nat)
  {
    && lbl.ReadForRecoveryLabel?
    && lbl.messages.WF()
    && v.WF()
    && v.truncatedJournal.Decodable()
    && var pagedTJ := v.truncatedJournal.I();
    && pagedTJ.IncludesSubseqAt(lbl.messages, receiptIndex)
    && v' == v
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
  {
    && v.WF()
    && v.truncatedJournal.Decodable()
    && var pagedTJ := v.truncatedJournal.I();
    && pagedTJ.FreezeForCommit(lbl, keepReceiptLines)
    && v' == v
  }

  // rename to match lbl QueryEndLsnLabel
  predicate ObserveFreshJournal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && v.WF()
    && lbl.endLsn == v.SeqEnd()
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.messages.WF()
    && v.WF()
    && lbl.messages.seqStart == v.SeqEnd()
    && v' == v.(unmarshalledTail := v.unmarshalledTail.Concat(lbl.messages))
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // diskView not tightened here
    && lbl.DiscardOldLabel?
    && v.WF()
    && lbl.requireEnd == v.SeqEnd()
    && v.SeqStart() <= lbl.startLsn <= v.SeqEnd()
    && (if v.unmarshalledTail.seqStart <= lbl.startLsn
        then v' == Variables(TruncatedJournal(lbl.startLsn, None, DiskView(map[])), v.unmarshalledTail.DiscardOld(lbl.startLsn))
        else v' == v.(truncatedJournal := v.truncatedJournal.DiscardOld(lbl.startLsn))
       )
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN, addr: Address)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v.unmarshalledTail.seqStart < cut // Can't marshall nothing.
    && v.unmarshalledTail.CanDiscardTo(cut)
    && v.UnusedAddr(addr)
    && var marshalledMsgs := v.unmarshalledTail.DiscardRecent(cut);
    && v' == Variables(
      v.truncatedJournal.AppendRecord(addr, marshalledMsgs),
      v.unmarshalledTail.DiscardOld(cut))
  }

  predicate Init(v: Variables, tj: TruncatedJournal)
  {
    && tj.Decodable() // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && v == Variables(tj, EmptyHistoryAt(tj.SeqEnd()))
  }

  datatype Step =
      ReadForRecoveryStep(receiptIndex: nat)
    | FreezeForCommitStep(keepReceiptLines: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN, addr: Address)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(receiptIndex) => ReadForRecovery(v, v', lbl, receiptIndex)
      case FreezeForCommitStep(keepReceiptLines) => FreezeForCommit(v, v', lbl, keepReceiptLines)
      case ObserveFreshJournalStep() => ObserveFreshJournal(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case DiscardOldStep() => DiscardOld(v, v', lbl)
      case InternalJournalMarshalStep(cut, addr) => InternalJournalMarshal(v, v', lbl, cut, addr)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
