// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "PagedJournal.i.dfy"

module GenericDisk {
  import opened Options

  type Block(!new, ==)
  function Parse<T>(block: Block) : T
  function Marshal<T>(t: T) : Block
  lemma ParseAxiom<T>(t: T)
    ensures Parse(Marshal(t)) == t

  type Address(!new, ==)
  type Pointer = Option<Address>

  type Disk = map<Address, Block> // TODO(jonh): rename DiskView, since it's partial.
}

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened JournalLabels
  import opened Maps
  import GenericDisk
  import PagedJournal

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  type Ranking = map<Address, nat>

  datatype JournalRecord = JournalRecord(messageSeq: MsgHistory, priorRecXXX: Pointer)
  {
    predicate WF()
    {
      messageSeq.WF()
    }

    // The DiskView always evaluates the priorRec pointer through the lens of
    // the boundaryLSN, dropping pointers that can't possibly provide any
    // useful LSNs.
    function CroppedPrior(boundaryLSN: LSN) : Pointer
    {
      if boundaryLSN < messageSeq.seqStart then priorRecXXX else None
    }
  }

  // The DiskView in this module is a tightly-populated mapping:
  // every record the journal needs is present in the mapping,
  // and every address is "important" to the journal.
  // The boundaryLSN enables us to ignore "cropped" pointers.
  datatype DiskView = DiskView(boundaryLSN: LSN, entries: map<Address, JournalRecord>) {
    predicate EntriesWF()
    {
      (forall addr | addr in entries :: entries[addr].WF())
    }

    predicate IsNondanglingPointer(ptr: Pointer)
    {
      ptr.Some? ==> ptr.value in entries
    }

    predicate NondanglingPointers()
    {
      (forall addr | addr in entries :: IsNondanglingPointer(entries[addr].CroppedPrior(boundaryLSN)))
    }

    predicate WF()
    {
      && EntriesWF()
      && NondanglingPointers()
    }

    predicate PointersRespectRank(ranking: Ranking)
      requires WF()
    {
      && entries.Keys <= ranking.Keys
      && (forall address | address in entries && entries[address].CroppedPrior(boundaryLSN).Some? ::
          && ranking[entries[address].CroppedPrior(boundaryLSN).value] < ranking[address]
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
      requires IsNondanglingPointer(ptr)
      requires PointersRespectRank(ranking)
      decreases if ptr.Some? then ranking[ptr.value] else -1 // I can't believe this works, Rustan!
    {
      if ptr.None?
      then None
      else
        var jr := entries[ptr.value];
        Some(PagedJournal.JournalRecord(jr.messageSeq, RankedIPtr(jr.CroppedPrior(boundaryLSN), ranking)))
    }

    function IPtr(ptr: Pointer) : Option<PagedJournal.JournalRecord>
      requires WF()
      requires Acyclic()
      requires IsNondanglingPointer(ptr)
    {
      RankedIPtr(ptr, TheRanking())
    }

    function DiscardOld(newBoundary: LSN) : (out: DiskView)
      requires WF()
      requires boundaryLSN <= newBoundary
      ensures out.WF()
    {
      DiskView(newBoundary, entries)
    }

    predicate IsSubDisk(bigger: DiskView)
    {
      && boundaryLSN == bigger.boundaryLSN
      && IsSubMap(entries, bigger.entries)
    }

    predicate Tight()
      requires WF()
    {
      forall other:DiskView |
        && other.WF()
        && other.IsSubDisk(this)
        :: other == this
    }
  }

  datatype TruncatedJournal = TruncatedJournal(
    freshestRec: Pointer,
    diskView: DiskView)
  {
    predicate WF() {
      && diskView.WF()
      && diskView.IsNondanglingPointer(freshestRec)
    }

    function SeqStart() : LSN
    {
      diskView.boundaryLSN
    }

    function SeqEnd() : LSN
      requires WF()
    {
      if freshestRec.None?  // normal case with empty TJ
      then diskView.boundaryLSN
      else diskView.entries[freshestRec.value].messageSeq.seqEnd
    }

    function DiscardOld(lsn: LSN) : (out:TruncatedJournal)
      requires WF()
      requires diskView.boundaryLSN <= lsn
    {
      if SeqEnd() <= lsn
      then TruncatedJournal(None, diskView.DiscardOld(lsn))
      else TruncatedJournal(freshestRec, diskView.DiscardOld(lsn))
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
      PagedJournal.TruncatedJournal(diskView.boundaryLSN, diskView.IPtr(freshestRec))
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
    TruncatedJournal(None, DiskView(0, map[]))
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
    // && lbl.FreezeForCommitLabel? enforced by pagedTJ.FreezeForCommit.
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

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel, tightDiskView: DiskView)
  {
    // diskView not tightened here
    && lbl.DiscardOldLabel?
    && v.WF()
    && tightDiskView.WF() // When you GC the disk, you must preserve the reachable pointers.
    && tightDiskView.Tight()  // We don't really need to require tightness at this layer, but I feel like it.
    && v.SeqStart() <= lbl.startLsn <= v.SeqEnd()
    && var croppedTJ := v.truncatedJournal.DiscardOld(lbl.startLsn);
    && tightDiskView.IsSubDisk(croppedTJ.diskView)
    && tightDiskView.IsNondanglingPointer(croppedTJ.freshestRec)  // Can't crop to nothing!
    && lbl.requireEnd == v.SeqEnd()
    // && var tightTJ := croppedTJ; TODO(jonh): deleteme
    && var tightTJ := TruncatedJournal(croppedTJ.freshestRec, tightDiskView);
    && v' == Variables(tightTJ,
        if v.unmarshalledTail.seqStart <= lbl.startLsn
        then v.unmarshalledTail.DiscardOld(lbl.startLsn)
        else v.unmarshalledTail
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
    | DiscardOldStep(tightDiskView: DiskView)
    | InternalJournalMarshalStep(cut: LSN, addr: Address)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(receiptIndex) => ReadForRecovery(v, v', lbl, receiptIndex)
      case FreezeForCommitStep(keepReceiptLines) => FreezeForCommit(v, v', lbl, keepReceiptLines)
      case ObserveFreshJournalStep() => ObserveFreshJournal(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case DiscardOldStep(tightDiskView) => DiscardOld(v, v', lbl, tightDiskView)
      case InternalJournalMarshalStep(cut, addr) => InternalJournalMarshal(v, v', lbl, cut, addr)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
