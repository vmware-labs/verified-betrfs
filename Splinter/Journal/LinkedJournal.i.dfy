// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournal.i.dfy"
include "GenericDisk.i.dfy"

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import GenericDisk
  import PagedJournal

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: TruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
    | InternalLabel()
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.Decodable())
    }
  }

  type Ranking = map<Address, nat>

  datatype JournalRecord = JournalRecord(messageSeq: MsgHistory, _priorRec: Pointer)
    // Never access priorRec directly; only reference it through CroppedPrior.
    // A Pointer only has meaning if its referent isn't rendered irrelevant by
    // some boundaryLSN.
  {
    predicate WF()
    {
      messageSeq.WF()
    }

    predicate HasLink(boundaryLSN: LSN) 
    {
      boundaryLSN < messageSeq.seqStart ==> CroppedPrior(boundaryLSN).Some?
    }

    // The DiskView always evaluates the priorRec pointer through the lens of
    // the boundaryLSN, dropping pointers that can't possibly provide any
    // useful LSNs.
    function CroppedPrior(boundaryLSN: LSN) : Pointer
    {
      if boundaryLSN < messageSeq.seqStart then _priorRec else None
    }
  }

  // The DiskView in this module is a tightly-populated mapping:
  // every record the journal needs is present in the mapping,
  // and every address is "important" to the journal.
  // The boundaryLSN enables us to ignore "cropped" pointers.
  // The values in this DiskView are typed, unlike GenericDisk.DiskView.
  //
  // TODO(jonh): Jialin suggests JournalStore to avoid the way "disk" brings in too
  // many other model assumptions.
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

    predicate ThisBlockCanConcat(addr: Address) 
      requires EntriesWF()
      requires NondanglingPointers()
      requires addr in entries
    {
      var head := entries[addr];
      var nextPtr := head.CroppedPrior(boundaryLSN);
      nextPtr.Some? ==> entries[nextPtr.value].messageSeq.CanConcat(head.messageSeq)
    }

    predicate BlocksCanConcat() 
      requires EntriesWF()
      requires NondanglingPointers()
    {
      forall addr | addr in entries :: ThisBlockCanConcat(addr)
    }

    predicate BlocksEachHaveLink()
    {
      forall addr | addr in entries :: entries[addr].HasLink(boundaryLSN)
    }

    predicate BlockInBounds(ptr: Pointer) 
    {
      && IsNondanglingPointer(ptr)
      && (ptr.Some? ==> boundaryLSN < entries[ptr.value].messageSeq.seqEnd)
    }

    predicate WF()
    {
      && EntriesWF()
      && NondanglingPointers()
      && BlocksCanConcat()
      && BlocksEachHaveLink()
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

    predicate Decodable(ptr: Pointer)
    {
      && WF()
      && IsNondanglingPointer(ptr)
    }

    function TheRankOf(ptr: Pointer) : int
      requires WF()
      requires IsNondanglingPointer(ptr)
    {
      if ptr.Some? && Acyclic() then TheRanking()[ptr.value] else -1
      // Rustan: I can't believe this works! How are you figuring out that we can pass 0 into
      // negatives, but we stop there!?
    }

    function DiscardOld(newBoundary: LSN) : (out: DiskView)
      requires boundaryLSN <= newBoundary
    {
      DiskView(newBoundary, entries)
    }

    predicate IsSubDisk(bigger: DiskView)
    {
      && boundaryLSN == bigger.boundaryLSN
      && IsSubMap(entries, bigger.entries)
    }

    function BuildTight(root: Pointer) : (out: DiskView)
      requires Decodable(root)
      decreases TheRankOf(root)
    {
      if !Acyclic() then DiskView(0, map[]) // Silly
      else if root.None? then DiskView(boundaryLSN, map[])
      else
        var addr := root.value;
        DiskView(boundaryLSN, BuildTight(entries[addr].CroppedPrior(boundaryLSN)).entries[addr := entries[addr]])
    }

    function PointerAfterCrop(root: Pointer, depth: nat) : (out: Pointer)
      requires Decodable(root)
      requires BlockInBounds(root)
      ensures IsNondanglingPointer(out)
      ensures BlockInBounds(out)
      decreases depth
    {
      if depth==0 || root.None?
      then root
      else
        PointerAfterCrop(entries[root.value].CroppedPrior(boundaryLSN), depth-1)
    }
  }

  datatype TruncatedJournal = TruncatedJournal(
    freshestRec: Pointer, // root address of journal
    diskView: DiskView)
  {

    predicate WF() {
      && diskView.WF()
      && diskView.IsNondanglingPointer(freshestRec)
      && diskView.BlockInBounds(freshestRec)
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

    predicate Decodable() // becomes invariant
    {
      && WF()
      && diskView.Acyclic()
    }

    function BuildTight() : (out: TruncatedJournal)
      requires WF()
    {
      TruncatedJournal(freshestRec, diskView.BuildTight(freshestRec))
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
      && truncatedJournal.SeqEnd() == unmarshalledTail.seqStart // TODO(jonh): can probably delete this, since it's proven by interp
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
  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && lbl.ReadForRecoveryLabel?
    && lbl.messages.WF()
    && v.WF()
    && v.truncatedJournal.Decodable()
    && var ptr := v.truncatedJournal.diskView.PointerAfterCrop(v.truncatedJournal.freshestRec, depth);
    && ptr.Some?
    && v.truncatedJournal.diskView.entries[ptr.value].messageSeq.IncludesSubseq(lbl.messages)
    && v' == v
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && lbl.WF()
    && lbl.FreezeForCommitLabel?
    && v.WF()
    && v.truncatedJournal.Decodable() // Shown by invariant, not runtime-checked
    && var ptr := v.truncatedJournal.diskView.PointerAfterCrop(v.truncatedJournal.freshestRec, depth);
    && var croppedTj := TruncatedJournal(ptr, v.truncatedJournal.diskView);
    && var newBdy := lbl.frozenJournal.SeqStart();
    && v.truncatedJournal.diskView.boundaryLSN <= newBdy
    && lbl.frozenJournal == croppedTj.DiscardOld(newBdy).BuildTight()
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
    && v.SeqStart() <= lbl.startLsn <= v.SeqEnd()
    && lbl.requireEnd == v.SeqEnd()
    && v' == Variables(v.truncatedJournal.DiscardOld(lbl.startLsn).BuildTight(),
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
      ReadForRecoveryStep(depth: nat)
    | FreezeForCommitStep(depth: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN, addr: Address)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(depth) => ReadForRecovery(v, v', lbl, depth)
      case FreezeForCommitStep(depth) => FreezeForCommit(v, v', lbl, depth)
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
