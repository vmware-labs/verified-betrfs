// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"

// A Journal that keeps an in-memory index that maps each in-use LSN to the Address that stores it.
// The impl will keep such an index so that Discard can return freed Addresses without having to
// fault in the freed section of the journal to learn the chain of addresses involved.
module ReprJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import LinkedJournal
  import GenericDisk
  import Mathematics

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type DiskView = LinkedJournal.DiskView
  type TruncatedJournal = LinkedJournal.TruncatedJournal

  datatype GCTruncatedJournal = GCTruncatedJournal(
    reserved: set<Address>,
    stranded: set<Address>,
    journal: TruncatedJournal
  ) {
    predicate WF() {
      journal.Decodable()
    }
  }

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: GCTruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
    // Internal-x labels refine to no-ops at the abstract spec
    | InternalJournalGCLabel(allocations: set<Address>, freed: set<Address>)
    | InternalLabel()  // Local No-op label
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.journal.Decodable())
    }

    function I(): LinkedJournal.TransitionLabel {
      match this {
        case ReadForRecoveryLabel(messages) => LinkedJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => LinkedJournal.FreezeForCommitLabel(frozenJournal.journal)
        case QueryEndLsnLabel(endLsn) => LinkedJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => LinkedJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd) => LinkedJournal.DiscardOldLabel(startLsn, requireEnd)
        case InternalJournalGCLabel(_, _) => LinkedJournal.InternalLabel()
        case InternalLabel() => LinkedJournal.InternalLabel()
      }
    }
  }

  datatype Variables = Variables(
    journal: LinkedJournal.Variables,
    reprIndex: map<LSN, Address>,   // maps in-repr lsn's to their page addr
    reserved: set<Address>,         // reserved addresses given by the global allocator
    stranded: set<Address>          // set of stranded addresses
  )
  {
    predicate WF() {
      && journal.WF()
      && journal.truncatedJournal.SeqStart() <= journal.truncatedJournal.SeqEnd()
    }
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && LinkedJournal.ReadForRecovery(v.journal, v'.journal, lbl.I(), depth)
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && LinkedJournal.FreezeForCommit(v.journal, v'.journal, lbl.I(), depth)
    // we only remember a subset of our reserved and stranded set as we freeze
    && lbl.frozenJournal.reserved <= v.reserved
    && lbl.frozenJournal.stranded <= v.stranded 
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate ObserveFreshJournal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedJournal.ObserveFreshJournal(v.journal, v'.journal, lbl.I())
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedJournal.Put(v.journal, v'.journal, lbl.I())
    && v' == v.(
      journal := v'.journal
    )
  }

  function DiscardOldAndGarbageCollect(tj: TruncatedJournal, newBdy: LSN, keep: set<Address>) : TruncatedJournal
    requires tj.WF()
    requires tj.diskView.boundaryLSN <= newBdy
  {
    var newEntries := MapRestrict(tj.diskView.entries, keep); 
    var newDiskView := LinkedJournal.DiskView(newBdy, newEntries);
    if tj.SeqEnd() == newBdy
    then LinkedJournal.TruncatedJournal(None, newDiskView)
    else LinkedJournal.TruncatedJournal(tj.freshestRec, newDiskView)
  }

  // Update reprIndex with by discarding lsn's strictly smaller than bdy
  function {:opaque} reprIndexDiscardUpTo(reprIndex: map<LSN, Address>, bdy: LSN) : (out: map<LSN, Address>)
    ensures IsSubMap(out, reprIndex)
    ensures forall k | k in out :: bdy <= k
    ensures forall k | k in reprIndex &&  bdy <= k :: k in out
  {
    map x: LSN | x in reprIndex && bdy <= x :: reprIndex[x]
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel) 
  {
    // Enabling conditions
    && lbl.DiscardOldLabel?
    && v.journal.WF()
    && v.journal.truncatedJournal.diskView.Acyclic()
    && v.journal.SeqStart() <= lbl.startLsn <= v.journal.SeqEnd()
    && lbl.requireEnd == v.journal.SeqEnd()
    && v.journal.truncatedJournal.CanDiscardTo(lbl.startLsn)
    // Define v'
    && var reprIndex' := reprIndexDiscardUpTo(v.reprIndex, lbl.startLsn);
    && var keepAddrs := reprIndex'.Values;
    && v' == v.(
      journal := LinkedJournal.Variables(
        DiscardOldAndGarbageCollect(v.journal.truncatedJournal, lbl.startLsn, keepAddrs),
        if v.journal.unmarshalledTail.seqStart <= lbl.startLsn
        then v.journal.unmarshalledTail.DiscardOld(lbl.startLsn)
        else v.journal.unmarshalledTail
      ),
      reprIndex := reprIndex',
      stranded := v.stranded + (v.reprIndex.Values - keepAddrs)  // "return" the set of freed addrs
  )
  }

  // Update reprIndex with additional lsn's from a new record
  function reprIndexAppendRecord(reprIndex: map<LSN, Address>, msgs: MsgHistory, addr: Address) : (out: map<LSN, Address>)
    requires msgs.WF()
    requires msgs.seqStart < msgs.seqEnd
    ensures (forall x | msgs.seqStart <= x < msgs.seqEnd :: x !in reprIndex) 
            ==> out.Values == reprIndex.Values + {addr}
  {
    // msgs is complete map from seqStart to seqEnd 
    var update :=  map x: LSN | msgs.seqStart <= x < msgs.seqEnd :: addr;
    assert msgs.seqStart in update;  // witness
    MapUnion(reprIndex, update)
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN, addr: Address)
  {
    // Enabling conditions
    && lbl.InternalLabel?
    && v.WF()
    && 0 < |v.reserved|
    && addr in v.reserved
    // State transition
    && LinkedJournal.InternalJournalMarshal(v.journal, v'.journal, lbl.I(), cut, addr)
    && v' == v.(
      journal := v'.journal,
      reprIndex := reprIndexAppendRecord(v.reprIndex, v.journal.unmarshalledTail.DiscardRecent(cut), addr),
      reserved := v.reserved - {addr}
    )
  }

  predicate InternalJournalReserve(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && lbl.InternalJournalGCLabel?
    && v.WF()
    && 0 < |lbl.allocations|
    && lbl.freed == {}
    // State transition
    && v' == v.(
      reserved := v.reserved + lbl.allocations
    )
  }

  predicate InternalJournalFree(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    // Enabling conditions
    && lbl.InternalJournalGCLabel?
    && v.WF()
    && lbl.allocations == {}
    && lbl.freed <= v.stranded
    && 0 < |lbl.freed|
    // State transition
    && v' == v.(
      stranded := v.stranded - lbl.freed
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }

  function BuildReprIndexDefn(dv: DiskView, root: Pointer) : map<LSN, Address> 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    decreases dv.TheRankOf(root)
  {
    if root.None? then map[]
    else 
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) <= x < currMsgs.seqEnd :: root.value;
      MapUnion(BuildReprIndexDefn(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), update)
  }

  function BuildReprIndex(tj: TruncatedJournal) : map<LSN, Address> 
    requires tj.WF()
    requires tj.diskView.Decodable(tj.freshestRec)
    requires tj.diskView.Acyclic()
  {
   BuildReprIndexDefn(tj.diskView, tj.freshestRec)
  }

  predicate Init(v: Variables, gcJournal: GCTruncatedJournal)
  {
    var tj := gcJournal.journal;
    && tj.Decodable()  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && tj.DiskIsTightWrtRepresentation()
    && v == 
        Variables(
          LinkedJournal.Variables(tj, EmptyHistoryAt(tj.BuildTight().SeqEnd())),
          BuildReprIndex(tj),
          gcJournal.reserved,
          gcJournal.stranded
      )
  }

  datatype Step =
      ReadForRecoveryStep(depth: nat)
    | FreezeForCommitStep(depth: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN, addr: Address)
    | InternalJournalReserveStep()  // reserve more addresses from the global allocator
    | InternalJournalFreeStep()       // free some stranded addresses
    | InternalNoOpStep()

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case ReadForRecoveryStep(depth) => ReadForRecovery(v, v', lbl, depth)
      case FreezeForCommitStep(depth) => FreezeForCommit(v, v', lbl, depth)
      case ObserveFreshJournalStep() => ObserveFreshJournal(v, v', lbl)
      case PutStep() => Put(v, v', lbl)
      case DiscardOldStep() => DiscardOld(v, v', lbl)
      case InternalJournalMarshalStep(cut, addr) => InternalJournalMarshal(v, v', lbl, cut, addr)
      case InternalJournalReserveStep() => InternalJournalReserve(v, v', lbl)
      case InternalJournalFreeStep() => InternalJournalFree(v, v', lbl)
      case InternalNoOpStep() =>  InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
