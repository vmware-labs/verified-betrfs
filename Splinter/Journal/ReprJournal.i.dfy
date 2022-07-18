// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"
include "GenericDisk.i.dfy"

module ReprJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import GenericDisk
  import LinkedJournal
  import Mathematics

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  type DiskView = LinkedJournal.DiskView
  type TruncatedJournal = LinkedJournal.TruncatedJournal
  type TransitionLabel = LinkedJournal.TransitionLabel
  type Step = LinkedJournal.Step

  // The Representation set for the journal data structure
  // function Repr(tj: LinkedJournal.TruncatedJournal, reprIndex: map<LSN, Address>) : set<Address>
  //   requires tj.WF()
  //   requires forall x | tj.SeqStart() <= x < tj.SeqEnd() :: x in reprIndex
  // {
  //   // tj.SeqStart() == tj.SeqEnd() means the journal is empty
  //   set x: LSN | tj.SeqStart() <= x < tj.SeqEnd() :: reprIndex[x]
  // }

  predicate IndexKeysMapToValidEntries(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    forall lsn | lsn in reprIndex ::
      && reprIndex[lsn] in tj.diskView.entries
      && tj.diskView.entries[reprIndex[lsn]].ContainsLSN(lsn)
  }

  predicate IndexDomainWF(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
  {
    // reprIndex's domain is exactly the set of LSN between journal.SeqStart() and journal.SeqEnd()
    && (forall lsn :: lsn in reprIndex <==> tj.SeqStart() <= lsn < tj.SeqEnd())
  }

  predicate IndexRangeWF(reprIndex: map<LSN, Address>, tj: TruncatedJournal)
    requires tj.WF()
    requires IndexDomainWF(reprIndex, tj)
    requires IndexKeysMapToValidEntries(reprIndex, tj)
  {
    forall addr | addr in reprIndex.Values ::
      && var msgs := tj.diskView.entries[addr].messageSeq;
      && var boundaryLSN := tj.diskView.boundaryLSN;
      && (forall lsn | Mathematics.max(boundaryLSN, msgs.seqStart) <= lsn < msgs.seqEnd :: 
            && lsn in reprIndex
            && reprIndex[lsn] == addr
        )
  }

  datatype Variables = Variables(
    journal: LinkedJournal.Variables,
    reprIndex: map<LSN, Address>  // maps in-repr lsn's to their page addr
  )
  {
    predicate WF() {
      && journal.WF()
      && IndexDomainWF(reprIndex, journal.truncatedJournal)
      && IndexKeysMapToValidEntries(reprIndex, journal.truncatedJournal)
      && IndexRangeWF(reprIndex, journal.truncatedJournal)
      && journal.truncatedJournal.SeqStart() <= journal.truncatedJournal.SeqEnd()
    }
  }

  predicate ReadForRecovery(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && LinkedJournal.ReadForRecovery(v.journal, v'.journal, lbl, depth)
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, depth: nat)
  {
    && LinkedJournal.FreezeForCommit(v.journal, v'.journal, lbl, depth)
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate ObserveFreshJournal(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedJournal.ObserveFreshJournal(v.journal, v'.journal, lbl)
    && v' == v.(
      journal := v'.journal
    )
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && LinkedJournal.Put(v.journal, v'.journal, lbl)
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
      reprIndex := reprIndex'
  )
  }

  // Update reprIndex with additional lsn's from a new record
  function reprIndexAppendRecord(reprIndex: map<LSN, Address>, msgs: MsgHistory, addr: Address) : (out: map<LSN, Address>)
    requires msgs.WF()
    requires msgs.seqStart < msgs.seqEnd
    requires forall x | msgs.seqStart <= x < msgs.seqEnd :: x !in reprIndex;
    ensures out.Values == reprIndex.Values + {addr}
  {
    // msgs is complete map from seqStart to seqEnd 
    var update :=  map x: LSN | msgs.seqStart <= x < msgs.seqEnd :: addr;
    assert msgs.seqStart in update;  // witness
    MapUnion(reprIndex, update)
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && v.WF()
    && LinkedJournal.InternalJournalMarshal(v.journal, v'.journal, lbl, cut)
    && lbl.addr !in v.reprIndex.Values  // Fresh!
    && v' == v.(
      journal := v'.journal,
      reprIndex := reprIndexAppendRecord(v.reprIndex, v.journal.unmarshalledTail.DiscardRecent(cut), lbl.addr)
    )
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

  predicate Init(v: Variables, tj: TruncatedJournal)
  {
    && tj.Decodable()  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && tj.DiskIsTightWrtRepresentation()
    && v == 
        Variables(
          LinkedJournal.Variables(tj, EmptyHistoryAt(tj.BuildTight().SeqEnd())),
          BuildReprIndex(tj)
      )
  }

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
