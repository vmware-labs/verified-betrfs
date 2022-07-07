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

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address

  type DiskView = LinkedJournal.DiskView
  type TruncatedJournal = LinkedJournal.TruncatedJournal
  type TransitionLabel = LinkedJournal.TransitionLabel
  type Step = LinkedJournal.Step

  // The Representation set for the journal data structure
  function Repr(tj: LinkedJournal.TruncatedJournal, reprIndex: map<LSN, Address>) : set<Address>
    requires tj.WF()
    requires forall x | tj.SeqStart() <= x < tj.SeqEnd() :: x in reprIndex
  {
    // tj.SeqStart() == tj.SeqEnd() means the journal is empty
    set x: LSN | tj.SeqStart() <= x < tj.SeqEnd() :: reprIndex[x]
  }

  datatype Variables = Variables(
    journal: LinkedJournal.Variables,
    reprIndex: map<LSN, Address>  // maps in-repr lsn's to their page addr
  )
  {
    predicate IndexDomainWF() 
      requires journal.WF()
    {
      (forall lsn :: journal.truncatedJournal.SeqStart() <= lsn < journal.truncatedJournal.SeqEnd() <==> lsn in reprIndex)
    }

    predicate IndexRangeWF()
      requires journal.WF()
    {
      forall lsn | lsn in reprIndex ::
        && reprIndex[lsn] in journal.truncatedJournal.diskView.entries
        && journal.truncatedJournal.diskView.entries[reprIndex[lsn]].ContainsLSN(lsn)
    }

    predicate WF() {
      && journal.WF()
      && IndexDomainWF()
      && IndexRangeWF()
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

  // Update reprIndex with by discarding lsn's strictly smaller than bdy
  function reprIndexDiscard(reprIndex: map<LSN, Address>, bdy: LSN) : map<LSN, Address>
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
    && v' == v.(
      journal := v'.journal,
      reprIndex := reprIndexDiscard(v.reprIndex, lbl.startLsn)
  )
  }

  // Update reprIndex with additional lsn's from a new record
  function reprIndexAppendRecord(reprIndex: map<LSN, Address>, msgs: MsgHistory, addr: Address) : map<LSN, Address>
  {
    var update :=  map x: LSN | msgs.seqStart <= x < msgs.seqEnd :: addr;
    MapUnion(reprIndex, update)
  }

  predicate InternalJournalMarshal(v: Variables, v': Variables, lbl: TransitionLabel, cut: LSN)
  {
    && LinkedJournal.InternalJournalMarshal(v.journal, v'.journal, lbl, cut)
    && lbl.addr !in v.reprIndex.Values  // Fresh!
    && v' == v.(
      journal := v'.journal,
      reprIndex := reprIndexAppendRecord(v.reprIndex, v.journal.unmarshalledTail.DiscardRecent(cut), lbl.addr)
    )
  }

  function BuildReprIndex(dv: DiskView, root: Pointer) : map<LSN, Address> 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    decreases dv.TheRankOf(root)
  {
    if root.None? then map[]
    else 
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | currMsgs.seqStart <= x < currMsgs.seqEnd :: root.value;
      MapUnion(BuildReprIndex(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), update)
  }

  predicate Init(v: Variables, tj: TruncatedJournal, strandStart: LSN, reserved: set<Address>)
  {
    && tj.Decodable()  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && strandStart <= tj.SeqStart()
    && v == 
        Variables(
          LinkedJournal.Variables(tj, EmptyHistoryAt(tj.SeqEnd())),
          BuildReprIndex(tj.diskView, tj.freshestRec)
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
