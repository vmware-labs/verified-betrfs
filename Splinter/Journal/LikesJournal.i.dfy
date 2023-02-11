// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournal.i.dfy"
include "../Likes.i.dfy"

// A Journal that keeps an in-memory index that maps each in-use LSN to the Address that stores it.
// The impl will keep such an index so that Discard can return freed Addresses without having to
// fault in the freed section of the journal to learn the chain of addresses involved.
module LikesJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import LinkedJournal
  import GenericDisk
  import Mathematics
  import opened LikesMod

  type Pointer = GenericDisk.Pointer
  type Address = GenericDisk.Address
  type DiskView = LinkedJournal.DiskView
  type TruncatedJournal = LinkedJournal.TruncatedJournal

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: TruncatedJournal)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
    // Internal-x labels refine to no-ops at the abstract spec
    | InternalJournalGCLabel(allocations: set<Address>, freed: set<Address>)
    | InternalLabel()  // Local No-op label
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.Decodable())
    }

    function I(): LinkedJournal.TransitionLabel {
      match this {
        case ReadForRecoveryLabel(messages) => LinkedJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => LinkedJournal.FreezeForCommitLabel(frozenJournal)
        case QueryEndLsnLabel(endLsn) => LinkedJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => LinkedJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd) => LinkedJournal.DiscardOldLabel(startLsn, requireEnd)
        case InternalJournalGCLabel(_, _) => LinkedJournal.InternalLabel()
        case InternalLabel() => LinkedJournal.InternalLabel()
      }
    }
  }

  // Account for every page reachable from bbtree.Root(), including
  // a ref the root. The caller of this, from some other data structure,
  // will multiply all my likes by the number of references into it from
  // that outer structure, so we can't leave any reachable stuff with zero.
  function TransitiveLikes(journal: LinkedJournal.TruncatedJournal) : Likes
    requires journal.WF()
    decreases journal.diskView.TheRankOf(journal.freshestRec)
  {
      // Does this become CanCrop?
    if journal.freshestRec.None?
    then
      NoLikes()
    else
      var rootLikes := multiset{ journal.freshestRec.value };
      TransitiveLikes(journal.Crop(1)) + rootLikes
  }

  function ImperativeLikes(v: Variables) : Likes
  {
    // no outbound refs from journal, so pretty simple
    v.likes
  }

  // TODO invariant; move to proof
  predicate ImperativeAgreement(v: Variables) 
  {
    && v.journal.truncatedJournal.diskView.Acyclic()
    // && v.branchedVars.branched.Valid()
    && TransitiveLikes(v.journal.truncatedJournal) == ImperativeLikes(v)
  }

  datatype Variables = Variables(
    journal: LinkedJournal.Variables,
    likes: Likes
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
//////////////////////////////////////////////////////////////////////////////
-------------------------------------------------------------------------------
    LEFT OFF HERE translating repr updates into likes updates
-------------------------------------------------------------------------------
//////////////////////////////////////////////////////////////////////////////
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
    // State transition
    && LinkedJournal.InternalJournalMarshal(v.journal, v'.journal, lbl.I(), cut, addr)
    && v' == v.(
      journal := v'.journal,
      reprIndex := reprIndexAppendRecord(v.reprIndex, v.journal.unmarshalledTail.DiscardRecent(cut), addr)
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

  predicate Init(v: Variables, journal: TruncatedJournal)
  {
    var tj := journal;
    && tj.Decodable()  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && tj.DiskIsTightWrtRepresentation()
    && v == 
        Variables(
          LinkedJournal.Variables(tj, EmptyHistoryAt(tj.BuildTight().SeqEnd())),
          BuildReprIndex(tj)
      )
  }

  datatype Step =
      ReadForRecoveryStep(depth: nat)
    | FreezeForCommitStep(depth: nat)
    | ObserveFreshJournalStep()
    | PutStep()
    | DiscardOldStep()
    | InternalJournalMarshalStep(cut: LSN, addr: Address)
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
      case InternalNoOpStep() =>  InternalNoOp(v, v', lbl)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
