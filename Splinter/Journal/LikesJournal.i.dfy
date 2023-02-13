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

  /***************************************************************************************
  *                                    Labels and defs                                   *
  ***************************************************************************************/

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
    requires journal.Decodable()
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

  /***************************************************************************************
  *                                    State Machine                                     *
  ***************************************************************************************/

  datatype Variables = Variables(
    journal: LinkedJournal.Variables,
    // lsnAddrIndex maps in-repr lsn's to their page addr. Keeping this around because 
    // otherwise, we will need to walk the journal to figure out what addrs to remove from 
    // likes set when we do a DiscardOld
    lsnAddrIndex: map<LSN, Address>,
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

  // Update lsnAddrIndex with by discarding lsn's strictly smaller than bdy
  function {:opaque} lsnAddrIndexDiscardUpTo(lsnAddrIndex: map<LSN, Address>, bdy: LSN) : (out: map<LSN, Address>)
    ensures IsSubMap(out, lsnAddrIndex)
    ensures forall k | k in out :: bdy <= k
    ensures forall k | k in lsnAddrIndex &&  bdy <= k :: k in out
  {
    map x: LSN | x in lsnAddrIndex && bdy <= x :: lsnAddrIndex[x]
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
    // Addrs to delete from likes are pages that are between the old LSN and new LSN,
    // excluding the page containing the new LSN boundary
    && var lsnAddrIndex' := lsnAddrIndexDiscardUpTo(v.lsnAddrIndex, lbl.startLsn);
    && var keepAddrs := lsnAddrIndex'.Values;
    && var unrefAddrs := v.lsnAddrIndex.Values - keepAddrs;

    && v' == v.(
      journal := LinkedJournal.Variables(
        DiscardOldAndGarbageCollect(v.journal.truncatedJournal, lbl.startLsn, keepAddrs),
        if v.journal.unmarshalledTail.seqStart <= lbl.startLsn
        then v.journal.unmarshalledTail.DiscardOld(lbl.startLsn)
        else v.journal.unmarshalledTail
      ),
      lsnAddrIndex := lsnAddrIndex',
      likes := v.likes - multiset(unrefAddrs)
  )
  }

  // Update lsnAddrIndex with additional lsn's from a new record
  function lsnAddrIndexAppendRecord(lsnAddrIndex: map<LSN, Address>, msgs: MsgHistory, addr: Address) : (out: map<LSN, Address>)
    requires msgs.WF()
    requires msgs.seqStart < msgs.seqEnd
    ensures (forall x | msgs.seqStart <= x < msgs.seqEnd :: x !in lsnAddrIndex) 
            ==> out.Values == lsnAddrIndex.Values + {addr}
  {
    // msgs is complete map from seqStart to seqEnd 
    var update :=  map x: LSN | msgs.seqStart <= x < msgs.seqEnd :: addr;
    assert msgs.seqStart in update;  // witness
    MapUnion(lsnAddrIndex, update)
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
      lsnAddrIndex := lsnAddrIndexAppendRecord(v.lsnAddrIndex, v.journal.unmarshalledTail.DiscardRecent(cut), addr),
      likes := v.likes + multiset({addr})
    )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
  }

  function BuildLsnAddrIndexDefn(dv: DiskView, root: Pointer) : map<LSN, Address> 
    requires dv.Decodable(root)
    requires dv.Acyclic()
    requires root.Some? ==> dv.boundaryLSN < dv.entries[root.value].messageSeq.seqEnd
    decreases dv.TheRankOf(root)
  {
    if root.None? then map[]
    else 
      var currMsgs := dv.entries[root.value].messageSeq;
      var update :=  map x: LSN | Mathematics.max(dv.boundaryLSN, currMsgs.seqStart) <= x < currMsgs.seqEnd :: root.value;
      MapUnion(BuildLsnAddrIndexDefn(dv, dv.entries[root.value].CroppedPrior(dv.boundaryLSN)), update)
  }

  function BuildLsnAddrIndex(tj: TruncatedJournal) : map<LSN, Address> 
    requires tj.WF()
    requires tj.diskView.Decodable(tj.freshestRec)
    requires tj.diskView.Acyclic()
  {
    BuildLsnAddrIndexDefn(tj.diskView, tj.freshestRec)
  }

  predicate Init(v: Variables, journal: TruncatedJournal)
  {
    var tj := journal;
    && tj.Decodable()  // An invariant carried by CoordinationSystem from FreezeForCommit, past a crash, back here
    && tj.DiskIsTightWrtRepresentation()
    && v == 
        Variables(
          LinkedJournal.Variables(tj, EmptyHistoryAt(tj.BuildTight().SeqEnd())),
          BuildLsnAddrIndex(tj),
          TransitiveLikes(journal)
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
} // end module LikesJournal
