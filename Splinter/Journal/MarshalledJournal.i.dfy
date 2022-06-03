// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "LinkedJournal.i.dfy"

module MarshalledJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import LinkedJournal
  import opened GenericDisk

  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: JournalImage)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
      // TODO(jonh): requireEnd is an enabling-condition check to enforce
      // MapIsFresh in CommitComplete. I don't think it's actually necessary,
      // but removing it broke the CoordinationSystemRefinement proof and I
      // couldn't fix it in five minutes.
    | InternalLabel(addrs: set<Address>)
  {
    predicate WF() {
      && (FreezeForCommitLabel? ==> frozenJournal.WF())
    }

    function I() : LinkedJournal.TransitionLabel
      requires WF()
    {
      match this
        case ReadForRecoveryLabel(messages) => LinkedJournal.ReadForRecoveryLabel(messages)
        case FreezeForCommitLabel(frozenJournal) => LinkedJournal.FreezeForCommitLabel(frozenJournal.I())
        case QueryEndLsnLabel(endLsn) => LinkedJournal.QueryEndLsnLabel(endLsn)
        case PutLabel(messages) => LinkedJournal.PutLabel(messages)
        case DiscardOldLabel(startLsn, requireEnd) => LinkedJournal.DiscardOldLabel(startLsn, requireEnd)
        case InternalLabel(addrs) => LinkedJournal.InternalLabel(addrs)
    }
  }

  datatype JournalSB = JournalSB(
    boundaryLSN: LSN,
    freshestRec: Pointer)

  datatype JournalImage = JournalImage(
    superblock: JournalSB,
    diskView: DiskView)
  {
    predicate TypeProvidesModel(typed: LinkedJournal.TruncatedJournal) {
      && typed.WF()
      && superblock.boundaryLSN == typed.diskView.boundaryLSN
      && superblock.freshestRec == typed.freshestRec
      && diskView == MarshalDisk(typed.diskView.entries)
    }

    predicate HasModel() {
      exists typed :: TypeProvidesModel(typed)
    }

    predicate WF()
    {
      HasModel()
    }

    function I() : LinkedJournal.TruncatedJournal
      requires WF()
    {
      var typed :| TypeProvidesModel(typed); typed
    }

    predicate IsEmpty() {
      superblock.freshestRec.None?
    }

    function SeqStart() : LSN
    {
      superblock.boundaryLSN
    }

    function SeqEnd() : LSN
      requires WF()
    {
      I().SeqEnd()
    }

    function Repr() : set<Address>
    {
      diskView.entries.Keys
    }
  }

  function EmptyJournalImage() : (out: JournalImage)
    ensures out.WF()
    ensures out.IsEmpty()
  {
    var out := JournalImage(JournalSB(0, None), DiskView(map[]));
    assert out.TypeProvidesModel(LinkedJournal.Mkfs());
    out
  }


  datatype Variables = Variables(
    journalImage: JournalImage,
    unmarshalledTail: MsgHistory)
  {
    predicate WF()
    {
      && journalImage.WF()
      && unmarshalledTail.WF()
    }
  }

  function MarshalDisk(typed: map<Address, LinkedJournal.JournalRecord>) : DiskView
  {
    DiskView(map addr | addr in typed :: Marshal(typed[addr]))
  }

  predicate TypeProvidesModel(v: Variables, typed: LinkedJournal.Variables)
  {
    && v.unmarshalledTail == typed.unmarshalledTail
    && v.journalImage.TypeProvidesModel(typed.truncatedJournal)
  }

  predicate InitModel(v: Variables, journalImage: JournalImage, t: LinkedJournal.Variables)
  {
    && TypeProvidesModel(v, t)
    && t.truncatedJournal.diskView.Acyclic()
    && LinkedJournal.Init(t, t.truncatedJournal)  // TODO(jonh): second argument now feels weirdly redundant
    && v.journalImage == journalImage
//      && v.unmarshalledTail.IsEmpty() // Implied by LinkedJournal.Init && TypeProvidesModel.
  }

  predicate Init(v: Variables, journalImage: JournalImage)
  {
    (exists t :: InitModel(v, journalImage, t))
  }

// TODO(jonh): delete this dead code!?
//\  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
//\    requires lbl.WF()
//\  {
//\    && lbl.FreezeForCommitLabel?
//\    && (exists t, t' ::
//\      // Connection up a layer
//\      && TypeProvidesModel(v, t)
//\      && TypeProvidesModel(v', t')
//\      && LinkedJournal.Next(t, t', lbl.I())
//\
//\      && var fr := lbl.frozenJournal.superblock.freshestRec;
//\
//\      // Have a tight model of the disk that's rooted where the SB points.
//\      && lbl.frozenJournal.diskView.IsSubDisk(v.journalImage.diskView)
//\      && lbl.frozenJournal.superblock.boundaryLSN == v.journalImage.superblock.boundaryLSN
//\      && lbl.frozenJournal.diskView.IsNondanglingPointer(fr)
//\      && lbl.frozenJournal.diskView.Tight()
//\
//\      // Constraint on freshestRec: End at a block that matches the end we
//\      // promised in the (abstract ghosty) frozenJournal
//\      && (if lbl.frozenJournal.IsEmpty()
//\          then fr.None?
//\          else
//\            && fr.Some?
//\            && t.truncatedJournal.diskView.entries[fr.value].messageSeq.seqEnd == lbl.frozenJournal.SeqEnd()
//\         )
//\    )
//\  }

  predicate Inv(v: Variables) {
    && (exists typed :: TypeProvidesModel(v, typed))
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.WF()
    && (exists t, t' ::
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedJournal.Next(t, t', lbl.I())
    )
  }
}
