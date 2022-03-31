// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "LinkedJournal.i.dfy"

module MarshalledJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import JournalLabels
  import opened Maps
  import LinkedJournal

  datatype JournalSB = JournalSB(
    boundaryLSN: LSN,
    freshestRec: Pointer)

  datatype JournalImage = JournalImage(
    superblock: JournalSB,
    blockDiskView: Disk)

  // TODO(jonh): appeal to parent lbl
  datatype TransitionLabel =
      ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: MsgHistory, journalImage: JournalImage)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
      // TODO(jonh): requireEnd is an enabling-condition check to enforce
      // MapIsFresh in CommitComplete. I don't think it's actually necessary,
      // but removing it broke the CoordinationSystemRefinement proof and I
      // couldn't fix it in five minutes.
    | InternalLabel()

  datatype Variables = Variables(
    journalImage: JournalImage,
    unmarshalledTail: MsgHistory)

  function MarshalDisk(typed: map<Address, LinkedJournal.JournalRecord>) : Disk
  {
    map addr | addr in typed :: Marshal(typed[addr])
  }

  predicate TypeProvidesModel(v: Variables, typed: LinkedJournal.Variables)
  {
    && typed.unmarshalledTail == v.unmarshalledTail 
    && typed.truncatedJournal.freshestRec == v.freshestRec
    && MarshalDisk(typed.truncatedJournal.diskView.entries) == v.disk
    && typed.truncatedJournal.diskView.boundaryLSN == v.boundaryLSN
  }

  function JournalImageI() : LinkedJournal.TruncatedJournal
  {
    true
  }

  function I(v: Variables) : LinkedJournal.Variables {
    LinkedJournal.Variables(v.journalImage.I(), v.unmarshalledTail)
  }

  predicate Init(v: Variables, journalImage: JournalImage)
  {
    (exists t ::
      && TypeProvidesModel(v, t)
      && LinkedJournal.Init(t, tj)
      && v.disk == journalImage.blockDiskView
      && v.boundaryLSN == journalImage.superblock.boundaryLSN
      && v.freshestRec == journalImage.superblock.pointer
//      && v.unmarshalledTail.IsEmpty() // Implied by LinkedJournal.Init && TypeProvidesModel.
    )
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel, keepReceiptLines: nat)
  {
    (exists t, t' ::
      // Connection up a layer
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedJournal.Next(t, t', lbl)

      // Have a tight model of the disk that's rooted where the SB points.
      && var fr := journalImage.superblock.freshestRec;
      && lbl.journalImage.blockDiskView.WF()
      && lbl.journalImage.blockDiskView.IsSubDisk(v.disk)
      && lbl.journalImage.blockDiskView.IsNondanglingPointer(fr)
      && lbl.journalImage.blockDiskView.Tight()

      // Start where the v journal starts
      && lbl.journalImage.superblock.boundaryLSN == v.boundaryLSN

      // End at a block that matches the end we promised in the (abstract ghosty) frozenJournal
      && (if lbl.frozenJournal.IsEmpty()
          then fr.None?
          else
            && fr.Some?
            && t.diskView[fr.value].messageSeq.seqEnd == lbl.frozenJournal.seqEnd
         )
    )
  }

  predicate Inv(v: Variables) {
    && (exists typed :: TypeProvidesModel(v, typed))
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel, journalImage: JournalImage)
  {
    (exists t, t' ::
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedJournal.Next(t, t', lbl)
      && AdditionalStupidConstraint(v, v', t, lbl, journalImage)
    )
  }
}
