// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"
include "MarhsalledJournal.i.dfy"

module AllocatedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened Maps
  import LinkedJournal
  import opened GenericDisk

  datatype TransitionLabel =
      LearnPersistentLabel(marshalled: MarshalledJournal.JournalImage)
    | FreezeForCommitLabel(frozenJournal: MarshalledJournal.JournalImage)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
      // TODO(jonh): requireEnd is an enabling-condition check to enforce
      // MapIsFresh in CommitComplete. I don't think it's actually necessary,
      // but removing it broke the CoordinationSystemRefinement proof and I
      // couldn't fix it in five minutes.
    | OtherLabel(mlbl: MarshalledJournal.TransitionLabel)
  {
    predicate WF()
    {
      (OtherLabel? ==>
        || mlbl.ReadForRecoveryLabel?
        || mlbl.QueryEndLsnLabel?
        || mlbl.PutLabel?
        || mlbl.InternalLabel?
      )
    }
  }

  datatype Alloction = Alloction(addresses: set<Addr>)

  function AllocationFor(marshalledImage: MarshalledJournal.JournalImage)
  {
    image.diskView.entries.Keys
  }

  datatype JournalImage = JournalImage(
    marshalled: MarshalledJournal.JournalImage,
    allocation: Allocation)
  {
    predicate Valid()
    {
      allocation == AllocationFor(marshalled)
    }
  }

  datatype Ephemeral = Unknown | Known(
    marshalled: MarshalledJournal.Variables,
    allocation: Allocation)
  {
    predicate Valid()
    {
      allocation == AllocationFor(marshalled.journalImage)
    }
  }

  datatype Variables = Variables(
    persistent: Option<JournalImage>, // This state machine "learns" the journal image allocation by reading the persistent journal at startup.
    ephemeral: Ephemeral,
    inFlight: Option<JournalImage>)
  {
    predicate WF()
    {
      && (ephemeral.Known? ==> persistent.Some?)
      && (inFlight.Some? ==> ephemeral.Known?)
    }
  }

  predicate Init(v: Variables)
  {
    && v.persistent.None?
    && v.ephemeral.Unknown?
    && v.inFlight.None?
  }

  predicate LearnPersistent(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.LearnPersistentLabel?
    && v.persistent.None?
    && v' == Variables(JournalImage(lbl.marshalled, AllocationFor(lbl.marshalled)), Unknown, None)
  }

  predicate FreezeForCommit(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.WF()
    && lbl.FreezeForCommitLabel?
    && v.WF()
    && v.ephemeral.Known?
    && v.inFlight.None?

    && MarshalledJournal.Next(v.ephemeral.marshalled, v'.ephemeral.marshalled,
        MarshalledJournal.FreezeForCommitLabel(lbl.frozenJournal))
    && v' == v.(
          ephemeral := Known(
            v'.ephemeral.marshalled,  // constrained by predicate above
            v.ephemeral.allocation),  // doesn't change
          inFlight := JournalImage(lbl.frozenJournal, AllocationFor(lbl.frozenJournal))
      )
  }

  predicate DiscardOld(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.WF()
    && lbl.DiscardOldLabel?
    && v.WF()
    && v.ephemeral.Known?
    && v.inFlight.Some?

    && MarshalledJournal.Next(v.ephemeral.marshalled, v'.ephemeral.marshalled,
        MarshalledJournal.DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
    && v' == v.(
          persistent := v.inFlight,
          ephemeral := Known(
            v'.ephemeral.marshalled,  // constrained by predicate above
            v.ephemeral.allocation),  // doesn't change
          inFlight := None)
  }

  predicate Other(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.WF()
    && lbl.OtherLabel?
    && v.WF()

    && MarshalledJournal.Next(v.ephemeral.marshalled, v'.ephemeral.marshalled, lbl.mlbl)
    && v' == v.(
          ephemeral := Known(
            v'.ephemeral.marshalled,  // constrained by predicate above
            v.ephemeral.allocation)  // doesn't change TODO except it does when doing internal!
        )
  }

  predicate 
    | ReadForRecoveryLabel(messages: MsgHistory)
    | FreezeForCommitLabel(frozenJournal: JournalImage)
    | QueryEndLsnLabel(endLsn: LSN)
    | PutLabel(messages: MsgHistory)
    | DiscardOldLabel(startLsn: LSN, requireEnd: LSN)
      // TODO(jonh): requireEnd is an enabling-condition check to enforce
      // MapIsFresh in CommitComplete. I don't think it's actually necessary,
      // but removing it broke the CoordinationSystemRefinement proof and I
      // couldn't fix it in five minutes.
    | InternalLabel()

  predicate Inv(v: Variables)
  {
    && (v.persistent.Some? ==> v.persistent.value.Valid())
    && v.ephemeral.Valid()
    && (v.inFlight.Some? ==> v.inFlight.value.Valid())
  }
}
