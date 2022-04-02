// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BlockCoordinationSystem.i.dfy"
include "../CoordinationLayer/CoordinationSystem.i.dfy"

module BlockCoordinationSystemRefinement
{
  import opened Options
  import opened BlockCoordinationSystem
  import MarshalledJournal
  import CoordinationSystem
  import AbstractJournal
  import opened MsgHistoryMod
  import LinkedJournal

  predicate JournalImageInv(journalImage: MarshalledJournal.JournalImage)
  {
    && journalImage.WF()
    && journalImage.I().diskView.Acyclic()
    && journalImage.I().I().WF()
  }

  predicate DiskImageInv(diskImage: DiskImage)
  {
    && JournalImageInv(diskImage.journal)
  }

  predicate MarshalledJournalInv(v: MarshalledJournal.Variables)
  {
    && JournalImageInv(v.journalImage)
    && v.unmarshalledTail.WF()
    && JournalImageI(v.journalImage).CanConcat(v.unmarshalledTail)
  }

  predicate EphemeralInv(ephemeral: Ephemeral)
  {
    && (ephemeral.Known? ==> MarshalledJournalInv(ephemeral.journal))
  }

  predicate Inv(v: Variables)
  {
    && DiskImageInv(v.persistentImage)
    && EphemeralInv(v.ephemeral)
    && (v.inFlightImage.Some? ==> DiskImageInv(v.inFlightImage.value))
  }

  function JournalImageI(journalImage: MarshalledJournal.JournalImage) : MsgHistory
    requires JournalImageInv(journalImage)
  {
    journalImage.I().I().I()
  }

  function DiskImageI(diskImage: DiskImage) : CoordinationSystem.DiskImage
    requires DiskImageInv(diskImage)
  {
    CoordinationSystem.DiskImage(diskImage.mapadt, JournalImageI(diskImage.journal))
  }

  function MarshalledJournalI(v: MarshalledJournal.Variables) : AbstractJournal.Variables
    requires MarshalledJournalInv(v)
  {
    AbstractJournal.Variables(JournalImageI(v.journalImage).Concat(v.unmarshalledTail))
  }

  function EphemeralI(ephemeral: Ephemeral) : CoordinationSystem.Ephemeral
    requires EphemeralInv(ephemeral)
  {
    if ephemeral.Unknown? then
      CoordinationSystem.Unknown
    else
      CoordinationSystem.Known(
      ephemeral.progress,
      ephemeral.syncReqs,
      ephemeral.mapadt,
      ephemeral.mapLsn,
      MarshalledJournalI(ephemeral.journal),
      ephemeral.frozenMap
      )
  }

  function I(v: Variables) : CoordinationSystem.Variables
    requires Inv(v)
  {
    CoordinationSystem.Variables(
      DiskImageI(v.persistentImage),
      EphemeralI(v.ephemeral),
      if v.inFlightImage.Some? then Some(DiskImageI(v.inFlightImage.value)) else None
      )
  }

  lemma RefinementInit(v: Variables)
    requires v.Init()
    ensures Inv(v)
    ensures I(v).Init()
  {
    assert v.persistentImage.journal.TypeProvidesModel(LinkedJournal.Mkfs());
    assert v.persistentImage.journal.I().diskView.PointersRespectRank(map[]);
  }

  lemma RefinementNext(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
}
