// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CrashTolerantJournal.i.dfy"
include "CoordinationJournal.i.dfy"
include "AllocationJournalRefinement.i.dfy"
include "../Journal/LikesJournalRefinement.i.dfy"
include "../Journal/PagedJournalRefinement.i.dfy"

module FullStackJournalRefinement {
  import opened Options
  import CoordinationJournal
  import AllocationJournal
  import AllocationJournalRefinement
  import LikesJournalRefinement
  import LikesJournal
  import LinkedJournalRefinement
  import PagedJournalRefinement
  import AbstractJournal
  import CrashTolerantJournal

  function ILbl(lbl: CoordinationJournal.TransitionLabel) : CrashTolerantJournal.TransitionLabel
  {
    match lbl
      case LoadEphemeralFromPersistentLabel() => CrashTolerantJournal.LoadEphemeralFromPersistentLabel()
      case ReadForRecoveryLabel(records) => CrashTolerantJournal.ReadForRecoveryLabel(records)
      case QueryEndLsnLabel(endLsn) => CrashTolerantJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(records) => CrashTolerantJournal.PutLabel(records)
      case FreezeAsLabel(_) => CrashTolerantJournal.InternalLabel()
      case InternalLabel(_, _) => CrashTolerantJournal.InternalLabel()
      case QueryLsnPersistenceLabel(syncLsn) => CrashTolerantJournal.QueryLsnPersistenceLabel(syncLsn)
      case CommitStartLabel(newBoundaryLsn, maxLsn) => CrashTolerantJournal.CommitStartLabel(newBoundaryLsn, maxLsn)
      case CommitCompleteLabel(requireEnd, _) => CrashTolerantJournal.CommitCompleteLabel(requireEnd)
      case CrashLabel() => CrashTolerantJournal.CrashLabel
  }

  function AllocLbl(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel) : AllocationJournal.TransitionLabel
    requires CoordinationJournal.Next(v, v', lbl)
  {
    match lbl
      case ReadForRecoveryLabel(records) => AllocationJournal.ReadForRecoveryLabel(records)
      case QueryEndLsnLabel(endLsn) => AllocationJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(records) => AllocationJournal.PutLabel(records)
      case InternalLabel(allocs, deallocs) => AllocationJournal.InternalAllocationsLabel(allocs, deallocs)
      case CommitStartLabel(_, _) => AllocationJournal.FreezeForCommitLabel(v'.inFlight.value)
      case CommitCompleteLabel(requireEnd, discarded) => AllocationJournal.DiscardOldLabel(v.inFlight.value.tj.SeqStart(), requireEnd, discarded)
      case _ => AllocationJournal.InternalAllocationsLabel({}, {}) // no op label
  }

  function IAllocLbl(lbl: AllocationJournal.TransitionLabel) : AbstractJournal.TransitionLabel
    requires lbl.WF()
  {
    PagedJournalRefinement.ILbl(LinkedJournalRefinement.ILbl(lbl.I().I()))
  }

  predicate Inv(v: CoordinationJournal.Variables)
  {
    && (v.ephemeral.Known? ==> AllocationJournalRefinement.Inv(v.ephemeral.v))
    && (v.inFlight.Some? ==> v.inFlight.value.tj.Decodable())
    && v.persistent.tj.Decodable()
  }

  function IJournal(journal: AllocationJournal.Variables) : AbstractJournal.Variables
    requires AllocationJournalRefinement.Inv(journal)
  {
    var likesJournal := AllocationJournalRefinement.I(journal);
    assert LikesJournalRefinement.Inv(likesJournal) by {
      AllocationJournalRefinement.reveal_LikesJournalInv();
    }
    var linkedJournal := LikesJournalRefinement.I(likesJournal);
    var pagedJournal := LinkedJournalRefinement.I(linkedJournal);
    var abstractJournal := PagedJournalRefinement.I(pagedJournal);
    abstractJournal
  }

  function IJournalImage(image: AllocationJournal.JournalImage) : CrashTolerantJournal.StoreImage
    requires image.tj.Decodable()
  {
    var pagedTj := LinkedJournalRefinement.ITruncatedJournal(image.tj);
    var msgHistory := PagedJournalRefinement.ITruncatedJournal(pagedTj);
    msgHistory
  }

  function IEphemeral(ephemeral: CoordinationJournal.Ephemeral) : CrashTolerantJournal.Ephemeral
    requires ephemeral.Known? ==> AllocationJournalRefinement.Inv(ephemeral.v)
  {
    if ephemeral.Unknown? then CrashTolerantJournal.Unknown
    else CrashTolerantJournal.Known(IJournal(ephemeral.v))
  }

  function I(v: CoordinationJournal.Variables) : CrashTolerantJournal.Variables
    requires Inv(v)
  {
    CrashTolerantJournal.Variables(
      IJournalImage(v.persistent), 
      IEphemeral(v.ephemeral),
      if v.inFlight.Some? then Some(IJournalImage(v.inFlight.value)) else None
    )
  }

  lemma InvNext(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires CoordinationJournal.Next(v, v', lbl)
    ensures Inv(v')
  {
    if lbl.LoadEphemeralFromPersistentLabel? 
    {
      AllocationJournalRefinement.InitRefines(v'.ephemeral.v, v.persistent);
      AllocationJournalRefinement.InvInit(v'.ephemeral.v, v.persistent);
    }

    if 
      || lbl.PutLabel? 
      || lbl.InternalLabel? 
      || lbl.CommitStartLabel? 
      || lbl.CommitCompleteLabel?  
    {
      AllocationJournalRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl));
    }
  }

  lemma AllocNextRefinesAbstract(v: AllocationJournal.Variables, v': AllocationJournal.Variables, lbl: AllocationJournal.TransitionLabel)
    requires AllocationJournalRefinement.Inv(v)
    requires AllocationJournalRefinement.Inv(v')
    requires AllocationJournal.Next(v, v', lbl)
    ensures AbstractJournal.Next(IJournal(v), IJournal(v'), IAllocLbl(lbl))
  {
    AllocationJournalRefinement.NextRefines(v, v', lbl);

    var likesJournal := AllocationJournalRefinement.I(v);
    var likesJournal' := AllocationJournalRefinement.I(v');
    assert LikesJournalRefinement.Inv(likesJournal) by {
      AllocationJournalRefinement.reveal_LikesJournalInv();
    }
    LikesJournalRefinement.NextRefines(likesJournal, likesJournal', lbl.I());

    var linkedJournal := LikesJournalRefinement.I(likesJournal);
    var linkedJournal' := LikesJournalRefinement.I(likesJournal');
    LinkedJournalRefinement.NextRefines(linkedJournal, linkedJournal', lbl.I().I());

    var pagedJournal := LinkedJournalRefinement.I(linkedJournal);
    var pagedJournal' := LinkedJournalRefinement.I(linkedJournal');
    var pagedLbl := LinkedJournalRefinement.ILbl(lbl.I().I());
    PagedJournalRefinement.NextRefines(pagedJournal, pagedJournal', pagedLbl);
  }

  lemma NextRefines(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires CoordinationJournal.Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), ILbl(lbl))
  {
    InvNext(v, v', lbl);

    match lbl {
      case LoadEphemeralFromPersistentLabel() => {}
      case ReadForRecoveryLabel(records) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case QueryEndLsnLabel(_) => {}
      case PutLabel(_) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case InternalLabel(allocs, deallocs) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case QueryLsnPersistenceLabel(_) => {}
      case FreezeAsLabel(_) => {}
      case CommitStartLabel(_, _) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case CommitCompleteLabel(_, _)=> { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case CrashLabel() => {}
    }
  }
}
