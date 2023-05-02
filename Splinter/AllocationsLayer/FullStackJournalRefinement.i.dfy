// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CrashTolerantJournal.i.dfy"
include "CoordinationJournal.i.dfy"
include "AllocationJournalRefinement.i.dfy"
include "../Journal/LikesJournalRefinement.i.dfy"
include "../Journal/PagedJournalRefinement.i.dfy"

module FullStackJournalRefinement {
  import opened Options
  import opened Maps
  import CoordinationJournal
  import AllocationJournal
  import AllocationJournalRefinement
  import LikesJournalRefinement
  import LikesJournal
  import LinkedJournalRefinement
  import PagedJournalRefinement
  import AbstractJournal
  import CrashTolerantJournal

  predicate FreshLabel(v: CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
  {
    && (lbl.InternalLabel? ==>
      && lbl.allocs !! v.persistent.AccessibleAUs()
      && (v.ephemeral.Known? ==> lbl.allocs !! v.ephemeral.v.AccessibleAUs())
      && (v.inFlight.Some? ==> lbl.allocs !! v.inFlight.value.AccessibleAUs()))
  }

  predicate JournalStatesAgrees(v: CoordinationJournal.Variables)
  {
    // frozen is a subset of ephemeral
    && ( v.ephemeral.Known? && v.inFlight.Some? ==>
      && var ephemeralDisk:= AllocationJournalRefinement.GetTj(v.ephemeral.v).diskView;
      && var inFlightDisk := v.inFlight.value.tj.diskView;
      && inFlightDisk.IsSubDiskWithNewerLSN(ephemeralDisk))
    // ephemeral and persistent state agrees
    && ( v.ephemeral.Known? ==> 
      && var ephemeralDisk:= AllocationJournalRefinement.GetTj(v.ephemeral.v).diskView;
      && var persistentDisk := v.persistent.tj.diskView;
      && MapsAgree(ephemeralDisk.entries, persistentDisk.entries))
  }

  // inflight and persistent pages are not free in the eye of mini allocator
  predicate InFlightAndPersistentPagesNotFree(v: CoordinationJournal.Variables)
  {
    && ( v.ephemeral.Known? && v.inFlight.Some? ==>
      && var miniAllocator := v.ephemeral.v.miniAllocator;
      && var inFlightDisk := v.inFlight.value.tj.diskView;
      && AllocationJournalRefinement.JournalPagesNotFree(inFlightDisk.entries.Keys, miniAllocator)
    )
    && ( v.ephemeral.Known? ==>
      && var miniAllocator := v.ephemeral.v.miniAllocator;
      && var persistentDisk := v.persistent.tj.diskView;
      && AllocationJournalRefinement.JournalPagesNotFree(persistentDisk.entries.Keys, miniAllocator)
    )
  }

  predicate Inv(v: CoordinationJournal.Variables)
  {
    && (v.ephemeral.Unknown? ==> v.inFlight.None?)
    && (v.ephemeral.Known? ==> AllocationJournalRefinement.Inv(v.ephemeral.v))
    && (v.inFlight.Some? ==> v.inFlight.value.tj.Decodable())
    && v.persistent.tj.Decodable()

    // not needed for stack refinement but will be used by cache
    && JournalStatesAgrees(v)
    && InFlightAndPersistentPagesNotFree(v)
  }

  function ILbl(lbl: CoordinationJournal.TransitionLabel) : CrashTolerantJournal.TransitionLabel
  {
    match lbl
      case LoadEphemeralFromPersistentLabel() => CrashTolerantJournal.LoadEphemeralFromPersistentLabel()
      case ReadForRecoveryLabel(records) => CrashTolerantJournal.ReadForRecoveryLabel(records)
      case QueryEndLsnLabel(endLsn) => CrashTolerantJournal.QueryEndLsnLabel(endLsn)
      case PutLabel(records) => CrashTolerantJournal.PutLabel(records)
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

  lemma AllocNextRefinesAbstract(v: AllocationJournal.Variables, v': AllocationJournal.Variables, lbl: AllocationJournal.TransitionLabel)
    requires AllocationJournalRefinement.Inv(v)
    requires AllocationJournalRefinement.Inv(v')
    requires AllocationJournal.Next(v, v', lbl)
    requires AllocationJournalRefinement.FreshLabel(v, lbl)
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

  lemma InternalLabelNextPreservesInv(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationJournal.Next(v, v', lbl)
    requires lbl.InternalLabel?
    ensures Inv(v')
  {
    AllocationJournalRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl));
    var allocStep :| AllocationJournal.NextStep(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl), allocStep);

    if allocStep.InternalNoOpStep? || allocStep.InternalMiniAllocatorPruneStep? {
      assert InFlightAndPersistentPagesNotFree(v');
      assert JournalStatesAgrees(v');
    }

    if allocStep.InternalMiniAllocatorFillStep? {
      assert JournalStatesAgrees(v');
      // if v.ephemeral.Known? {
      //   var miniAllocator := v.ephemeral.v.miniAllocator;
      //   var persistentDisk := v.persistent.tj.diskView;
      //   assert forall addr | addr in persistentDisk.entries :: addr.au !in lbl.allocs;
      //   if v.inFlight.Some? {
      //     var inFlightDisk := v.inFlight.value.tj.diskView;
      //     assert forall addr | addr in inFlightDisk.entries :: addr.au !in lbl.allocs;
      //   }
      // }
      // assert InFlightAndPersistentPagesNotFree(v');
    }

    if allocStep.InternalJournalMarshalStep? {
      AllocationJournalRefinement.InternalJournalMarshalDiskRelation(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl), allocStep);
    }
  }

  lemma CommitStartLabelNextPreservesInv(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires CoordinationJournal.Next(v, v', lbl)
    requires lbl.CommitStartLabel?
    ensures Inv(v')
  {
    AllocationJournalRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); 
    var ephemeralDisk := AllocationJournalRefinement.GetTj(v.ephemeral.v).diskView;
    var miniAllocator := v.ephemeral.v.miniAllocator;
    assert AllocationJournalRefinement.JournalPagesNotFree(ephemeralDisk.entries.Keys, miniAllocator) 
      by {  AllocationJournalRefinement.reveal_LikesJournalInv(); }
  }

  lemma InvNext(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires CoordinationJournal.Next(v, v', lbl)
    ensures Inv(v')
  {
    match lbl {
      case LoadEphemeralFromPersistentLabel() => {
        AllocationJournalRefinement.InitRefines(v'.ephemeral.v, v.persistent);
        AllocationJournalRefinement.InvInit(v'.ephemeral.v, v.persistent);
      }
      case ReadForRecoveryLabel(records) => {}
      case QueryEndLsnLabel(_) => {}
      case PutLabel(_) => { AllocationJournalRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case InternalLabel(allocs, deallocs) => { InternalLabelNextPreservesInv(v, v', lbl); }
      case QueryLsnPersistenceLabel(_) => {}
      case CommitStartLabel(_, _) => { CommitStartLabelNextPreservesInv(v, v', lbl); }
      case CommitCompleteLabel(_, _) => { AllocationJournalRefinement.NextRefines(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case CrashLabel() => {}
    }
  }

  lemma InitRefines(v: CoordinationJournal.Variables)
    requires CoordinationJournal.Init(v)
    ensures Inv(v)
    ensures CrashTolerantJournal.Init(I(v))
  {
  }

  lemma NextRefines(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
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
      case CommitStartLabel(_, _) => { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case CommitCompleteLabel(_, _)=> { AllocNextRefinesAbstract(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl)); }
      case CrashLabel() => {}
    }
  }

  // used by coordination system refinement
  lemma InternalLabelAccessibleAUs(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires FreshLabel(v, lbl)
    requires lbl.InternalLabel?
    requires lbl.allocs !! lbl.deallocs
    requires CoordinationJournal.Next(v, v', lbl)
    requires Inv(v')
    ensures v.EphemeralAUs() + lbl.allocs - lbl.deallocs == v'.EphemeralAUs()
  {
    var allocStep :| AllocationJournal.NextStep(v.ephemeral.v, v'.ephemeral.v, AllocLbl(v, v', lbl), allocStep);
    match allocStep {
      case InternalMiniAllocatorFillStep() => {}
      case InternalMiniAllocatorPruneStep() => {
        // maintained by allocation journal inv
        assume lbl.deallocs !! v.ephemeral.v.lsnAUIndex.Values; 
      }
      case InternalJournalMarshalStep(_, addr) => {
        AllocationJournalRefinement.reveal_LikesJournalInv();
        LikesJournalRefinement.reveal_IndexDomainValid();
      } 
      case InternalNoOpStep() => {}
    }
  }

  lemma CommitCompleteAccessibleAUs(v: CoordinationJournal.Variables, v': CoordinationJournal.Variables, lbl: CoordinationJournal.TransitionLabel)
    requires Inv(v)
    requires lbl.CommitCompleteLabel?
    requires CoordinationJournal.Next(v, v', lbl)
    ensures v'.EphemeralAUs() == v.EphemeralAUs() - lbl.discarded
  {
  }
}
