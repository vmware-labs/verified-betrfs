// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "GCCrashTolerantJournal.i.dfy"
include "../CoordinationLayer/AbstractJournal.i.dfy"
include "../CoordinationLayer/CrashTolerantJournal.i.dfy"
include "../Journal/PagedJournalRefinement.i.dfy"
include "../Journal/LinkedJournalRefinement.i.dfy"
include "../Journal/ReprJournalRefinement.i.dfy"

module GCCrashTolerantJournalRefinement {
  import opened Options
  import AbstractJournal
  import PagedJournalRefinement
  import LinkedJournalRefinement
  import ReprJournalRefinement
  import CrashTolerantJournal 
  import opened GCCrashTolerantJournal

  function IALabel(lbl: TransitionLabel) : CrashTolerantJournal.TransitionLabel
  {
    lbl.base
  }

  function IImage(image: StoreImage) : CrashTolerantJournal.StoreImage 
    requires image.WF()
  {
    // turn GCTruncatedJournal to msgHistory
    PagedJournalRefinement.ITruncatedJournal(LinkedJournalRefinement.ITruncatedJournal(image.journal))
  }

  function IReprJ(rj: ReprJournal.Variables) : AbstractJournal.Variables
    requires rj.WF()
    requires rj.journal.truncatedJournal.Decodable()
  {
    PagedJournalRefinement.I(LinkedJournalRefinement.I(ReprJournalRefinement.I(rj)))
  }

  function IReprJLabel(rlbl: ReprJournal.TransitionLabel) : AbstractJournal.TransitionLabel
    requires rlbl.WF()
  {
    PagedJournalRefinement.ILbl(LinkedJournalRefinement.ILbl(rlbl.I()))
  }

  function I(v: Variables) : CrashTolerantJournal.Variables
    requires v.WF()
    requires v.ephemeral.Known? ==> v.ephemeral.v.journal.truncatedJournal.Decodable()
  {
    CrashTolerantJournal.Variables(
      IImage(v.persistent),
      if v.ephemeral.Unknown?  then CrashTolerantJournal.Unknown else CrashTolerantJournal.Known(IReprJ(v.ephemeral.v)),
      if v.inFlight.None? then None else Some(IImage(v.inFlight.value))
    )
  }

  predicate Inv(v: Variables) {
    && v.WF()
    && (v.ephemeral.Known? ==> 
          && v.ephemeral.v.journal.truncatedJournal.Decodable()
          && ReprJournalRefinement.Inv(v.ephemeral.v)
      )
  }

  lemma InitRefines(v: Variables)
    requires Inv(v)
    requires Init(v)
    ensures Inv(v)
    ensures CrashTolerantJournal.Init(I(v))
  {}

  lemma LoadEphemeralFromPersistentRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    requires lbl.base.LoadEphemeralFromPersistentLabel?
    ensures Inv(v') 
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    ReprJournalRefinement.InvInit(v'.ephemeral.v, v.persistent);
  }

  lemma JournalNext(j: ReprJournal.Variables, j': ReprJournal.Variables, lbl: ReprJournal.TransitionLabel)
    requires ReprJournalRefinement.Inv(j)
    requires ReprJournal.Next(j, j', lbl)
    ensures ReprJournalRefinement.Inv(j')
    ensures AbstractJournal.Next(IReprJ(j), IReprJ(j'), IReprJLabel(lbl))
  {
    ReprJournalRefinement.NextRefines(j, j', lbl);
    LinkedJournalRefinement.NextRefines(
      ReprJournalRefinement.I(j),
      ReprJournalRefinement.I(j'),
      lbl.I());
    PagedJournalRefinement.NextRefines(
      LinkedJournalRefinement.I(ReprJournalRefinement.I(j)),
      LinkedJournalRefinement.I(ReprJournalRefinement.I(j')),
      LinkedJournalRefinement.ILbl(lbl.I()));
  }

  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.ReadForRecoveryLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var j, j' := v.ephemeral.v, v'.ephemeral.v;
    var lbl := ReprJournal.ReadForRecoveryLabel(lbl.base.records);
    JournalNext(j, j', lbl);
  }

  lemma PutRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.PutLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    // This lemma is defined to move the obligation out of NextRefines
  }

  lemma InternalRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.InternalLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var j, j' := v.ephemeral.v, v'.ephemeral.v;
    var jlbl: ReprJournal.TransitionLabel;
    if Internal(v, v', lbl) {
      jlbl := ReprJournal.InternalLabel();
    } else {
      jlbl := ReprJournal.InternalJournalGCLabel(lbl.allocations, lbl.freed);
    }
    ReprJournalRefinement.InvNext(j, j', jlbl);
    JournalNext(j, j', jlbl);
  }

  lemma CommitStartRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.CommitStartLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var j, j' := v.ephemeral.v, v'.ephemeral.v;
    var jlbl := ReprJournal.FreezeForCommitLabel(v'.inFlight.value);
    JournalNext(j, j', jlbl);
  }

  lemma CommitCompleteRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.CommitCompleteLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var j, j' := v.ephemeral.v, v'.ephemeral.v;
    var jlbl := ReprJournal.DiscardOldLabel(v.inFlight.value.journal.SeqStart(), lbl.base.requireEnd);
    JournalNext(j, j', jlbl);
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    match lbl.base {
      case LoadEphemeralFromPersistentLabel() =>
        LoadEphemeralFromPersistentRefines(v, v', lbl);
      case ReadForRecoveryLabel(_) => 
        ReadForRecoveryRefines(v, v', lbl);
      case QueryEndLsnLabel(_) => {}
      case PutLabel(_) =>
        PutRefines(v, v', lbl);
      case InternalLabel() => 
        InternalRefines(v, v', lbl);
      case QueryLsnPersistenceLabel(_) => {}
      case CommitStartLabel(_, _) => 
        CommitStartRefines(v, v', lbl);
      case CommitCompleteLabel(_) => 
        CommitCompleteRefines(v, v', lbl);
      case CrashLabel() => {}
    }
  }
}
