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

  lemma ReadForRecoveryRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl) 
    requires lbl.base.ReadForRecoveryLabel?
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    var j, j' := v.ephemeral.v, v'.ephemeral.v;
    var jLbl := ReprJournal.ReadForRecoveryLabel(lbl.base.records);
    ReprJournalRefinement.NextRefines(j, j', jLbl);
    LinkedJournalRefinement.NextRefines(
      ReprJournalRefinement.I(j),
      ReprJournalRefinement.I(j'),
      jLbl.I());
    PagedJournalRefinement.NextRefines(
      LinkedJournalRefinement.I(ReprJournalRefinement.I(j)),
      LinkedJournalRefinement.I(ReprJournalRefinement.I(j')),
      LinkedJournalRefinement.ILbl(jLbl.I()));
    assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
  }

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl))
  {
    match lbl.base {
      case LoadEphemeralFromPersistentLabel() =>
        // Done
        LoadEphemeralFromPersistentRefines(v, v', lbl);
        assert Inv(v');
        assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case ReadForRecoveryLabel(_) => 
        // Done
        ReadForRecoveryRefines(v, v', lbl);
        assert Inv(v');
        assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case QueryEndLsnLabel(_) => 
        assume false;
        assert Inv(v');
        assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case PutLabel(_) =>
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case InternalLabel() => 
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case QueryLsnPersistenceLabel(_) => 
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case CommitStartLabel(_, _) => 
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case CommitCompleteLabel(_) => 
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
      case CrashLabel() => 
        assume false;
        // assert Inv(v');
        // assert CrashTolerantJournal.Next(I(v), I(v'), IALabel(lbl));
    }
  }




}

