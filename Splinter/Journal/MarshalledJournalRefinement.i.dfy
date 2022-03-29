// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournalRefinement.i.dfy"
include "MarshalledJournal.i.dfy"

module MarhalledJournalRefinement
// TODO refines RefinementObligation(JournalLabels, PagedJournal)
{
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened JournalLabels
  import LinkedJournal
  import LinkedJournalRefinement
  import opened MarshalledJournal

  predicate HasTypedModel(v: Variables)
  {
    exists typed :: TypeProvidesModel(v, typed)
  }

  function TheTypedModel(v: Variables) : LinkedJournal.Variables
    requires HasTypedModel(v)
  {
    var typed :| TypeProvidesModel(v, typed); typed
  }

  lemma TypedModelUnique()
    ensures forall v, t1, t2 | TypeProvidesModel(v, t1) && TypeProvidesModel(v, t2) :: t1 == t2
  {
    forall v, t1, t2 | TypeProvidesModel(v, t1) && TypeProvidesModel(v, t2)
      ensures t1 == t2
    {
      var e1 := t1.truncatedJournal.diskView.entries;
      var e2 := t2.truncatedJournal.diskView.entries;
      forall addr ensures addr in e1 <==> addr in e2 {
        assert addr in MarshalDisk(t2.truncatedJournal.diskView.entries) || true;  // trigger
      }
      forall addr | addr in e1
        ensures e1[addr] == e2[addr]
      {
        ParseAxiom(e1[addr]);
        ParseAxiom(e2[addr]);
        assert Marshal(e1[addr]) == v.disk[addr] == Marshal(e2[addr]);  // trigger
      }

    }
  }

  predicate Inv(v: Variables) {
    && HasTypedModel(v)
    && LinkedJournalRefinement.Inv(TheTypedModel(v))
  }

  lemma InvInit(v: Variables, tj: LinkedJournal.TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
  {
    TypedModelUnique();
  }

  function I(v: Variables) : LinkedJournal.Variables
    requires Inv(v)
  {
    TheTypedModel(v)
  }
  
  lemma RefinementInit(v: Variables, tj: LinkedJournal.TruncatedJournal)
    requires Init(v, tj)
    ensures Inv(v)
    ensures LinkedJournal.Init(I(v), tj)
  {
    TypedModelUnique();
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures LinkedJournal.Next(I(v), I(v'), lbl)
  {
    var t, t' :|
      && TypeProvidesModel(v, t)
      && TypeProvidesModel(v', t')
      && LinkedJournal.Next(t, t', lbl);
    TypedModelUnique();
    LinkedJournalRefinement.InvNext(t, t', lbl);
    LinkedJournalRefinement.NextRefines(t, t', lbl);
  }
}
