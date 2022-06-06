// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedJournalRefinement.i.dfy"
include "MarshalledJournal.i.dfy"

module MarshalledJournalRefinement
// TODO refines RefinementObligation(JournalLabels, PagedJournal)
{
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import LinkedJournal
  import LinkedJournalRefinement
  import opened MarshalledJournal
  import opened GenericDisk

  predicate HasTypedModel(v: Variables)
  {
    exists typed :: TypeProvidesModel(v, typed)
  }

  function TheTypedModel(v: Variables) : LinkedJournal.Variables
    requires HasTypedModel(v)
  {
    // todo(jonh): this is same as I()
    var typed :| TypeProvidesModel(v, typed); typed
  }

  lemma TypedModelUnique()
    ensures forall v: JournalImage, t1, t2 | v.TypeProvidesModel(t1) && v.TypeProvidesModel(t2) :: t1 == t2
  {
    forall v: JournalImage, t1, t2 | v.TypeProvidesModel(t1) && v.TypeProvidesModel(t2)
      ensures t1 == t2
    {
      var e1 := t1.diskView.entries;
      var e2 := t2.diskView.entries;
      forall addr ensures addr in e1 <==> addr in e2 {
        assert addr in MarshalDisk(t2.diskView.entries).entries || true;  // trigger
      }
      forall addr | addr in e1
        ensures e1[addr] == e2[addr]
      {
        ParseAxiom(e1[addr]);
        ParseAxiom(e2[addr]);
        //assert Marshal(e1[addr]) == v.journalImage.diskView.entries[addr] == Marshal(e2[addr]);  // trigger
        assert Marshal(e1[addr]) == v.diskView.entries[addr];  // TODO(jonh): which is a trigger?
        assert v.diskView.entries[addr] == Marshal(e2[addr]);  // trigger
      }

    }
  }

//  lemma MkfsRefines()
//    ensures Mkfs().WF()
//    ensures Mkfs().I().Decodable()
//  {
//    assert Mkfs().TypeProvidesModel(LinkedJournal.Mkfs());
//    LinkedJournalRefinement.MkfsRefines();
//    assert Mkfs().I() == LinkedJournal.Mkfs();  // trigger
//  }

  predicate Inv(v: Variables) {
    && HasTypedModel(v)
    && LinkedJournalRefinement.Inv(TheTypedModel(v))
  }

  lemma InvInit(v: Variables, journalImage: JournalImage)
    requires Init(v, journalImage)
    ensures Inv(v)
  {
    TypedModelUnique();
  }

  function I(v: Variables) : LinkedJournal.Variables
    requires Inv(v)
  {
    TheTypedModel(v)
  }
  
  lemma RefinementInit(v: Variables, journalImage: JournalImage)
    requires Init(v, journalImage)
    ensures Inv(v)
    ensures LinkedJournal.Init(I(v), journalImage.I())
  {
    TypedModelUnique();
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures LinkedJournal.Next(I(v), I(v'), lbl.I())
  {
    var t := TheTypedModel(v);
    var t' := TheTypedModel(v');
    TypedModelUnique();
    LinkedJournalRefinement.InvNext(t, t', lbl.I());
    LinkedJournalRefinement.NextRefines(t, t', lbl.I());
  }
}
