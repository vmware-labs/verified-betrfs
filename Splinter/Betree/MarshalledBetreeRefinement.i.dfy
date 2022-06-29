// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "LinkedBetreeRefinement.i.dfy"
include "MarshalledBetree.i.dfy"

module MarshalledBetreeRefinement
// TODO refines RefinementObligation(BetreeLabels, PagedBetree)
{
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import LinkedBetreeMod
  import LinkedBetreeRefinement
  import opened MarshalledBetreeMod
  import opened GenericDisk

  predicate HasTypedModel(v: Variables)
  {
    exists typed :: TypeProvidesModel(v, typed)
  }

  function TheTypedModel(v: Variables) : LinkedBetreeMod.Variables
    requires HasTypedModel(v)
  {
    // todo(jonh): this is same as I()
    var typed :| TypeProvidesModel(v, typed); typed
  }

  lemma TypedModelUnique()
    ensures forall v: BetreeImage, t1, t2 | v.TypeProvidesModel(t1) && v.TypeProvidesModel(t2) :: t1 == t2
  {
    forall v: BetreeImage, t1, t2 | v.TypeProvidesModel(t1) && v.TypeProvidesModel(t2)
      ensures t1 == t2
    {
      var e1 := t1.value.diskView.entries;
      var e2 := t2.value.diskView.entries;
      forall addr ensures addr in e1 <==> addr in e2 {
        assert addr in MarshalDisk(t2.value.diskView.entries).entries || true;  // trigger
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
      assert t1.value == t2.value;   // trigger extensionality
    }
  }

  predicate InvImage(journalImage: BetreeImage)
  {
    && journalImage.HasModel()
    && LinkedBetreeRefinement.InvLinkedBetree(journalImage.I().value)
  }

  predicate Inv(v: Variables) {
    && HasTypedModel(v)
    && LinkedBetreeRefinement.Inv(TheTypedModel(v))
  }

  lemma InvInit(v: Variables, journalImage: BetreeImage)
    requires Init(v, journalImage)
    requires InvImage(journalImage)
    ensures Inv(v)
  {
    TypedModelUnique();
  }

  function I(v: Variables) : LinkedBetreeMod.Variables
    requires Inv(v)
  {
    TheTypedModel(v)
  }
  
  lemma RefinementInit(v: Variables, journalImage: BetreeImage)
    requires Init(v, journalImage)
    ensures Inv(v)
    ensures LinkedBetreeMod.Init(I(v), journalImage.I())
  {
    TypedModelUnique();
  }

  lemma RefinementNext(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v)
    requires Next(v, v', lbl)
    ensures Inv(v')
    ensures LinkedBetreeMod.Next(I(v), I(v'), lbl.I())
  {
    var t := TheTypedModel(v);
    var t' := TheTypedModel(v');
    TypedModelUnique();
    LinkedBetreeRefinement.InvNext(t, t', lbl.I());
    LinkedBetreeRefinement.NextRefines(t, t', lbl.I());
  }

  // Used by BlockCrashTolerantMapRefinement to cart Acyclicity from Inv(v) to frozen image
  lemma IVarsIsIImage(v: Variables)
    requires Inv(v)
    ensures I(v).linked == v.betreeImage.I().value
  {
    TypedModelUnique();
  }

  lemma EmptyRefines()
    ensures EmptyBetreeImage().WF()
    ensures EmptyBetreeImage().I() == LinkedBetreeMod.EmptyImage()
  {
    assert EmptyBetreeImage().TypeProvidesModel(LinkedBetreeMod.EmptyImage());  // witness
    TypedModelUnique();
  }
}
