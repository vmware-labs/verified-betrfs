// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BlockCrashTolerantMap.i.dfy"
include "../CoordinationLayer/CrashTolerantMap.i.dfy"
include "../Betree/PagedBetreeRefinement.i.dfy"
include "../Betree/PivotBetreeRefinement.i.dfy"
include "../Betree/LinkedBetreeRefinement.i.dfy"
include "../Betree/MarshalledBetreeRefinement.i.dfy"

module BlockCrashTolerantMapRefinement {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened StampedMod
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Buffers
  import CrashTolerantMap 
  import opened BlockCrashTolerantMap 
  import PagedBetreeRefinement
  import PivotBetreeRefinement
  import LinkedBetreeRefinement
  import MarshalledBetreeRefinement
  import AbstractMap

  predicate DecodableImage(store: StoreImage)
  {
    && store.WF()
    && store.I().value.diskView.Acyclic() // TODO(jonh): introduce "Decodable" into LinkedBetree/Refinement
  }

  function IImage(store: StoreImage) : CrashTolerantMap.StoreImage
    requires DecodableImage(store)
  {
    PagedBetreeRefinement.IStampedBetree(
      PivotBetreeRefinement.IStampedBetree(
        LinkedBetreeRefinement.IStampedBetree(
          store.I())))
  }

  function IMB(mv: MarshalledBetreeMod.Variables) : AbstractMap.Variables
    requires mv.WF()
    requires MarshalledBetreeRefinement.Inv(mv)
  {
    PagedBetreeRefinement.I(
      PivotBetreeRefinement.I(
        LinkedBetreeRefinement.I(
          MarshalledBetreeRefinement.I(
            mv))))
  }

  predicate Decodable(v: Variables)
  {
    && DecodableImage(v.persistent)
    && (v.ephemeral.Known? ==> MarshalledBetreeRefinement.Inv(v.ephemeral.v))
    && (v.inFlight.Some? ==> DecodableImage(v.inFlight.value))
  }

  function I(v: Variables) : CrashTolerantMap.Variables
    requires Decodable(v)
  {
    CrashTolerantMap.Variables(
      IImage(v.persistent),
      if v.ephemeral.Unknown?
      then CrashTolerantMap.Unknown
      else CrashTolerantMap.Known(
        IMB(v.ephemeral.v)
      ),
      if v.inFlight.None? then None else Some(IImage(v.inFlight.value))
    )
  }

  predicate Inv(v: Variables)
  {
    && Decodable(v)
  }

  function IALabel(lbl: TransitionLabel) : CrashTolerantMap.TransitionLabel
    requires lbl.WF()
  {
    lbl.base
  }

  predicate DecodableStep(step: Step)
  {
    step.FreezeMapInternalStep? ==> DecodableImage(step.frozenMap)
  }

  function IStep(step: Step) : CrashTolerantMap.Step
  {
    if !DecodableStep(step) then CrashTolerantMap.CrashStep() else
    match step
      case LoadEphemeralFromPersistentStep() => CrashTolerantMap.LoadEphemeralFromPersistentStep()
      case PutRecordsStep() => CrashTolerantMap.PutRecordsStep()
      case QueryStep() => CrashTolerantMap.QueryStep()
      case FreezeMapInternalStep(frozenMap) => CrashTolerantMap.FreezeMapInternalStep(IImage(frozenMap))
      case EphemeralInternalStep() => CrashTolerantMap.EphemeralInternalStep()
      case CommitStartStep() => CrashTolerantMap.CommitStartStep()
      case CommitCompleteStep() => CrashTolerantMap.CommitCompleteStep()
      case CrashStep() => CrashTolerantMap.CrashStep()
  }

  lemma LoadEphemeralFromPersistentRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.LoadEphemeralFromPersistentLabel?
    ensures Inv(v') && CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), CrashTolerantMap.LoadEphemeralFromPersistentStep())
  {
    MarshalledBetreeRefinement.RefinementInit(v'.ephemeral.v, v.persistent);
    PagedBetreeRefinement.InitRefines(
      PivotBetreeRefinement.I(LinkedBetreeRefinement.I(MarshalledBetreeRefinement.I(v'.ephemeral.v))),
      PivotBetreeRefinement.IStampedBetree(LinkedBetreeRefinement.IStampedBetree(v.persistent.I())));
  }

  // Maybe this belongs in MarshalledBetree specifically?
  predicate DecodableMBLabel(lbl: MarshalledBetreeMod.TransitionLabel) {
    && lbl.WF()
    //&& lbl.I().WF()
  }
  function IAMBLabel(lbl: MarshalledBetreeMod.TransitionLabel) : AbstractMap.TransitionLabel
    requires DecodableMBLabel(lbl)
  {
    PagedBetreeRefinement.ILbl(PivotBetreeRefinement.ILbl(LinkedBetreeRefinement.ILbl(lbl.I())))
  }

  lemma BetreeChainedNext(j: MarshalledBetreeMod.Variables, j': MarshalledBetreeMod.Variables, lbl: MarshalledBetreeMod.TransitionLabel)
    requires MarshalledBetreeRefinement.Inv(j)
    requires MarshalledBetreeMod.Next(j, j', lbl)
    ensures MarshalledBetreeRefinement.Inv(j')
    ensures AbstractMap.Next(IMB(j), IMB(j'), IAMBLabel(lbl))
  {
    MarshalledBetreeRefinement.RefinementNext(j, j', lbl);
    // TODO(jonh): inconsistent theorem naming: RefinementNext vs NextRefines
    LinkedBetreeRefinement.NextRefines(
      MarshalledBetreeRefinement.I(j),
      MarshalledBetreeRefinement.I(j'),
      lbl.I());
    PivotBetreeRefinement.NextRefines(
      LinkedBetreeRefinement.I(MarshalledBetreeRefinement.I(j)),
      LinkedBetreeRefinement.I(MarshalledBetreeRefinement.I(j')),
      LinkedBetreeRefinement.ILbl(lbl.I()));
    PagedBetreeRefinement.NextRefines(
      PivotBetreeRefinement.I(LinkedBetreeRefinement.I(MarshalledBetreeRefinement.I(j))),
      PivotBetreeRefinement.I(LinkedBetreeRefinement.I(MarshalledBetreeRefinement.I(j'))),
      PivotBetreeRefinement.ILbl(LinkedBetreeRefinement.ILbl(lbl.I())));
  }

  lemma PutRecordsRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Inv(v) && Next(v, v', lbl) && lbl.base.PutRecordsLabel?
    ensures Inv(v') && CrashTolerantMap.Next(I(v), I(v'), IALabel(lbl))
  {
    BetreeChainedNext(v.ephemeral.v, v'.ephemeral.v, MarshalledBetreeMod.PutLabel(lbl.base.records));
  }


  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires Inv(v)
    ensures Inv(v')
    ensures CrashTolerantMap.Next(I(v), I(v'), IALabel(lbl))
  {
    var step :| NextStep(v, v', lbl, step);
    match step {
      case LoadEphemeralFromPersistentStep() => {
        LoadEphemeralFromPersistentRefines(v, v', lbl);
        assert CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case PutRecordsStep() => {
        assume Inv(v');
        assume CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case QueryStep() => {
        assert Inv(v');
        assume CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case FreezeMapInternalStep(frozenMap) => {
        assume Inv(v');
        assume CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case EphemeralInternalStep() => {
        assume Inv(v');
        assume CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case CommitStartStep() => {
        assert Inv(v');
        assert CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case CommitCompleteStep() => {
        assert Inv(v');
        assert CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
      case CrashStep() => {
        assert Inv(v');
        assert CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
      }
    }
//    assert Inv(v') by {
//        if step.LoadEphemeralFromPersistentStep? { LoadEphemeralFromPersistentRefines(v, v', lbl); }
//        if step.PutRecordsStep? { assert Inv(v'); }
//        if step.QueryStep? { assert Inv(v'); }
//        if step.FreezeMapInternalStep? { assert Inv(v'); }
//        if step.EphemeralInternalStep? { assert Inv(v'); }
//        if step.CommitStartStep? { assert Inv(v'); }
//        if step.CommitCompleteStep? { assert Inv(v'); }
//        if step.CrashStep? { assert Inv(v'); }
//    }
  }
}
