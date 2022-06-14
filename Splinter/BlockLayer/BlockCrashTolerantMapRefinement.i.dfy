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

  predicate Decodable(v: Variables)
  {
    true
  }

  function IMB(mv: MarshalledBetreeMod.Variables) : AbstractMap.Variables
  {
    PagedBetreeRefinement.I(
      PivotBetreeRefinement.I(
        LinkedBetreeRefinement.I(
          MarshalledBetreeRefinement.I(
            mv))))
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
    lbl
  }

  function IStep(step: Step) : CrashTolerantMap.Step
  {
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

  lemma NextRefines(v: Variables, v': Variables, lbl: TransitionLabel)
    requires Next(v, v', lbl)
    requires Inv(v)
    ensures Inv(v')
    ensures CrashTolerantMap.Next(I(v), I(v'), IALabel(lbl))
  {
    var step :| NextStep(v, v', lbl, step);
    assert CrashTolerantMap.NextStep(I(v), I(v'), IALabel(lbl), IStep(step));
  }
}
