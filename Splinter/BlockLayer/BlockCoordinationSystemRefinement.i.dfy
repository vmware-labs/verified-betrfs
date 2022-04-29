// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/CoordinationSystemRefinement.i.dfy"
include "../Journal/MarshalledJournalRefinement.i.dfy"
include "BlockCoordinationSystem.i.dfy"
include "BlockCrashTolerantJournalRefinement.i.dfy"
include "BlockCrashTolerantMapRefinement.i.dfy"

module BlockCoordinationSystemRefinement
{
  import opened Options
  import CoordinationSystem
  import CoordinationSystemRefinement
  import opened MsgHistoryMod
  import opened ValueMessage
  import opened BlockCoordinationSystem
  import AbstractJournal
  import PagedJournalRefinement
  import LinkedJournal
  import LinkedJournalRefinement
  import MarshalledJournal  // TODO(jonh): move this stuff into BlockCrashTolerantJournalRefinement or something?
  import MarshalledJournalRefinement
  import CrashTolerantMap
  import CrashTolerantJournal
  import BlockCrashTolerantJournalRefinement
  import BlockCrashTolerantMapRefinement

  // Decodable is a pretty cheap almost-type property, but not one we can
  // trivially check, either with a typecheck in the implementation or a cheap
  // runtime check, so we don't want to call it WF and risk it ending up in a
  // v' where it'll be hard to prove later. Instead, we define it here and
  // prove it as part of Inv.

  predicate DecodableMap(jv: BlockCrashTolerantMap.Variables)
  {
    true
  }

  predicate DecodableVariables(v: Variables)
  {
    && BlockCrashTolerantJournalRefinement.Decodable(v.journal)
    && DecodableMap(v.mapadt)
  }

  //////////////////////////////////////////////////////////////////////
  // Inv

  function SuperblockRepr() : set<Address>
  {
    // Could store the superblock in two places.
    // Um, addresses aren't concrete yet.
    { 0, 1 }
  }

  predicate Framing(v: Variables)
    requires v.WF()
  {
    // This theorem doesn't get interesting until there's something interesting
    // happening in more than one place!
    && v.journal.Repr() !! v.mapadt.Repr()
    && v.journal.Repr() !! SuperblockRepr()
    && v.mapadt.Repr() !! SuperblockRepr()
  }

  predicate Inv(v: Variables) {
    && v.WF()
    && DecodableVariables(v)
    && BlockCrashTolerantJournalRefinement.Inv(v.journal)
    && BlockCrashTolerantMapRefinement.Inv(v.mapadt)

    // This layer's version of CoordinationSystemRefinement.InvInFlightGeometry
    && (v.journal.inFlight.Some? ==> 
        v.journal.inFlight.value.I().SeqStart() == v.mapadt.inFlight.value.seqEnd
      )
  }

  function IEphemeral(ephemeral: Ephemeral) : CoordinationSystem.Ephemeral
    requires true //DecodableEphemeral(ephemeral)
  {
    if ephemeral.Unknown? then CoordinationSystem.Unknown
    else CoordinationSystem.Known(
      ephemeral.progress,
      ephemeral.syncReqs,
      ephemeral.mapLsn
    )
  }

  function I(v: Variables) : CoordinationSystem.Variables
    requires DecodableVariables(v)
  {
    CoordinationSystem.Variables(
      BlockCrashTolerantJournalRefinement.I(v.journal),
      BlockCrashTolerantMapRefinement.I(v.mapadt),
      IEphemeral(v.ephemeral)
    )
  }
  
  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures CoordinationSystem.Init(I(v))
  {
    BlockCrashTolerantJournalRefinement.InitRefines(v.journal);
  }

  function IStep(step: Step) : CoordinationSystem.Step
  {
    step
  }

  predicate NextCondition(v: Variables, v': Variables, uiop: UIOp, step: Step)
  {
    && Inv(v)
    && Next(v, v', uiop)
    && NextStep(v, v', uiop, step)
  }


  lemma LoadEphemeralFromPersistentNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step)
    requires step.LoadEphemeralFromPersistentStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.LoadEphemeralFromPersistentLabel()));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn));
  }

  lemma RecoverNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.RecoverStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.ReadForRecoveryLabel(step.records)));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.PutRecordsLabel(step.records));
  }

  lemma AcceptRequestNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.AcceptRequestStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
  }

  lemma QueryNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.QueryStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.QueryEndLsnLabel(v.ephemeral.mapLsn)));
    var key := uiop.baseOp.req.input.key;
    var value := uiop.baseOp.reply.output.value;
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.QueryLabel(v.ephemeral.mapLsn, key, value));
  }

  lemma PutNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.PutStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    var key := uiop.baseOp.req.input.key;
    var val := uiop.baseOp.req.input.value;
    var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.PutLabel(singleton)));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.PutRecordsLabel(singleton));
  }

  lemma JournalInternalNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.JournalInternalStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.InternalLabel()));
  }

  lemma MapInternalNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.MapInternalStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.InternalLabel());
  }

  lemma DeliverReplyNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.DeliverReplyStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
  }

  lemma ReqSyncNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.ReqSyncStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
  }

  lemma ReplySyncNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.ReplySyncStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
  }

  lemma CommitStartNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.CommitStartStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.CommitStartLabel(step.newBoundaryLsn, v.ephemeral.mapLsn)));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.CommitStartLabel(step.newBoundaryLsn));
  }

  lemma CommitCompleteNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.CommitCompleteStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.CommitCompleteLabel(v.ephemeral.mapLsn)));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.CommitCompleteLabel());
  }

  lemma CrashNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires NextCondition(v, v', uiop, step) && step.CrashStep?
    ensures Inv(v') && CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step))
  {
    BlockCrashTolerantJournalRefinement.NextRefines(v.journal, v'.journal, SimpleLabel(CrashTolerantJournal.CrashLabel()));
    BlockCrashTolerantMapRefinement.NextRefines(v.mapadt, v'.mapadt, CrashTolerantMap.CrashLabel());
    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, CoordinationSystem.CrashStep());
  }

  // TODO(jonh, robj): Things get pretty timey-outey here. Proposed solution is
  // that the map & journal stacks, at this point, should be basically opaque, with
  // only its interpretation properties exposed.
  // TODO(utaal): This opacification is probably a good test for the opaque rules in Verus!
  // TODO(jonh): Once that's fixed, we could surely pull the prooflets above
  // back into their respective cases down here.
  lemma RefinementNext(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => { LoadEphemeralFromPersistentNext(v, v', uiop, step); }
      case RecoverStep(_) => { RecoverNext(v, v', uiop, step); }
      case AcceptRequestStep() => { AcceptRequestNext(v, v', uiop, step); }
      case QueryStep() => { QueryNext(v, v', uiop, step); }
      case PutStep() => { PutNext(v, v', uiop, step); }
      case JournalInternalStep() => { JournalInternalNext(v, v', uiop, step); }
      case MapInternalStep() => { MapInternalNext(v, v', uiop, step); }
      case DeliverReplyStep() => { DeliverReplyNext(v, v', uiop, step); }
      case ReqSyncStep() => { ReqSyncNext(v, v', uiop, step); }
      case ReplySyncStep() => { ReplySyncNext(v, v', uiop, step); }
      case CommitStartStep(_) => { CommitStartNext(v, v', uiop, step); }
      case CommitCompleteStep() => { CommitCompleteNext(v, v', uiop, step); }
      case CrashStep() => { CrashNext(v, v', uiop, step); }
    }
  }
}
