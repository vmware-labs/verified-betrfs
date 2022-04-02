// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../Spec/MapSpec.s.dfy"
include "../CoordinationLayer/CoordinationSystem.i.dfy"
include "../Journal/MarshalledJournalRefinement.i.dfy"
include "BlockCoordinationSystem.i.dfy"

module BlockCoordinationSystemRefinement
{
  import opened Options
  import CoordinationSystem
  import opened MsgHistoryMod
  import opened ValueMessage
  import opened BlockCoordinationSystem
  import AbstractJournal
  import PagedJournalRefinement
  import LinkedJournal
  import LinkedJournalRefinement
  import MarshalledJournalRefinement

  // Decodable is a pretty cheap almost-type property, but not one we can
  // trivially check, either with a typecheck in the implementation or a cheap
  // runtime check, so we don't want to call it WF and risk it ending up in a
  // v' where it'll be hard to prove later. Instead, we define it here and
  // prove it as part of Inv.
  predicate DecodableJournalImage(journalImage: MarshalledJournal.JournalImage)
  {
    && journalImage.WF()
    && journalImage.I().Decodable()
  }

  predicate DecodableDiskImage(diskImage: DiskImage)
  {
    && DecodableJournalImage(diskImage.journal)
  }

  predicate DecodableEphemeral(ephemeral: Ephemeral)
  {
    ephemeral.Known? ==> MarshalledJournalRefinement.Inv(ephemeral.journal)
  }

  predicate DecodableVariables(v: Variables)
  {
    && DecodableDiskImage(v.persistentImage)
    && DecodableEphemeral(v.ephemeral)
    && (v.inFlightImage.Some? ==> DecodableDiskImage(v.inFlightImage.value))
  }

  predicate DecodableStep(step: Step)
  {
    step.CommitStartStep? ==> DecodableJournalImage(step.frozenJournal)
  }

  //////////////////////////////////////////////////////////////////////
  // Inv

  predicate Inv(v: Variables) {
    && DecodableVariables(v)
  }

  // IA Interpret to Abstraction: peel all the way up the stack.
  function IAJournalImage(journalImage: MarshalledJournal.JournalImage) : MsgHistory
    requires DecodableJournalImage(journalImage)
  {
    journalImage.I().I().I()
  }

  function IAJournal(journal: MarshalledJournal.Variables) : AbstractJournal.Variables
    requires MarshalledJournalRefinement.Inv(journal)
  {
    PagedJournalRefinement.I(LinkedJournalRefinement.I(MarshalledJournalRefinement.I(journal)))
  }

  // Interpret BlockCoordinationSystem types
  function IDiskImage(diskImage: DiskImage) : CoordinationSystem.DiskImage
    requires DecodableDiskImage(diskImage)
  {
    CoordinationSystem.DiskImage(diskImage.mapadt, IAJournalImage(diskImage.journal))
  }

  function IEphemeral(ephemeral: Ephemeral) : CoordinationSystem.Ephemeral
    requires DecodableEphemeral(ephemeral)
  {
    if ephemeral.Unknown? then CoordinationSystem.Unknown
    else CoordinationSystem.Known(
      ephemeral.progress,
      ephemeral.syncReqs,
      ephemeral.mapadt,
      ephemeral.mapLsn,
      IAJournal(ephemeral.journal),
      ephemeral.frozenMap
    )
  }

  function I(v: Variables) : CoordinationSystem.Variables
    requires DecodableVariables(v)
  {
    CoordinationSystem.Variables(
      IDiskImage(v.persistentImage),
      IEphemeral(v.ephemeral),
      if v.inFlightImage.None? then None else Some(IDiskImage(v.inFlightImage.value))
    )
  }
  
  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures Inv(v)
    ensures CoordinationSystem.Init(I(v))
  {
    MarshalledJournalRefinement.MkfsRefines();
    assert MarshalledJournal.Mkfs().WF();
    assert DecodableDiskImage(v.persistentImage);
    assert DecodableVariables(v);
  }

  function IStep(step: Step) : CoordinationSystem.Step
    requires DecodableStep(step)
  {
    match step
      case LoadEphemeralFromPersistentStep() => CoordinationSystem.LoadEphemeralFromPersistentStep
      case RecoverStep(puts) => CoordinationSystem.RecoverStep(puts)
      case AcceptRequestStep() => CoordinationSystem.AcceptRequestStep()
      case QueryStep() => CoordinationSystem.QueryStep()
      case PutStep() => CoordinationSystem.PutStep()
      case DeliverReplyStep() => CoordinationSystem.DeliverReplyStep
//    case | JournalInternalStep() => CoordinationSystem.JournalInternalStep()
//    case | SplinterTreeInternalStep() => CoordinationSystem.SplinterTreeInternalStep()
      case ReqSyncStep() => CoordinationSystem.ReqSyncStep
      case ReplySyncStep() => CoordinationSystem.ReplySyncStep
      case FreezeMapAdtStep() => CoordinationSystem.FreezeMapAdtStep
      case CommitStartStep(seqBoundary, frozenJournal) => CoordinationSystem.CommitStartStep(IAJournalImage(frozenJournal))
      case CommitCompleteStep() => CoordinationSystem.CommitCompleteStep()
      case CrashStep() => CoordinationSystem.CrashStep()
  }

  lemma RefinementNext(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => {
        MarshalledJournalRefinement.InvInit(v'.ephemeral.journal, v.persistentImage.journal);
        assert Inv(v'); // case boilerplate

        var j := v.persistentImage.journal;
        var j' := v'.ephemeral.journal;

        assert MarshalledJournal.Init(j', j);
        MarshalledJournalRefinement.RefinementInit(j', j);
        assert LinkedJournal.Init(MarshalledJournalRefinement.I(j'), j.I());
        

        assert I(v').ephemeral.journal.journal == I(v).persistentImage.journal;
        assert AbstractJournal.Init(I(v').ephemeral.journal, I(v).persistentImage.journal);
        assert CoordinationSystem.LoadEphemeralFromPersistent(I(v), I(v'), uiop);
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case RecoverStep(puts) => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case AcceptRequestStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case QueryStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case PutStep() => {
        var key := uiop.baseOp.req.input.key;
        var val := uiop.baseOp.req.input.value;
        var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));
        MarshalledJournalRefinement.RefinementNext(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.PutLabel(singleton));
      
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
//      case JournalInternalStep(sk) => {
//}
//      case SplinterTreeInternalStep(sk) => {
//}
      case DeliverReplyStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case ReqSyncStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case ReplySyncStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case FreezeMapAdtStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case CommitStartStep(seqBoundary, frozenJournal) => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case CommitCompleteStep() => {
        MarshalledJournalRefinement.RefinementNext(v.ephemeral.journal, v'.ephemeral.journal,
          MarshalledJournal.DiscardOldLabel(v.inFlightImage.value.mapadt.seqEnd, v.ephemeral.mapLsn));
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
      case CrashStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
    }
  }
}
