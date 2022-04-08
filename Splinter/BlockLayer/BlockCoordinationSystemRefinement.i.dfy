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

  predicate DecodableJournalLabel(journalLabel: MarshalledJournal.TransitionLabel)
  {
    && journalLabel.WF()
    && journalLabel.I().WF()
  }

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
    // TODO(jonh,robj): Reaching into journal's journalImage is a bit layer-violation-y.
    // Maybe it's okay for the proof?
    && (v.ephemeral.Known? ==>
        v.persistentImage.journal.diskView.IsSubDisk(v.ephemeral.journal.journalImage.diskView)
      )
      // persistent disk journal repr is always a subset of the ephemeral journal repr
//      && v.persistentImage.journal.diskView.entries.Keys <= v.ephemeral.journal.journalImage.diskView.entries.Keys
//      && v.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v.persistentImage.journal.diskView))
    && (v.inFlightImage.Some? ==>
      && v.ephemeral.Known?
      && LinkedJournalRefinement.InFlightSubDiskProperty(
          MarshalledJournalRefinement.I(v.ephemeral.journal), v.inFlightImage.value.journal.I())
      )
      
      //v.inFlightImage.value.journal.diskView.AgreesWithDisk(v.persistentImage.journal.diskView))
//    && (v.ephemeral.Known? && v.inFlightImage.Some? ==>
//      v.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v.inFlightImage.value.journal.diskView))
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

  function IAJournalLabel(lbl: MarshalledJournal.TransitionLabel) : AbstractJournal.TransitionLabel
    requires DecodableJournalLabel(lbl)
  {
    PagedJournalRefinement.ILbl(lbl.I().I())
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

    // Interestingly, the IsSubDisk invariants are trivial here. ephemeral and
    // inFlightImage are trivial because they're just empty. And the persistentImage
    // starts out as a journal whose diskView is empty, which is a subdisk of every
    // other disk.
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
      case DeliverReplyStep() => CoordinationSystem.DeliverReplyStep()
      case JournalInternalStep() => CoordinationSystem.JournalInternalStep()
      case MapInternalStep() => CoordinationSystem.MapInternalStep()
      case ReqSyncStep() => CoordinationSystem.ReqSyncStep()
      case ReplySyncStep() => CoordinationSystem.ReplySyncStep()
      case FreezeMapAdtStep() => CoordinationSystem.FreezeMapAdtStep()
      case CommitStartStep(frozenJournal) => CoordinationSystem.CommitStartStep(IAJournalImage(frozenJournal))
      case CommitCompleteStep() => CoordinationSystem.CommitCompleteStep()
      case CrashStep() => CoordinationSystem.CrashStep()
  }

  lemma LoadEphemeralFromPersistentNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.LoadEphemeralFromPersistentStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
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

  // TODO(jonh): this would go in the opaqued journal kit, or at least MarshalledJournalRefinement
  lemma JournalChainedNext(j: MarshalledJournal.Variables, j': MarshalledJournal.Variables, lbl: MarshalledJournal.TransitionLabel)
    requires MarshalledJournalRefinement.Inv(j)
    requires MarshalledJournal.Next(j, j', lbl)
    ensures MarshalledJournalRefinement.Inv(j')
    ensures AbstractJournal.Next(IAJournal(j), IAJournal(j'), IAJournalLabel(lbl))
  {
    MarshalledJournalRefinement.RefinementNext(j, j', lbl);
    // TODO(jonh): inconsistent theorem naming: RefinementNext vs NextRefines
    LinkedJournalRefinement.NextRefines(
      MarshalledJournalRefinement.I(j),
      MarshalledJournalRefinement.I(j'),
      lbl.I());
    PagedJournalRefinement.NextRefines(
      LinkedJournalRefinement.I(MarshalledJournalRefinement.I(j)),
      LinkedJournalRefinement.I(MarshalledJournalRefinement.I(j')),
      lbl.I().I());
  }

  lemma RecoverNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.RecoverStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    JournalChainedNext(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.ReadForRecoveryLabel(step.puts));
    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step)); // trigger
  }

  lemma PutNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.PutStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    var key := uiop.baseOp.req.input.key;
    var val := uiop.baseOp.req.input.value;
    var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.PutLabel(singleton));
    if v'.inFlightImage.Some? {
      assert v'.inFlightImage.value.journal.diskView.AgreesWithDisk(v'.persistentImage.journal.diskView);
    }
    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step)); // trigger?
  }

  lemma JournalInternalNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.JournalInternalStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    JournalChainedNext(v.ephemeral.journal, v'.ephemeral.journal,
      MarshalledJournal.InternalLabel());

    var lbl := MarshalledJournal.InternalLabel();
    var t, t' :|
      && MarshalledJournal.TypeProvidesModel(v.ephemeral.journal, t)
      && MarshalledJournal.TypeProvidesModel(v'.ephemeral.journal, t')
      && LinkedJournal.Next(t, t', lbl.I());
    var lstep :| LinkedJournal.NextStep(t, t', lbl.I(), lstep);
    assume lstep.addr !in v'.persistentImage.journal.diskView.entries;
//    assert v'.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v'.persistentImage.journal.diskView);
      
    if v'.inFlightImage.Some? {
      assume lstep.addr !in v.inFlightImage.value.journal.diskView.entries;
//      assert v'.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v'.inFlightImage.value.journal.diskView);
      MarshalledJournalRefinement.RefinementNext(v.ephemeral.journal, v'.ephemeral.journal, MarshalledJournal.InternalLabel());  // hoist one layer to LinkedJournal. (JournalChainedNext hides this jump)

      // saw an out-of-resource here, but can't repro
      // with assert false: 20s success
      // with neither, no proc: success argh.
      // with neither, proc: 17s success
      // with InFlightSubDiskPreserved: 15s success
      LinkedJournalRefinement.InFlightSubDiskPreserved(
        MarshalledJournalRefinement.I(v.ephemeral.journal),
        MarshalledJournalRefinement.I(v'.ephemeral.journal),
        v.inFlightImage.value.journal.I());

    }
    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step)); // trigger?
  }

  lemma CommitStartNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.CommitStartStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    JournalChainedNext(v.ephemeral.journal, v'.ephemeral.journal,
      MarshalledJournal.FreezeForCommitLabel(step.frozenJournal));
//    assert v'.inFlightImage.value.journal.diskView.AgreesWithDisk(v'.persistentImage.journal.diskView);
//    assume step.frozenJournal.diskView.AgreesWithDisk(v'.ephemeral.journal.journalImage.diskView);
//    assert v'.persistentImage.journal.diskView.entries.Keys <= v'.ephemeral.journal.journalImage.diskView.entries.Keys;
//    assert step.frozenJournal.diskView.AgreesWithDisk(v'.persistentImage.journal.diskView);
//    assert v'.inFlightImage.value.journal == step.frozenJournal;

    var mjlbl := MarshalledJournal.FreezeForCommitLabel(step.frozenJournal);
    MarshalledJournalRefinement.RefinementNext(v.ephemeral.journal, v'.ephemeral.journal, mjlbl);  // hoist one layer to LinkedJournal. (JournalChainedNext hides this jump)
//    LinkedJournalRefinement.InFlightSubDiskCreated(
//      MarshalledJournalRefinement.I(v.ephemeral.journal),
//      MarshalledJournalRefinement.I(v'.ephemeral.journal),
//      mjlbl.I());

    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step)); // trigger
  }

  lemma CommitCompleteNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.CommitCompleteStep?
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    JournalChainedNext(v.ephemeral.journal, v'.ephemeral.journal,
      MarshalledJournal.DiscardOldLabel(v.inFlightImage.value.mapadt.seqEnd, v.ephemeral.mapLsn));
//    if v'.ephemeral.Known? {
//      assert v'.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v.ephemeral.journal.journalImage.diskView);
//      assert v.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v.inFlightImage.value.journal.diskView);
//      assert v'.ephemeral.journal.journalImage.diskView.AgreesWithDisk(v'.persistentImage.journal.diskView);
//    }
    assert v'.persistentImage == v.inFlightImage.value; // step
    assert v.inFlightImage.value.journal.diskView.IsSubDisk(
      v.ephemeral.journal.journalImage.DiscardOld(v.inFlightImage.value.SeqStart()).diskView); // inv
    assert v.inFlightImage.value == v'.persistentImage;
    assert v'.ephemeral.journal.journalImage.diskView == v.ephemeral.journal.journalImage.DiscardOld(v.inFlightImage.value.SeqStart()).diskView;
    assert v'.persistentImage.journal.diskView.IsSubDisk(v'.ephemeral.journal.journalImage.diskView);
    assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step)); // trigger
  }

  // TODO(jonh, robj): Things get pretty timey-outey here. Proposed solution is
  // that the journal stack, at this point, should be basically opaque, with
  // only its interpretation properties exposed.
  // TODO(utaal): This opacification is probably a good test for the opaque rules in Verus!
  // TODO(jonh): Once that's fixed, we could surely pull the prooflets above
  // back into their respective cases down here.
  lemma {:timeLimitMultiplier 3} RefinementNext(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures CoordinationSystem.Next(I(v), I(v'), uiop)
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => {
        LoadEphemeralFromPersistentNext(v, v', uiop, step);
      }
      case RecoverStep(puts) => {
        RecoverNext(v, v', uiop, step);
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
        PutNext(v, v', uiop, step);
      }
      case JournalInternalStep() => {
        JournalInternalNext(v, v', uiop, step);
      }
      case MapInternalStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
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
      case CommitStartStep(frozenJournal) => {
        CommitStartNext(v, v', uiop, step);
      }
      case CommitCompleteStep() => {
        CommitCompleteNext(v, v', uiop, step);
      }
      case CrashStep() => {
        assert Inv(v'); // case boilerplate
        assert CoordinationSystem.NextStep(I(v), I(v'), uiop, IStep(step));
      }
    }
  }
}
