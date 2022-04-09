// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CoordinationSystem.i.dfy"

// This module shows refinement of CoordinatorMod to
// CrashTolerantMapSpecMod, thereby functioning as the top layer in a
// refinement stack for program models in refinement layers below.

// TODO(jonh): satisfy a refinement-module proof obligation!
module CoordinationSystemRefinement {
  import opened SequencesLite // Last, DropLast
  import opened CM = CoordinationSystem
  import opened StampedMapMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
  import opened TotalKMMapMod
  import opened LSNMod
  import MapSpecMod

  function IEJ(ej: AbstractJournal.Variables) : (out:MsgHistory)
    requires ej.WF()
    ensures out.WF()
  { ej.journal }

  function IMap(mapp: AbstractMap.Variables) : (out:StampedMap)
  {
    mapp.stampedMap
  }

  import Async = CM.Async
  type Journal = MsgHistory

  function EphemeralSeqEnd(ephemeral: Ephemeral) : LSN
    requires ephemeral.WF() && ephemeral.Known?
  {
    IEJ(ephemeral.journal).seqEnd
  }

  function StampedMapToVersion(sm: StampedMapMod.StampedMap) : CrashTolerantMapSpecMod.Version
  {
    CrashTolerantMapSpecMod.Version(Async.PersistentState(MapSpecMod.Variables(sm.mi)))
  }

  function VersionsWithForgottenPrefix(base: StampedMapMod.StampedMap, msgHistory: MsgHistory, stableLSN: LSN) : (versions:seq<CrashTolerantMapSpecMod.Version>)
    requires msgHistory.WF()
    requires msgHistory.CanFollow(base.seqEnd)
    requires msgHistory.CanDiscardTo(stableLSN)
    ensures |versions| == msgHistory.seqEnd+1
  {
    // Construct a Version seq with the entries before stableLSN Forgotten: that's what spec expects.
    var numVersions := msgHistory.seqEnd + 1;
    seq(numVersions, lsn requires 0<=lsn<numVersions =>
      if lsn < stableLSN
      then CrashTolerantMapSpecMod.Forgotten
      else StampedMapToVersion(MapPlusHistory(base, msgHistory.DiscardRecent(lsn))))
  }

  function Ic() : CrashTolerantMapSpecMod.Constants
  {
    CrashTolerantMapSpecMod.Constants()
  }

  function I(v: Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()  // silly-handler
    else
      var stableLSN := v.persistentImage.SeqEnd();
      if v.ephemeral.Known?
      then CrashTolerantMapSpecMod.Variables(
        VersionsWithForgottenPrefix(v.persistentImage.mapadt, IEJ(v.ephemeral.journal), stableLSN),
          v.ephemeral.progress, v.ephemeral.syncReqs, stableLSN)
      else CrashTolerantMapSpecMod.Variables(
        VersionsWithForgottenPrefix(v.persistentImage.mapadt, v.persistentImage.journal, stableLSN),
          Async.InitEphemeralState(), map[], stableLSN)
  }

  // Where these journals share an LSN, they map it to the same message.
  predicate {:opaque} JournalOverlapsAgree(j0: Journal, j1: Journal)
    requires j0.WF() && j1.WF()
  {
    forall lsn | j0.Contains(lsn) && j1.Contains(lsn) :: j0.msgs[lsn] == j1.msgs[lsn]
  }

  predicate JournalExtendsJournal(jlong: Journal, jshort: Journal, startLsn: LSN)
    requires jlong.WF() && jshort.WF()
    requires jlong.CanFollow(startLsn)
    requires jshort.CanFollow(startLsn)
  {
    && jlong.CanDiscardTo(jshort.seqEnd)            // jlong is longer
    && jlong.DiscardRecent(jshort.seqEnd) == jshort // they agree on contents in overlap
  }

  predicate InvPersistentJournalGeometry(v: Variables)
    requires v.WF()
  {
    && v.persistentImage.journal.CanFollow(v.persistentImage.mapadt.seqEnd)
  }

  predicate InvEphemeralGeometry(v: Variables)
    requires v.WF() && v.ephemeral.Known?
  {
    // Ephemeral journal begins at persistent map
    && IEJ(v.ephemeral.journal).CanFollow(v.persistentImage.mapadt.seqEnd)
    // Ephemeral map ends no earlier than persistent map
    && v.persistentImage.mapadt.seqEnd <= IMap(v.ephemeral.mapadt).seqEnd
    // Ephemeral journal ends no earlier than ephmeral map
    // (With the first conjunct, this conjunct happens to subsume the second conjunct,
    // but this was the nicest way to write it.)
    && IEJ(v.ephemeral.journal).CanDiscardTo(IMap(v.ephemeral.mapadt).seqEnd)
    // Ephemeral journal is no shorter than persistent state
    && v.persistentImage.SeqEnd() <= EphemeralSeqEnd(v.ephemeral)
    // Local snapshot of mapLsn matched actual map state machine
    && v.ephemeral.mapLsn == v.ephemeral.mapadt.stampedMap.seqEnd
  }

  predicate InvEphemeralValueAgreement(v: Variables)
    requires v.WF() && v.ephemeral.Known?
    requires InvEphemeralGeometry(v)
  {
    // Ephemeral journal agrees with persistent journal
    && JournalOverlapsAgree(v.persistentImage.journal, IEJ(v.ephemeral.journal))
    // Ephemeral map state agrees with ephemeral journal (tacked onto persistent map)
    && IMap(v.ephemeral.mapadt) == MapPlusHistory(v.persistentImage.mapadt, IEJ(v.ephemeral.journal).DiscardRecent(IMap(v.ephemeral.mapadt).seqEnd))
  }

  predicate InvFrozenGeometry(v: Variables)
    requires v.WF() && v.ephemeral.Known?
    requires v.ephemeral.frozenMap.Some?
  {
    // frozen map hsan't passed ephemeral journal
    && v.ephemeral.frozenMap.value.seqEnd <= EphemeralSeqEnd(v.ephemeral)
  }

  predicate FrozenMapDoesntRegress(v: Variables)
  {
    && v.WF()
    && v.ephemeral.Known?
    && v.ephemeral.frozenMap.Some?
    // And it doesn't stop before the persistent image map (so we'll be able
    // to DiscardOld on the ephemeral journal to see they agree)
    && v.persistentImage.mapadt.seqEnd <= v.ephemeral.frozenMap.value.seqEnd
  }

  predicate InvFrozenValueAgreement(v: Variables)
    requires v.WF()
    requires v.ephemeral.Known?
    requires InvEphemeralGeometry(v)
    requires v.ephemeral.frozenMap.Some?
    requires InvFrozenGeometry(v)
  {
    // Agreement is only defined when FrozenMapDoesntRegress, but
    // FrozenMapDoesntRegress isn't an invariant because we runtime-check it at
    // the moment we need it, in CommitStart.
    FrozenMapDoesntRegress(v) ==>
      v.ephemeral.frozenMap.value == MapPlusHistory(v.persistentImage.mapadt, IEJ(v.ephemeral.journal).DiscardRecent(v.ephemeral.frozenMap.value.seqEnd))
    // NB: Frozen Journal agreement comes "for free" because the frozen
    // journal is just defined as the frozenJournalLSN prefix of the
    // ephemeral journal.
  }

  predicate InvInFlightGeometry(v: Variables)
    requires v.WF() && v.inFlightImage.Some?
  {
    && var ifImage := v.inFlightImage.value;

    // We need a well-behaved journal to relate in-flight state to.
    && v.ephemeral.Known?
    && InvEphemeralGeometry(v)

    // Geometry properties
    // In-flight map + journal stitch.
    && ifImage.journal.CanFollow(ifImage.mapadt.seqEnd)
    // Commiting in-flight state won't shrink persistent state
    && v.persistentImage.SeqEnd() <= ifImage.SeqEnd()
    // In-flight map doesn't precede persistent map -- that would cause
    // forgotten lsns to pop back into existence, and we don't have those lsns
    // in the ephemeral journal to compare to.
    && v.persistentImage.mapadt.seqEnd <= ifImage.mapadt.seqEnd
    // in-flight view hsan't passed ephemeral journal
    && ifImage.SeqEnd() <= EphemeralSeqEnd(v.ephemeral)
  }

  predicate InvInFlightValueAgreement(v: Variables)
    requires v.WF() && v.inFlightImage.Some?
    requires InvInFlightGeometry(v)
  {
    && var ifImage := v.inFlightImage.value;
    // in-flight journal is consistent with the persistent journal
    && JournalOverlapsAgree(ifImage.journal, v.persistentImage.journal)
    // in-flight journal is consistent with the ephemeral journal
    && JournalOverlapsAgree(ifImage.journal, IEJ(v.ephemeral.journal))
    // in-flight map matches corresponding state in ephemeral world
    && ifImage.mapadt == MapPlusHistory(v.persistentImage.mapadt,
                      IEJ(v.ephemeral.journal).DiscardRecent(ifImage.mapadt.seqEnd))
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && InvPersistentJournalGeometry(v)
    && (v.ephemeral.Known? ==>
      && InvEphemeralGeometry(v)
      && InvEphemeralValueAgreement(v)

      && (v.ephemeral.frozenMap.Some? ==>
        && InvFrozenGeometry(v)
        && InvFrozenValueAgreement(v)
        )
      )
    && (v.inFlightImage.Some? ==>
      && InvInFlightGeometry(v)
      && InvInFlightValueAgreement(v)
      )
  }

  lemma InitRefines(v: Variables)
    requires v.Init()
    ensures Inv(v)
    ensures I(v) == CrashTolerantMapSpecMod.InitState()
  {
    assert I(v).versions[0].asyncState.appv.kmmap == TotalKMMapMod.EmptyKMMap(); // trigger
  }

  lemma CommitStepPreservesHistory(v: Variables, v': Variables, uiop: UIOp, step: Step, lsn: LSN)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CommitCompleteStep?
    requires v.persistentImage.mapadt.seqEnd <= lsn <= EphemeralSeqEnd(v.ephemeral)
    requires v.inFlightImage.value.mapadt.seqEnd <= lsn  // Can't do much with lsns that have been forgotten
    ensures IEJ(v'.ephemeral.journal).CanDiscardTo(lsn);
    ensures MapPlusHistory(v.persistentImage.mapadt, IEJ(v.ephemeral.journal).DiscardRecent(lsn))
            == MapPlusHistory(v'.persistentImage.mapadt, IEJ(v'.ephemeral.journal).DiscardRecent(lsn));
  {
    // There are six pieces in play here: the persistent and in-flight images and the ephemeral journals:
    //  _________ __________
    // | pdi.map | pdi.jrnl |
    //  --------- ----------
    //  ______________R__________
    // | idi.map      | idi.jrnl |
    //  -------------- ----------
    //            ____________________
    //           | eph.jrnl           |
    //            --------------------
    //                 _______________
    //                | eph'.jrnl     |
    //                 ---------------
    // "R" is the "reference LSN" -- that's where we're going to prune ephemeral.journal, since
    // after the commit it is going to be the LSN of the persistent map.

    var refLsn := v.inFlightImage.value.mapadt.seqEnd;
    var ej := IEJ(v.ephemeral.journal);
    var eji := ej.DiscardRecent(lsn);

    // Here's a calc, but in comments so we can use a shorthand algebra:
    // Let + represent both MapPlusHistory and Concat (they're associative).
    // Let [x..] represent DiscardOld(x) and [..y] represent DiscardRecent(y).
    // var im:=v.inFlightImage.value.mapadt, pm:=v.persistentImage.mapadt, R:=im.seqEnd
    // pm'+ej'[..lsn]
    // im+ej'[..lsn]
    // im+ej[..lsn][R..]
    //   {InvInFlightVersionAgreement}
    // (pm+ej[..R])+ej[..lsn][R..]
    JournalAssociativity(v.persistentImage.mapadt, ej.DiscardRecent(refLsn), ej.DiscardRecent(lsn).DiscardOld(refLsn));
    // pm+(ej[..R]+ej[..lsn][R..])
    assert ej.DiscardRecent(refLsn) == ej.DiscardRecent(lsn).DiscardRecent(refLsn);  // because R <= lsn; smaller lsn are Forgotten
    // pm+(ej[..lsn][..R]+ej[..lsn][R..])
    assert eji.DiscardRecent(refLsn).Concat(eji.DiscardOld(refLsn)) == eji;  // trigger
    // pm+ej[..lsn]
  }

  lemma {:timeLimitMultiplier 2} InvInductivePutStep(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.PutStep?
    ensures Inv(v')
  {
    reveal_JournalOverlapsAgree();
    if v.inFlightImage.Some? {
      var idiEnd := v.inFlightImage.value.mapadt.seqEnd;
      assert IEJ(v.ephemeral.journal).DiscardRecent(idiEnd) == IEJ(v'.ephemeral.journal).DiscardRecent(idiEnd); // trigger
    }
    if FrozenMapDoesntRegress(v') {
      assert FrozenMapDoesntRegress(v);
      var frozenEnd := v.ephemeral.frozenMap.value.seqEnd;
      assert IEJ(v.ephemeral.journal).DiscardRecent(frozenEnd) == IEJ(v'.ephemeral.journal).DiscardRecent(frozenEnd); // trigger
      assert v'.ephemeral.frozenMap.value == MapPlusHistory(v'.persistentImage.mapadt, IEJ(v'.ephemeral.journal).DiscardRecent(v'.ephemeral.frozenMap.value.seqEnd));
      assert InvFrozenValueAgreement(v');
    }

    // InvEphemeralMapIsJournalSnapshot
    var key := uiop.baseOp.req.input.key;
    var val := uiop.baseOp.req.input.value;
    var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));
    JournalAssociativity(v.persistentImage.mapadt, IEJ(v.ephemeral.journal), singleton);
    assert IEJ(v.ephemeral.journal).DiscardRecent(IMap(v.ephemeral.mapadt).seqEnd) == IEJ(v.ephemeral.journal); // trigger
    assert IEJ(v'.ephemeral.journal) == IEJ(v'.ephemeral.journal).DiscardRecent(IMap(v'.ephemeral.mapadt).seqEnd); // trigger
    // TODO(chris): I'm wondering why these subexpressions aren't sort of
    // self-triggering? It's a very common pattern in this code.
//    calc {
//      v'.ephemeral.mapadt;
//      MapPlusHistory(v.ephemeral.mapadt, singleton);
//      MapPlusHistory(MapPlusHistory(v.persistentImage.mapadt, v.ephemeral.journal.DiscardRecent(v.ephemeral.mapadt.seqEnd)), singleton);
//      MapPlusHistory(MapPlusHistory(v.persistentImage.mapadt, v.ephemeral.journal), singleton);
//      MapPlusHistory(v.persistentImage.mapadt, v.ephemeral.journal.Concat(singleton));
//      MapPlusHistory(v.persistentImage.mapadt, v'.ephemeral.journal);
//      MapPlusHistory(v'.persistentImage.mapadt, v'.ephemeral.journal.DiscardRecent(v'.ephemeral.mapadt.seqEnd));
//    }
    assert Inv(v');
  }

  lemma InvInductiveCommitCompleteStep(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.CommitCompleteStep?
    ensures Inv(v')
  {
    reveal_JournalOverlapsAgree();
    if FrozenMapDoesntRegress(v') {
      CommitStepPreservesHistory(v, v', uiop, step, v.ephemeral.frozenMap.value.seqEnd);
    }

    var pm := v.persistentImage.mapadt;
    var em := IMap(v.ephemeral.mapadt);
    var ej := IEJ(v.ephemeral.journal);
    var imEnd := v.inFlightImage.value.mapadt.seqEnd;

    JournalAssociativity(pm, ej.DiscardRecent(imEnd), ej.DiscardOld(imEnd).DiscardRecent(em.seqEnd));
    assert ej.DiscardRecent(em.seqEnd) == ej.DiscardRecent(imEnd).Concat(ej.DiscardOld(imEnd).DiscardRecent(em.seqEnd));   // trigger
  }

  lemma InvInductive(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => {
        reveal_JournalOverlapsAgree();
        assert Inv(v');
      }
      case RecoverStep(puts) => {
        // InvEphemeralMapIsJournalSnapshot
        var em := IMap(v.ephemeral.mapadt);
        var ej := IEJ(v.ephemeral.journal);
        JournalAssociativity(v.persistentImage.mapadt, ej.DiscardRecent(em.seqEnd), puts);
        assert ej.DiscardRecent(em.seqEnd).Concat(puts)
          == IEJ(v'.ephemeral.journal).DiscardRecent(IMap(v'.ephemeral.mapadt).seqEnd);  // trigger
      }
      case AcceptRequestStep() => {
        assert Inv(v');
      }
      case QueryStep() => {
        assert Inv(v');
      }
      case PutStep() => {
        InvInductivePutStep(v, v', uiop, step);
      }
      case DeliverReplyStep() => {
        assert Inv(v');
      }
      case JournalInternalStep() => { assert Inv(v'); }
      case MapInternalStep() => { assert Inv(v'); }
      case ReqSyncStep() => {
        assert Inv(v');
      }
      case ReplySyncStep() => {
        assert Inv(v');
      }
      case FreezeMapAdtStep() => {
        assert Inv(v');
      }
      case CommitStartStep(frozenJournal) => {
        reveal_JournalOverlapsAgree();
        assert Inv(v');
      }
      case CommitCompleteStep() => {
        InvInductiveCommitCompleteStep(v, v', uiop, step);
      }
      case CrashStep() => {
        assert Inv(v');
      }
    }
  }

  lemma {:timeLimitMultiplier 2} JournalAssociativity(x: StampedMap, y: Journal, z: Journal)
    requires y.WF()
    requires z.WF()
    requires y.CanFollow(x.seqEnd)
    requires z.CanFollow(y.seqEnd)
    ensures MapPlusHistory(MapPlusHistory(x, y), z) == MapPlusHistory(x, y.Concat(z))
    decreases z.Len();
  {
    if !z.IsEmpty() {
      var ztrim := z.DiscardRecent(z.seqEnd - 1);
      var yz := y.Concat(z);


      JournalAssociativity(x, y, ztrim);
      assert yz.DiscardRecent(yz.seqEnd - 1) == y.Concat(ztrim); // trigger
    }
  }

  lemma {:timeLimitMultiplier 4} PutStepRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.PutStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    InvInductivePutStep(v, v', uiop, step);

    var j := IEJ(v.ephemeral.journal);
    var j' := IEJ(v'.ephemeral.journal);
    var base := v.persistentImage.mapadt;
    var key := uiop.baseOp.req.input.key;
    var value := uiop.baseOp.req.input.value;

    assert j'.MsgHistory? ==> j' == j'.DiscardRecent(j'.Len() + j'.seqStart);  // seq trigger
    assert j.MsgHistory? ==> j == j.DiscardRecent(j.Len() + j.seqStart);  // seq trigger

    assert forall i | v.persistentImage.mapadt.seqEnd<=i<|I(v).versions| :: j'.DiscardRecent(i) == j.DiscardRecent(i);  // Rob Power Trigger

    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), uiop); // witness
  }

  lemma CommitCompleteNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CommitCompleteStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    // See description & diagram in CommitStepPreservesHistory.
    InvInductive(v, v', uiop);
    forall i | 0<=i<|I(v).versions|
      ensures I(v').versions[i] == if i < I(v').stableIdx then CrashTolerantMapSpecMod.Forgotten else I(v).versions[i]
    {
      if v.inFlightImage.value.SeqEnd() <= i {
        CommitStepPreservesHistory(v, v', uiop, step, i);
      }
    }
    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), UIOp.SyncOp);  // witness
  }

  // Infuriating timetouts driving me back to IronFleet punts
  lemma BatchNextA(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires
      || step.LoadEphemeralFromPersistentStep?
      || step.RecoverStep?
      || step.AcceptRequestStep?
      || step.QueryStep?
      || step.DeliverReplyStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    InvInductive(v, v', uiop);
    if step.LoadEphemeralFromPersistentStep? {
      assert uiop == UIOp.NoopOp;
    }
    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), uiop);
  }

  lemma BatchNextB(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires
      || step.JournalInternalStep?
      || step.MapInternalStep?
      || step.ReqSyncStep?
      || step.ReplySyncStep?
      || step.FreezeMapAdtStep?
      || step.CommitStartStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    InvInductive(v, v', uiop);
    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), uiop);
  }

  lemma {:timeLimitMultiplier 2} CrashNext(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CrashStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    reveal_JournalOverlapsAgree();
    var stableLSN := v'.persistentImage.SeqEnd();
    if v.ephemeral.Known? {
      assert forall lsn | v.persistentImage.mapadt.seqEnd <= lsn < stableLSN :: true; // trigger
      assert v'.persistentImage.journal.DiscardRecent(stableLSN) == IEJ(v.ephemeral.journal).DiscardRecent(stableLSN); // trigger
    }
    assert CrashTolerantMapSpecMod.Crash(I(v), I(v'));  //trigger
    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), uiop); // case boilerplate

    assert CrashTolerantMapSpecMod.NextStep(Ic(), I(v), I(v'), UIOp.CrashOp);  // witness
  }

  lemma NextRefines(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(Ic(), I(v), I(v'), uiop)
  {
    InvInductive(v, v', uiop);

    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => { BatchNextA(v, v', uiop, step); }
      case RecoverStep(puts) => { BatchNextA(v, v', uiop, step); }
      case AcceptRequestStep() => { BatchNextA(v, v', uiop, step); }
      case QueryStep() => { BatchNextA(v, v', uiop, step); }
      case PutStep() => { PutStepRefines(v, v', uiop, step); }
      case DeliverReplyStep() => { BatchNextA(v, v', uiop, step); }
      case JournalInternalStep() => { BatchNextB(v, v', uiop, step); }
      case MapInternalStep() => { BatchNextB(v, v', uiop, step); }
      case ReqSyncStep() => { BatchNextB(v, v', uiop, step); }
      case ReplySyncStep() => { BatchNextB(v, v', uiop, step); }
      case FreezeMapAdtStep() => { BatchNextB(v, v', uiop, step); }
      case CommitStartStep(frozenJournal) => { BatchNextB(v, v', uiop, step); }
      case CommitCompleteStep() => { CommitCompleteNext(v, v', uiop, step); }
      case CrashStep() => { CrashNext(v, v', uiop, step); }
    }
  }
}
