include "CoordProgramMod.i.dfy"

// This module shows refinement of CoordProgram to CrashTolerantMapSpecMod,
// thereby functioning as the top layer in a refinement stack for program
// models in refinement layers below.

// TODO(jonh): satisfy a refinement-module proof obligation!
module CoordProgramRefinement {
  import opened SequencesLite // Last, DropLast
  import opened CoordProgramMod
  import opened MsgHistoryMod
  import opened KeyType
  import opened ValueMessage
  import MapSpecMod

  import Async = CrashTolerantMapSpecMod.async

  function StampedMapToVersion(sm: StampedMapMod.StampedMap) : CrashTolerantMapSpecMod.Version
  {
    CrashTolerantMapSpecMod.Version(Async.PersistentState(MapSpecMod.Variables(sm)))
  }

  function VersionsWithForgottenPrefix(base: StampedMapMod.StampedMap, journal: Journal, stableLSN: LSN) : (versions:seq<CrashTolerantMapSpecMod.Version>)
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
    requires journal.CanDiscardTo(stableLSN)
    ensures |versions| == SeqEndFor(base.seqEnd, journal)+1
  {
    // Construct a Version seq with the entries before stableLSN Forgotten: that's what spec expects.
    var numVersions := SeqEndFor(base.seqEnd, journal) + 1;
    seq(numVersions, lsn requires 0<=lsn<numVersions =>
      if lsn < stableLSN
      then CrashTolerantMapSpecMod.Forgotten
      else StampedMapToVersion(MapPlusHistory(base, journal.DiscardRecent(lsn))))
  }

  function I(v: CoordProgramMod.Variables) : CrashTolerantMapSpecMod.Variables
  {
    var stableLSN := v.persistentSuperblock.SeqEnd();

    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()  // silly-handler
    else if v.ephemeral.Known?
    then CrashTolerantMapSpecMod.Variables(
      VersionsWithForgottenPrefix(v.persistentSuperblock.mapadt, v.ephemeral.journal, stableLSN),
        v.ephemeral.progress, v.ephemeral.syncReqs, stableLSN)
    else CrashTolerantMapSpecMod.Variables(
      VersionsWithForgottenPrefix(v.persistentSuperblock.mapadt, v.persistentSuperblock.journal, stableLSN),
        Async.InitEphemeralState(), map[], stableLSN)
  }

  // Where these journals share an LSN, they map it to the same message.
  predicate JournalOverlapsAgree(j0: Journal, j1: Journal)
    requires j0.WF() && j1.WF()
  {
    forall lsn | j0.Contains(lsn) && j1.Contains(lsn) :: j0.msgs[lsn] == j1.msgs[lsn]
  }

  predicate JournalExtendsJournal(jlong: Journal, jshort: Journal, startLsn: LSN)
    requires jlong.WF() && jshort.WF()
    requires jlong.CanFollow(startLsn)
    requires jshort.CanFollow(startLsn)
  {
    && jlong.CanDiscardTo(SeqEndFor(startLsn, jshort))            // jlong is longer
    && jlong.DiscardRecent(SeqEndFor(startLsn, jshort)) == jshort // they agree on contents in overlap
  }

  predicate InvPersistentJournalGeometry(v: CoordProgramMod.Variables)
  {
    && v.persistentSuperblock.journal.CanFollow(v.persistentSuperblock.mapadt.seqEnd)
  }

  predicate InvEphemeralGeometry(v: CoordProgramMod.Variables)
    requires v.WF() && v.ephemeral.Known?
  {
    // Ephemeral journal begins at persistent map
    && v.ephemeral.journal.CanFollow(v.persistentSuperblock.mapadt.seqEnd)
    // Ephemeral map ends no earlier than persistent map
    && v.persistentSuperblock.mapadt.seqEnd <= v.ephemeral.mapadt.seqEnd
    // Ephemeral journal ends no earlier than ephmeral map
    // (With the first conjunct, this conjunct happens to subsume the second conjunct,
    // but this was the nicest way to write it.)
    && v.ephemeral.journal.CanDiscardTo(v.ephemeral.mapadt.seqEnd)
    // Ephemeral journal is no shorter than persistent state
    && v.persistentSuperblock.SeqEnd() <= v.ephemeral.SeqEnd()
  }

  predicate InvEphemeralValueAgreement(v: CoordProgramMod.Variables)
    requires v.WF() && v.ephemeral.Known?
    requires InvEphemeralGeometry(v)
  {
    // Ephemeral journal agrees with persistent journal
    && JournalOverlapsAgree(v.persistentSuperblock.journal, v.ephemeral.journal)
    // Ephemeral map state agrees with ephemeral journal (tacked onto persistent map)
    && v.ephemeral.mapadt == MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.DiscardRecent(v.ephemeral.mapadt.seqEnd))
  }

  predicate InvFrozenGeometry(v: CoordProgramMod.Variables)
    requires v.WF() && v.ephemeral.Known?
    requires v.ephemeral.frozenMap.Some?
  {
    // frozen map hsan't passed ephemeral journal
    && v.ephemeral.frozenMap.value.seqEnd <= v.ephemeral.SeqEnd()
  }

  predicate FrozenMapDoesntRegress(v: CoordProgramMod.Variables)
  {
    && v.ephemeral.Known?
    && v.ephemeral.frozenMap.Some?
    // And it doesn't stop before the persistent superblock (so we'll be able
    // to DiscardOld on the ephemeral journal to see they agree)
    && v.persistentSuperblock.mapadt.seqEnd <= v.ephemeral.frozenMap.value.seqEnd
  }

  predicate InvFrozenValueAgreement(v: CoordProgramMod.Variables)
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
      v.ephemeral.frozenMap.value == MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.DiscardRecent(v.ephemeral.frozenMap.value.seqEnd))
    // NB: Frozen Journal agreement comes "for free" because the frozen
    // journal is just defined as the frozenJournalLSN prefix of the
    // ephemeral journal.
  }

  predicate InvInFlightGeometry(v: CoordProgramMod.Variables)
    requires v.WF() && v.inFlightSuperblock.Some?
  {
    && var isb := v.inFlightSuperblock.value;

    // We need a well-behaved journal to relate in-flight state to.
    && v.ephemeral.Known?
    && InvEphemeralGeometry(v)

    // Geometry properties
    // In-flight map + journal stitch.
    && isb.journal.CanFollow(isb.mapadt.seqEnd)
    // Commiting in-flight state won't shrink persistent state
    && v.persistentSuperblock.SeqEnd() <= isb.SeqEnd()
    // In-flight map doesn't precede persistent map -- that would cause
    // forgotten lsns to pop back into existence, and we don't have those lsns
    // in the ephemeral journal to compare to.
    && v.persistentSuperblock.mapadt.seqEnd <= isb.mapadt.seqEnd
    // in-flight view hsan't passed ephemeral journal
    && isb.SeqEnd() <= v.ephemeral.SeqEnd()
  }

  predicate InvInFlightValueAgreement(v: CoordProgramMod.Variables)
    requires v.WF() && v.inFlightSuperblock.Some?
    requires InvInFlightGeometry(v)
  {
    && var isb := v.inFlightSuperblock.value;
    // in-flight journal is consistent with the persistent journal
    && JournalOverlapsAgree(isb.journal, v.persistentSuperblock.journal)
    // in-flight journal is consistent with the ephemeral journal
    && JournalOverlapsAgree(isb.journal, v.ephemeral.journal)
    // in-flight map matches corresponding state in ephemeral world
    && isb.mapadt == MapPlusHistory(v.persistentSuperblock.mapadt,
                      v.ephemeral.journal.DiscardRecent(isb.mapadt.seqEnd))
  }

  predicate Inv(v: CoordProgramMod.Variables)
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
    && (v.inFlightSuperblock.Some? ==>
      && InvInFlightGeometry(v)
      && InvInFlightValueAgreement(v)
      )
  }

  lemma InitRefines(v: CoordProgramMod.Variables)
    requires CoordProgramMod.Init(v)
    ensures Inv(v)
    ensures I(v) == CrashTolerantMapSpecMod.InitState()
  {
//    assert JournalInterpTypeMod.Mkfs().SyncReqsAt(0) == {}; // trigger set comprehension
  }

  lemma CommitStepPreservesHistory(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step, lsn: LSN)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CommitCompleteStep?
    requires v.persistentSuperblock.mapadt.seqEnd <= lsn <= v.ephemeral.SeqEnd()
    requires v.inFlightSuperblock.value.mapadt.seqEnd <= lsn  // Can't do much with lsns that have been forgotten
    ensures v'.ephemeral.journal.CanDiscardTo(lsn);
    ensures MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.DiscardRecent(lsn))
            == MapPlusHistory(v'.persistentSuperblock.mapadt, v'.ephemeral.journal.DiscardRecent(lsn));
  {
    // There are six pieces in play here: the persistent and in-flight superblocks and the ephemeral journals:
    //  _________ __________
    // | psb.map | psb.jrnl |
    //  --------- ----------
    //  ______________R__________
    // | isb.map      | isb.jrnl |
    //  -------------- ----------
    //            ____________________
    //           | eph.jrnl           |
    //            --------------------
    //                 _______________
    //                | eph'.jrnl     |
    //                 ---------------
    // "R" is the "reference LSN" -- that's where we're going to prune ephemeral.journal, since
    // after the commit it is going to be the LSN of the persistent map.

    var refLsn := v.inFlightSuperblock.value.mapadt.seqEnd;
    var ej := v.ephemeral.journal;
    var eji := v.ephemeral.journal.DiscardRecent(lsn);

    // Here's a calc, but in comments so we can use a shorthand algebra:
    // Let + represent both MapPlusHistory and Concat (they're associative).
    // Let [x..] represent DiscardOld(x) and [..y] represent DiscardRecent(y).
    // var im:=v.inFlightSuperblock.value.mapadt, pm:=v.persistentSuperblock.mapadt, R:=im.seqEnd
    // pm'+ej'[..lsn]
    // im+ej'[..lsn]
    // im+ej[..lsn][R..]
    // InvInFlightVersionAgreement
    // (pm+ej[..R])+ej[..lsn][R..]
    JournalAssociativity(v.persistentSuperblock.mapadt, ej.DiscardRecent(refLsn), ej.DiscardRecent(lsn).DiscardOld(refLsn));
    // pm+(ej[..R]+ej[..lsn][R..])
    assert ej.DiscardRecent(refLsn) == ej.DiscardRecent(lsn).DiscardRecent(refLsn);  // because R <= lsn; smaller lsn are Forgotten
    // pm+(ej[..lsn][..R]+ej[..lsn][R..])
    assert eji.DiscardRecent(refLsn).Concat(eji.DiscardOld(refLsn)) == eji;  // trigger
    // pm+ej[..lsn]
  }

  lemma {:timeLimitMultiplier 2} InvInductivePutStep(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.PutStep?
    ensures Inv(v')
  {
    if v.inFlightSuperblock.Some? {
      var isbEnd := v.inFlightSuperblock.value.mapadt.seqEnd;
      assert v.ephemeral.journal.DiscardRecent(isbEnd) == v'.ephemeral.journal.DiscardRecent(isbEnd); // trigger
    }
    if FrozenMapDoesntRegress(v') {
      assert FrozenMapDoesntRegress(v);
      var frozenEnd := v.ephemeral.frozenMap.value.seqEnd;
      assert v.ephemeral.journal.DiscardRecent(frozenEnd) == v'.ephemeral.journal.DiscardRecent(frozenEnd); // trigger
      assert v'.ephemeral.frozenMap.value == MapPlusHistory(v'.persistentSuperblock.mapadt, v'.ephemeral.journal.DiscardRecent(v'.ephemeral.frozenMap.value.seqEnd));
      assert InvFrozenValueAgreement(v');
    }

    // InvEphemeralMapIsJournalSnapshot
    var key := uiop.baseOp.req.input.key;
    var val := uiop.baseOp.req.input.value;
    var singleton := MsgHistoryMod.Singleton(NextLSN(v), KeyedMessage(key, Define(val)));
    JournalAssociativity(v.persistentSuperblock.mapadt, v.ephemeral.journal, singleton);
    assert v.ephemeral.journal.DiscardRecent(v.ephemeral.mapadt.seqEnd) == v.ephemeral.journal; // trigger
    assert v'.ephemeral.journal == v'.ephemeral.journal.DiscardRecent(v'.ephemeral.mapadt.seqEnd); // trigger
    // TODO(chris): I'm wondering why these subexpressions aren't sort of
    // self-triggering? It's a very common pattern in this code.
//    calc {
//      v'.ephemeral.mapadt;
//      MapPlusHistory(v.ephemeral.mapadt, singleton);
//      MapPlusHistory(MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.DiscardRecent(v.ephemeral.mapadt.seqEnd)), singleton);
//      MapPlusHistory(MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal), singleton);
//      MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.Concat(singleton));
//      MapPlusHistory(v.persistentSuperblock.mapadt, v'.ephemeral.journal);
//      MapPlusHistory(v'.persistentSuperblock.mapadt, v'.ephemeral.journal.DiscardRecent(v'.ephemeral.mapadt.seqEnd));
//    }
    assert Inv(v');
  }

  lemma InvInductiveCommitCompleteStep(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step)
    requires step.CommitCompleteStep?
    ensures Inv(v')
  {
    if FrozenMapDoesntRegress(v') {
      assert FrozenMapDoesntRegress(v);
      calc {
        v'.ephemeral.frozenMap.value;
        v.ephemeral.frozenMap.value;
        MapPlusHistory(v.persistentSuperblock.mapadt, v.ephemeral.journal.DiscardRecent(v.ephemeral.frozenMap.value.seqEnd));
        {
          CommitStepPreservesHistory(v, v', uiop, step, v.ephemeral.frozenMap.value.seqEnd);
        }
        MapPlusHistory(v'.persistentSuperblock.mapadt, v'.ephemeral.journal.DiscardRecent(v'.ephemeral.frozenMap.value.seqEnd));
      }
    }

    // InvEphemeralMapIsJournalSnapshot
    var pm := v.persistentSuperblock.mapadt;
    var em := v.ephemeral.mapadt;
    var ej := v.ephemeral.journal;
    var imEnd := v.inFlightSuperblock.value.mapadt.seqEnd;

    JournalAssociativity(pm, ej.DiscardRecent(imEnd), ej.DiscardOld(imEnd).DiscardRecent(em.seqEnd));
    assert ej.DiscardRecent(em.seqEnd) == ej.DiscardRecent(imEnd).Concat(ej.DiscardOld(imEnd).DiscardRecent(em.seqEnd));   // trigger
  }

  lemma InvInductive(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    ensures Inv(v')
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralStateStep() => {
        assert Inv(v');
      }
      case RecoverStep(puts) => {
        // InvEphemeralMapIsJournalSnapshot
        var em := v.ephemeral.mapadt;
        var ej := v.ephemeral.journal;
        JournalAssociativity(v.persistentSuperblock.mapadt, ej.DiscardRecent(em.seqEnd), puts);
        assert ej.DiscardRecent(em.seqEnd).Concat(puts)
          == v'.ephemeral.journal.DiscardRecent(v'.ephemeral.mapadt.seqEnd);  // trigger
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
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep() => {
        assert Inv(v');
      }
      case ReplySyncStep() => {
        assert Inv(v');
      }
      case FreezeJournalStep(newFrozenLSN) => {
        assert Inv(v');
      }
      case FreezeMapAdtStep() => {
        assert v'.ephemeral.Known?;
        assert v'.ephemeral.frozenMap.Some?;
        calc {
          v'.ephemeral.frozenMap.value;
          MapPlusHistory(v'.persistentSuperblock.mapadt, v'.ephemeral.journal.DiscardRecent(v'.ephemeral.frozenMap.value.seqEnd));
        }
        assert InvFrozenValueAgreement(v');
        assert Inv(v');
      }
      case CommitStartStep(seqBoundary) => {
        assert Inv(v');
      }
      case CommitCompleteStep() => {
        InvInductiveCommitCompleteStep(v, v', uiop, step);
      }
    }
  }

  lemma SingletonConcatIsMapUpdate(base: StampedMapMod.StampedMap, j: Journal, lsn: LSN, kmsg: KeyedMessage)
    requires j.WF()
    requires j.CanFollow(base.seqEnd)
    requires lsn == if j.EmptyHistory? then base.seqEnd else j.seqEnd
    requires kmsg.message.Define?;  // we'll have to get smarter if we want to generalize.
    ensures j.Concat(MsgHistoryMod.Singleton(lsn, kmsg)).CanFollow(base.seqEnd)
    ensures MapPlusHistory(base, j).mi[kmsg.key := kmsg.message]
      == MapPlusHistory(base, j.Concat(MsgHistoryMod.Singleton(lsn, kmsg))).mi
  {
    var j' := j.Concat(MsgHistoryMod.Singleton(lsn, kmsg));
    ApplyToStampedMapRecursiveIsDiscardTail(j', base, j'.Len()-1);
    assert j'.DiscardRecent(j'.seqStart + j.Len()) == j;  // trigger
    assert j'.ApplyToStampedMap(base).mi == j'.ApplyToStampedMapRecursive(base, j'.Len()-1).mi[kmsg.key := kmsg.message];  // trigger
  }

  lemma {:timeLimitMultiplier 2} JournalAssociativity(x: MapAdt, y: Journal, z: Journal)
    requires y.WF()
    requires z.WF()
    requires y.CanFollow(x.seqEnd)
    requires z.CanFollow(SeqEndFor(x.seqEnd, y))
    ensures MapPlusHistory(MapPlusHistory(x, y), z) == MapPlusHistory(x, y.Concat(z))
    decreases z.Len();
  {
    if !z.EmptyHistory? {
      var ztrim := z.DiscardRecent(z.seqEnd - 1);
      var yz := y.Concat(z);

      JournalAssociativity(x, y, ztrim);
      ApplyToStampedMapRecursiveIsDiscardTail(z, MapPlusHistory(x, y), z.Len()-1);
      assert yz.DiscardRecent(yz.seqEnd - 1) == y.Concat(ztrim); // trigger
      ApplyToStampedMapRecursiveIsDiscardTail(yz, x, yz.Len()-1);
    }
  }

  lemma PutStepRefines(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.PutStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  {
    InvInductivePutStep(v, v', uiop, step); // TODO why do we need a whole fancy proof up there but not here!?

    var j := v.ephemeral.journal;
    var j' := v'.ephemeral.journal;
    var base := v.persistentSuperblock.mapadt;
    var key := uiop.baseOp.req.input.key;
    var value := uiop.baseOp.req.input.value;

    assert j'.MsgHistory? ==> j' == j'.DiscardRecent(j'.Len() + j'.seqStart);  // seq trigger
    SingletonConcatIsMapUpdate(base, j, v.ephemeral.SeqEnd(), KeyedMessage(key, Define(value)));
    assert j.MsgHistory? ==> j == j.DiscardRecent(j.Len() + j.seqStart);  // seq trigger

    assert forall i | v.persistentSuperblock.mapadt.seqEnd<=i<|I(v).versions| :: j'.DiscardRecent(i) == j.DiscardRecent(i);  // Rob Power Trigger

    assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // witness
  }

  lemma CommitStepRefines(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CommitCompleteStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  {
    // See description & diagram in CommitStepPreservesHistory.
    InvInductive(v, v', uiop);
    forall i | 0<=i<|I(v).versions|
      ensures I(v').versions[i] == if i < I(v').stableIdx then CrashTolerantMapSpecMod.Forgotten else I(v).versions[i]
    {
      if v.inFlightSuperblock.value.SeqEnd() <= i {
        CommitStepPreservesHistory(v, v', uiop, step, i);
      }
    }
    assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), UIOp.SyncOp);  // witness
  }

  lemma {:timeLimitMultiplier 2} NextRefines(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  {
    InvInductive(v, v', uiop);

    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralStateStep() => {
        assert uiop == CrashTolerantMapSpecMod.NoopOp;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case RecoverStep(puts) => {
        assert uiop == CrashTolerantMapSpecMod.NoopOp;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case AcceptRequestStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case QueryStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case PutStep() => {
        PutStepRefines(v, v', uiop, step);
      }
      case DeliverReplyStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case ReplySyncStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case FreezeJournalStep(newFrozenLSN) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case FreezeMapAdtStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case CommitStartStep(seqBoundary) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case CommitCompleteStep() => { CommitStepRefines(v, v', uiop, step); }
    }
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
