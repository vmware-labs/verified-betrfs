include "CoordProgramMod.i.dfy"

// This module shows refinement of CoordProgram to CrashTolerantMapSpecMod,
// thereby functioning as the top layer in a refinement stack for program
// models in refinement layers below.
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

  predicate InvLSNTracksPersistentWhenJournalEmpty(v: CoordProgramMod.Variables)
  {
    // TODO this may be obsoleted by cleaner use of SeqEnd() predicate
    // We need this extra condition to ensure that, when the ephemeral journal
    // is empty, the ephemeral map indeed matches the disk -- otherwise we won't
    // assign the right lsn to new puts.
    && (v.ephemeral.Known? && v.ephemeral.journal.EmptyHistory? ==>
        NextLSN(v) == v.persistentSuperblock.mapadt.seqEnd
      )
  }

  predicate JournalExtendsJournal(jlong: Journal, jshort: Journal, startLsn: LSN)
  {
    && jlong.WF()
    && jshort.WF()
    && jshort.CanFollow(startLsn)
    && jlong.CanFollow(startLsn)
    && jlong.CanDiscardTo(SeqEndFor(startLsn, jshort))
    && jlong.DiscardRecent(SeqEndFor(startLsn, jshort)) == jshort
  }

  predicate InvJournalMonotonic(v: CoordProgramMod.Variables)
  {
    v.ephemeral.Known? ==>
      JournalExtendsJournal(v.ephemeral.journal, v.persistentSuperblock.journal, v.persistentSuperblock.mapadt.seqEnd)
  }

  predicate InvEphemeralJournalExtendsPersistentJournal(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && v.ephemeral.Known?
    && JournalExtendsJournal(v.ephemeral.journal, v.persistentSuperblock.journal, v.persistentSuperblock.mapadt.seqEnd)
  }

  predicate InvInFlightVersionAgreement(v: CoordProgramMod.Variables)
  {
    && InvEphemeralJournalExtendsPersistentJournal(v) // already appears higher in Inv, but we need it too.

    && v.inFlightSuperblock.Some?
    && var psb := v.persistentSuperblock;
    && var isb := v.inFlightSuperblock.value;
    && var ej := v.ephemeral.journal;

    // Ephemeral journal is at least as far as in-flight (frozen) map.
    && ej.CanDiscardTo(isb.mapadt.seqEnd)
    // in-flight journal extends persistent journal
    && JournalExtendsJournal(isb.journal, psb.journal, psb.mapadt.seqEnd)
    // Ephemeral journal agrees with in-flight journal
    && JournalExtendsJournal(ej.DiscardOld(isb.mapadt.seqEnd), isb.journal, isb.mapadt.seqEnd)
    // in-flight map matches corresponding state in ephemeral world
    && isb.mapadt == MapPlusHistory(psb.mapadt, ej.DiscardRecent(isb.mapadt.seqEnd))
  }

  predicate InvInFlightProperties(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && (v.inFlightSuperblock.Some? ==>
      && v.ephemeral.Known?
      && v.ephemeral.journal.CanDiscardTo(v.inFlightSuperblock.value.mapadt.seqEnd)
      && v.persistentSuperblock.SeqEnd() <= v.inFlightSuperblock.value.SeqEnd() // commit doesn't shrink persistent state
      && v.inFlightSuperblock.value.SeqEnd() <= v.ephemeral.SeqEnd()  // maintain InvJournalMonotonic
      && InvInFlightVersionAgreement(v)
      )
  }

  predicate Inv(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && (v.ephemeral.Known? ==>
      // StampedMapret ephemeral state by stitching ephemeral journal (which
      // invariantly matches ephemeral mapadt) with persistent mapadt (which
      // it can follow exactly without beheading).
      && InvEphemeralJournalExtendsPersistentJournal(v)
      && InvLSNTracksPersistentWhenJournalEmpty(v)
      )
    && InvJournalMonotonic(v)
    && InvInFlightProperties(v)
  }

  lemma InitRefines(v: CoordProgramMod.Variables)
    requires CoordProgramMod.Init(v)
    ensures Inv(v)
    ensures I(v) == CrashTolerantMapSpecMod.InitState()
  {
//    assert JournalInterpTypeMod.Mkfs().SyncReqsAt(0) == {}; // trigger set comprehension
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
        assert Inv(v');
      }
      case AcceptRequestStep() => {
        assert Inv(v');
      }
      case QueryStep(key, val) => {
        assert Inv(v');
      }
      case PutStep() => {
        if v.inFlightSuperblock.Some? {
          var isbEnd := v.inFlightSuperblock.value.mapadt.seqEnd;
          assert v.ephemeral.journal.DiscardRecent(isbEnd) == v'.ephemeral.journal.DiscardRecent(isbEnd); // trigger
        }
        assert Inv(v');
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
        assert Inv(v');
      }
      case CommitStartStep(seqBoundary) => {
        assert v'.inFlightSuperblock.Some?;
        //assert v'.persistentSuperblock.SeqEnd() <=  LEFT OFF HERE looking at BestFrozenState.
        assert v'.persistentSuperblock.SeqEnd() <= v'.inFlightSuperblock.value.SeqEnd(); // commit doesn't shrink persistent state
        var psb' := v'.persistentSuperblock;
        var isb' := v'.inFlightSuperblock.value;
        var ej' := v'.ephemeral.journal;
        assume JournalExtendsJournal(isb'.journal, psb'.journal, psb'.mapadt.seqEnd);
        assume InvInFlightVersionAgreement(v');
        assert Inv(v');
      }
      case CommitCompleteStep() => {
        assert Inv(v');
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

  lemma JournalAssociativity(x: MapAdt, y: Journal, z: Journal)
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

  lemma CommitStepRefines(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp, step: Step)
    requires Inv(v)
    requires CoordProgramMod.Next(v, v', uiop)
    requires NextStep(v, v', uiop, step);
    requires step.CommitCompleteStep?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
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

    forall i | 0<=i<|I(v).versions| ensures
      || I(v').versions[i] == I(v).versions[i]
      || (i < I(v').stableIdx && I(v').versions[i].Forgotten?)
    {
      var refLsn := v.inFlightSuperblock.value.mapadt.seqEnd;

      if refLsn <= i {
        var ej := v.ephemeral.journal;
        var eji := v.ephemeral.journal.DiscardRecent(i);

        // Here's a calc, but commented to use a shorthand algebra:
        // Let + represent both MapPlusHistory and Concat (they're associative).
        // Let [x..] represent DiscardOld(x) and [..y] represent DiscardRecent(y).
        // var im:=v.inFlightSuperblock.value.mapadt, pm:=v.persistentSuperblock.mapadt, R:=im.seqEnd
        // I(v')
        // im+ej'[..i]
        // im+ej[..i][R..]
        // InvInFlightVersionAgreement
        // (pm+ej[..R])+ej[..i][R..]
        JournalAssociativity(v.persistentSuperblock.mapadt, ej.DiscardRecent(refLsn), ej.DiscardRecent(i).DiscardOld(refLsn));
        // pm+(ej[..R]+ej[..i][R..])
        assert ej.DiscardRecent(refLsn) == ej.DiscardRecent(i).DiscardRecent(refLsn);  // because R <= i; smaller i are Forgotten
        // pm+(ej[..i][..R]+ej[..i][R..])
        assert eji.DiscardRecent(refLsn).Concat(eji.DiscardOld(refLsn)) == eji;  // trigger
        // pm+ej[..i]
        // I(v)
      }
    }
    assert CrashTolerantMapSpecMod.Sync(I(v), I(v'));
    assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), UIOp.SyncOp);
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }

  lemma NextRefines(v: CoordProgramMod.Variables, v': CoordProgramMod.Variables, uiop: CoordProgramMod.UIOp)
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
      case QueryStep(key, val) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case PutStep() => {
        var j := v.ephemeral.journal;
        var j' := v'.ephemeral.journal;
        var base := v.persistentSuperblock.mapadt;
        var key := uiop.baseOp.req.input.k;
        var val := uiop.baseOp.req.input.v;

        assert j'.MsgHistory? ==> j' == j'.DiscardRecent(j'.Len() + j'.seqStart);  // seq trigger
        if j.MsgHistory? {
          assert j == j.DiscardRecent(j.Len() + j.seqStart);  // seq trigger
          SingletonConcatIsMapUpdate(base, j, j.seqEnd, KeyedMessage(key, Define(val)));
        }
        assert forall i | v.persistentSuperblock.mapadt.seqEnd<=i<|I(v).versions| :: j'.DiscardRecent(i) == j.DiscardRecent(i);  // Rob Power Trigger

        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
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
        assume false;
        assert uiop == CrashTolerantMapSpecMod.NoopOp;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case CommitCompleteStep() => { CommitStepRefines(v, v', uiop, step); }
    }
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
