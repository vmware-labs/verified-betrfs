include "../IOSystem.s.dfy"
include "../ProofObligations.s.dfy"
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

  function InterpsFromBase(base: InterpMod.Interp, journal: Journal) : seq<InterpMod.Interp>
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    var numVersions := journal.Len()+1;  // Can apply zero to Len() messages.
    seq(numVersions, i requires 0 <= i < numVersions =>
      journal.PruneTail(i + journal.seqStart).ApplyToInterp(base))
  }

  function VersionsFromBase(base: InterpMod.Interp, journal: Journal) : (versions:seq<CrashTolerantMapSpecMod.Version>)
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    var numVersions := journal.Len()+1;
    seq(numVersions, i requires 0 <= i < numVersions => 
      var interp := InterpsFromBase(base, journal)[i];
      CrashTolerantMapSpecMod.Version(Async.PersistentState(MapSpecMod.Variables(interp))))
  }

  function VersionsWithForgottenPrefix(base: InterpMod.Interp, journal: Journal) : (versions:seq<CrashTolerantMapSpecMod.Version>)
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
    ensures |versions| == SeqEndFor(base, journal)+1
  {
    var forgottenVersions := seq(base.seqEnd, i => CrashTolerantMapSpecMod.Forgotten);
    forgottenVersions + VersionsFromBase(base, journal)
  }

  // Stitch together a base map, a journal, and the specified ephemeral request state.
  function IStitch(base: MapAdt, journal: Journal, progress: Async.EphemeralState, syncReqs: SyncReqs, stableLSN: LSN) : CrashTolerantMapSpecMod.Variables
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    CrashTolerantMapSpecMod.Variables(VersionsWithForgottenPrefix(base, journal), progress, syncReqs, stableLSN)
  }

  function I(v: CoordProgramMod.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()
    else if v.ephemeral.Known?
      then IStitch(v.persistentSuperblock.mapadt, v.ephemeral.journal,
        v.ephemeral.progress, v.ephemeral.syncReqs, v.persistentSuperblock.SeqEnd())
      else IStitch(v.persistentSuperblock.mapadt, v.persistentSuperblock.journal,
        Async.InitEphemeralState(), map[], v.persistentSuperblock.SeqEnd())
  }

  predicate InvLSNTracksPersistentWhenJournalEmpty(v: CoordProgramMod.Variables)
  {
    // TODO this may be obsoleted by cleaner use of SeqEnd() predicate
    // We need this extra condition to ensure that, when the ephemeral journal
    // is empty, the ephemeral map indeed matches the disk -- otherwise we won't
    // assign the right lsn to new puts.
    && (v.ephemeral.Known? && v.ephemeral.journal.IsEmpty() ==>
        v.ephemeral.mapadt.seqEnd == v.persistentSuperblock.mapadt.seqEnd
      )
  }

  predicate InvJournalMonotonic(v: CoordProgramMod.Variables)
  {
    v.ephemeral.Known? ==>
      v.persistentSuperblock.journal.seqEnd <= v.ephemeral.journal.seqEnd
  }

  predicate InvEphemeralJournalMatchesPersistentJournal(v: CoordProgramMod.Variables)
    requires v.WF()
  {
    v.ephemeral.journal.PruneTail(v.persistentSuperblock.SeqEnd()) == v.persistentSuperblock.journal
  }

  predicate InvInFlightVersionAgreement(v: CoordProgramMod.Variables)
    requires v.WF()
    requires v.inFlightSuperblock.Some?
  {
    var psb := v.persistentSuperblock;
    var isb := v.inFlightSuperblock.value;

    // in-flight map summarizes existing persistent map plus necessary prefix of persistent journal
    && isb.mapadt == psb.journal.PruneTail(isb.mapadt.seqEnd).ApplyToInterp(psb.mapadt)
    // in-flight journal captures remainder of persistent journal
    && isb.journal.PruneTail(psb.SeqEnd()) == psb.journal.PruneHead(isb.mapadt.seqEnd)
  }

  predicate InvInFlightProperties(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && (v.inFlightSuperblock.Some? ==>
      && v.ephemeral.Known?
      && v.ephemeral.journal.CanPruneTo(v.inFlightSuperblock.value.mapadt.seqEnd)
      && v.persistentSuperblock.SeqEnd() <= v.inFlightSuperblock.value.SeqEnd() // commit doesn't shrink persistent state
      && v.inFlightSuperblock.value.SeqEnd() <= v.ephemeral.SeqEnd()  // maintain InvJournalMonotonic
      && InvInFlightVersionAgreement(v)
      )
  }

  predicate Inv(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && (v.ephemeral.Known? ==>
      // Interpret ephemeral state by stitching ephemeral journal (which
      // invariantly matches ephemeral mapadt) with persistent mapadt (which
      // it can follow exactly without beheading).
      && v.ephemeral.journal.CanFollow(v.persistentSuperblock.mapadt.seqEnd)
      && InvEphemeralJournalMatchesPersistentJournal(v)
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
      case QueryStep(key, val) => {
        assert Inv(v');
      }
      case PutStep() => {
        assert Inv(v');
      }
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep() => {
        assert Inv(v');
      }
      case CompleteSyncStep() => {
        assert Inv(v');
      }
      case FreezeJournalStep(newFrozenLSN) => {
        assert Inv(v');
      }
      case FreezeMapAdtStep() => {
        assert Inv(v');
      }
      case CommitStartStep(seqBoundary) => {
        assume Inv(v');
      }
      case CommitCompleteStep() => {
        assert Inv(v');
      }
    }
  }

  lemma ApplicationConcatenation(base: InterpMod.Interp, j: Journal, lsn: LSN, kmsg: KeyedMessage)
    requires j.WF()
    requires j.CanFollow(base.seqEnd)
    requires lsn == if j.IsEmpty() then base.seqEnd else j.seqEnd
    requires kmsg.message.Define?;  // we'll have to get smarter if we want to generalize.
    ensures j.Concat(MsgHistoryMod.Singleton(lsn, kmsg)).CanFollow(base.seqEnd)
    ensures j.ApplyToInterp(base).mi[kmsg.key := kmsg.message]
      == j.Concat(MsgHistoryMod.Singleton(lsn, kmsg)).ApplyToInterp(base).mi
  {
    var j' := j.Concat(MsgHistoryMod.Singleton(lsn, kmsg));
    ApplyToInterpRecursiveIsPrune(j', base, j'.Len()-1);
    assert j'.PruneTail(j'.seqStart + j.Len()) == j;  // trigger
    assert j'.ApplyToInterp(base).mi == j'.ApplyToInterpRecursive(base, j'.Len()-1).mi[kmsg.key := kmsg.message];  // trigger
  }

  lemma JournalAssociativity(x: MapAdt, y: Journal, z: Journal)
    requires y.WF()
    requires z.WF()
    requires y.CanFollow(x.seqEnd)
    requires z.CanFollow(SeqEndFor(x, y))
    ensures z.ApplyToInterp(y.ApplyToInterp(x)) == y.Concat(z).ApplyToInterp(x);
    decreases z.Len();
  {
    if !z.IsEmpty() {
      var ztrim := z.PruneTail(z.seqEnd - 1);
      calc {
        ztrim.ApplyToInterp(y.ApplyToInterp(x));
          { JournalAssociativity(x, y, ztrim); }
        y.Concat(ztrim).ApplyToInterp(x);
      }

        var lsn := z.seqStart + z.Len() - 1;
        var key := z.msgs[lsn].key;
        var oldMessage := y.ApplyToInterp(x).mi[key];
        var newMessage := z.msgs[lsn].message;

      calc {
        z.ApplyToInterp(y.ApplyToInterp(x)).mi;
        z.ApplyToInterpRecursive(y.ApplyToInterp(x), z.Len()).mi;
        {
          assert z.Len() != 0;  // open the defn
        }
        z.ApplyToInterpRecursive(y.ApplyToInterp(x), z.Len()-1).mi[key := Merge(newMessage, oldMessage)];
        {
          ApplyToInterpRecursiveIsPrune(z, y.ApplyToInterp(x), z.Len() -1);
//          assert z.ApplyToInterpRecursive(y.ApplyToInterp(x), z.Len() -1) ==
//            z.PruneTail(z.seqStart + z.Len() - 1).ApplyToInterpRecursive(y.ApplyToInterp(x), z.Len()-1);
        }
        ztrim.ApplyToInterpRecursive(y.ApplyToInterp(x), z.Len()-1).mi[key := Merge(newMessage, oldMessage)];
        ztrim.ApplyToInterp(y.ApplyToInterp(x)).mi[key := Merge(newMessage, oldMessage)];
          { JournalAssociativity(x, y, ztrim); }
        y.Concat(ztrim).ApplyToInterp(x).mi[key := Merge(newMessage, oldMessage)];

        y.Concat(z).ApplyToInterpRecursive(x, y.Concat(z).Len()-1).mi[key := Merge(newMessage, oldMessage)];
        {
          var yz := y.Concat(z);
          var yzlsn := yz.seqStart + yz.Len() - 1;
          var yzkey := yz.msgs[lsn].key;
          var yzoldMessage := x.mi[key];
          var yznewMessage := yz.msgs[lsn].message;
          assert yzkey == key;
          assert yznewMessage == newMessage;
          assert yzoldMessage == oldMessage;
        }
        y.Concat(z).ApplyToInterpRecursive(x, y.Concat(z).Len()).mi;
        y.Concat(z).ApplyToInterp(x).mi;
      }
    }
  }

//  lemma JournalSplit(j: Journal, lsn: LSN)
//    requires j.WF()
//    requires j.CanPruneTo(lsn)
//    ensures j.PruneTail(lsn).Concat(j.PruneHead(lsn)) == j
//  {
//  }

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
      case QueryStep(key, val) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case PutStep() => {
        assume false; // skip for now
        var j := v.ephemeral.journal;
        var j' := v'.ephemeral.journal;
        var base := v.persistentSuperblock.mapadt;
        var key := uiop.baseOp.req.input.k;
        var val := uiop.baseOp.req.input.v;

        assert j == j.PruneTail(j.Len() + j.seqStart);  // seq trigger
        assert j' == j'.PruneTail(j'.Len() + j'.seqStart);  // seq trigger
        ApplicationConcatenation(base, j, j.seqEnd, KeyedMessage(key, Define(val)));
        assert forall i | v.persistentSuperblock.mapadt.seqEnd<=i<|I(v).versions| :: j'.PruneTail(i) == j.PruneTail(i);  // Rob Power Trigger

        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case CompleteSyncStep() => {
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
      case CommitCompleteStep() => {
        // There are six pieces in play here: the persistent and in-flight superblocks and the ephemeral journals:
        //  _________ __________
        // | psb.map | psb.jrnl |
        //  --------- ----------
        //  ______________ __________
        // | isb.map      | isb.jrnl |
        //  -------------- ----------
        //            ____________________
        //           | eph.jrnl           |
        //            --------------------
        //                 _______________
        //                | eph'.jrnl     |
        //                 ---------------

        forall i | 0<=i<|I(v).versions| ensures
          || I(v').versions[i] == I(v).versions[i]
          || (i < I(v').stableIdx && I(v').versions[i].Forgotten?)
        {
          var psb := v.persistentSuperblock;
          var isb := v.inFlightSuperblock.value;
          assert isb == v'.persistentSuperblock;

          var forgottenVersions' := seq(isb.mapadt.seqEnd, i => CrashTolerantMapSpecMod.Forgotten);
          assert |forgottenVersions'| == isb.mapadt.seqEnd;

          assert i < isb.mapadt.seqEnd <==> I(v').versions[i].Forgotten?;

          if |forgottenVersions'| <= i {
            var refVersion := isb.mapadt;
            var refLsn := refVersion.seqEnd;
            assert refVersion == v'.persistentSuperblock.mapadt;
            assert refVersion == psb.journal.PruneTail(isb.mapadt.seqEnd).ApplyToInterp(psb.mapadt);  // invariant

            var eji := v.ephemeral.journal.PruneTail(i);
            calc {
              I(v').versions[i].asyncState.appv.interp;
                // defn
              v'.ephemeral.journal.PruneTail(i).ApplyToInterp(isb.mapadt);  // isb == v'.psb
                // invariant InvInFlightVersionAgreement
              v'.ephemeral.journal.PruneTail(i).ApplyToInterp(psb.journal.PruneTail(refLsn).ApplyToInterp(psb.mapadt));
                // invariant that ephemeral journal agrees with persistent journal on overlapping stuff
              v'.ephemeral.journal.PruneTail(i).ApplyToInterp(v.ephemeral.journal.PruneTail(psb.SeqEnd()).PruneTail(refLsn).ApplyToInterp(psb.mapadt));
                { assert v.ephemeral.journal.PruneTail(psb.SeqEnd()).PruneTail(refLsn) == v.ephemeral.journal.PruneTail(refLsn); }  // trigger
              v'.ephemeral.journal.PruneTail(i).ApplyToInterp(v.ephemeral.journal.PruneTail(refLsn).ApplyToInterp(psb.mapadt));
              {
                JournalAssociativity(psb.mapadt, v.ephemeral.journal.PruneTail(refLsn), v'.ephemeral.journal.PruneTail(i));
              }
              v.ephemeral.journal.PruneTail(refLsn).Concat(v'.ephemeral.journal.PruneTail(i)).ApplyToInterp(psb.mapadt);
                // InvEphemeralJournalMatchesPersistentJournal
              v.ephemeral.journal.PruneTail(refLsn).Concat(v.ephemeral.journal.PruneHead(refLsn).PruneTail(i)).ApplyToInterp(psb.mapadt);
              v.ephemeral.journal.PruneTail(refLsn).Concat(eji.PruneHead(refLsn)).ApplyToInterp(psb.mapadt);
              { assert v.ephemeral.journal.PruneTail(refLsn) == eji.PruneTail(refLsn); } // trigger
              eji.PruneTail(refLsn).Concat(eji.PruneHead(refLsn)).ApplyToInterp(psb.mapadt);
              {
                assert eji.PruneTail(refLsn).Concat(eji.PruneHead(refLsn)) == eji;  // trigger
//                JournalSplit(eji, refLsn);
              }
              eji.ApplyToInterp(psb.mapadt);
              v.ephemeral.journal.PruneTail(i).ApplyToInterp(psb.mapadt);
                // defn
              I(v).versions[i].asyncState.appv.interp;
            }

//            assert refVersion == VersionsWithForgottenPrefix(isb.mapadt, v'.ephemeral.journal)[refVersion.seqEnd].asyncState.appv.interp;
//            assert refVersion == v'.ephemeral.journal.PruneTail(refVersion.seqEnd).ApplyToInterp(isb.mapadt);
//           
//            var subsumedJournal := v.ephemeral.journal.PruneTail(refVersion.seqEnd);
//            var keptJournal := v.ephemeral.journal.PruneHead(refVersion.seqEnd);
//
//            assert subsumedJournal.CanPruneTo(refVersion.seqEnd);
//            assert subsumedJournal.PruneTail(refVersion.seqEnd).CanFollow(psb.mapadt.seqEnd);
//
//            calc {
//              VersionsWithForgottenPrefix(psb.mapadt, subsumedJournal)[refVersion.seqEnd].asyncState.appv.interp;
//                // just the defn
//              subsumedJournal.PruneTail(refVersion.seqEnd).ApplyToInterp(psb.mapadt);
//              {
//                assert subsumedJournal.IsEmpty() || subsumedJournal.seqEnd == refVersion.seqEnd;
//                assert subsumedJournal.PruneTail(refVersion.seqEnd) == subsumedJournal; // trigger?
//              }
//              subsumedJournal.ApplyToInterp(psb.mapadt);
//              isb.mapadt;
//                { assert v'.ephemeral.journal.PruneTail(refVersion.seqEnd).IsEmpty(); }
//              // refVersion is v'.ephemeral.journal.PruneTail(refVersion.seqEnd).ApplyToInterp(isb.mapadt);
//              refVersion;
//            }
//            assert refVersion == VersionsWithForgottenPrefix(psb.mapadt, subsumedJournal)[refVersion.seqEnd].asyncState.appv.interp;
//            assert refVersion == subsumedJournal.ApplyToInterp(psb.mapadt);
//
//            assert refVersion.seqEnd <= i;
//
//            assert keptJournal.PruneTail(i).CanFollow(refVersion.seqEnd);
//            var j:int := i;
//            calc {
//              I(v).versions[i].asyncState.appv.interp;
//              v.ephemeral.journal.PruneTail(i).ApplyToInterp(psb.mapadt);
//              keptJournal.PruneTail(i).ApplyToInterp(refVersion);
//              v'.ephemeral.journal.PruneTail(i).ApplyToInterp(refVersion);
//              I(v').versions[i].asyncState.appv.interp;
//            }
          }
        }
      
        assert v.persistentSuperblock.SeqEnd() <= v.inFlightSuperblock.value.SeqEnd();
        assert v.persistentSuperblock.SeqEnd() <= v'.persistentSuperblock.SeqEnd();
        assert CrashTolerantMapSpecMod.SpontaneousCommit(I(v), I(v'));
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
    }
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
