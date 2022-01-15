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
    ensures |versions| == SeqEndFor(base.seqEnd, journal)+1
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

  predicate JournalExtendsJournal(jlong: Journal, jshort: Journal, startLsn: LSN)
  {
    && jlong.WF()
    && jshort.WF()
    && jshort.CanFollow(startLsn)
    && jlong.CanFollow(startLsn)
    && jlong.CanPruneTo(SeqEndFor(startLsn, jshort))
    && jlong.PruneTail(SeqEndFor(startLsn, jshort)) == jshort
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
    && ej.CanPruneTo(isb.mapadt.seqEnd)
    // in-flight journal extends persistent journal
    && JournalExtendsJournal(isb.journal, psb.journal, psb.mapadt.seqEnd)
    // Ephemeral journal agrees with in-flight journal
    && JournalExtendsJournal(ej.PruneHead(isb.mapadt.seqEnd), isb.journal, isb.mapadt.seqEnd)
    // in-flight map matches corresponding state in ephemeral world
    && isb.mapadt == ej.PruneTail(isb.mapadt.seqEnd).ApplyToInterp(psb.mapadt)
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
      case QueryStep(key, val) => {
        assert Inv(v');
      }
      case PutStep() => {
        assume false;
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
    requires z.CanFollow(SeqEndFor(x.seqEnd, y))
    ensures z.ApplyToInterp(y.ApplyToInterp(x)) == y.Concat(z).ApplyToInterp(x);
    decreases z.Len();
  {
    if !z.IsEmpty() {
      var ztrim := z.PruneTail(z.seqEnd - 1);
      var yz := y.Concat(z);

      JournalAssociativity(x, y, ztrim);
      ApplyToInterpRecursiveIsPrune(z, y.ApplyToInterp(x), z.Len()-1);
      assert yz.PruneTail(yz.seqEnd - 1) == y.Concat(ztrim); // trigger
      ApplyToInterpRecursiveIsPrune(yz, x, yz.Len()-1);
    }
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
      case QueryStep(key, val) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
      case PutStep() => {
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
            var eji := v.ephemeral.journal.PruneTail(i);

            // Here's a calc, but commented to use a shorthand algebra:
            // Let + be ApplyToInterp and Concat (they're associative).
            // var im:=v.inFlightSuperblock.value.mapadt, pm:=v.persistentSuperblock.mapadt, R:=im.seqEnd
            // I(v')
            // im+ej'[..i]
            // im+ej[..i][R..]
            // InvInFlightVersionAgreement
            // (pm+ej[..R])+ej[..i][R..]
            JournalAssociativity(v.persistentSuperblock.mapadt, ej.PruneTail(refLsn), ej.PruneTail(i).PruneHead(refLsn));
            // pm+(ej[..R]+ej[..i][R..])
            assert ej.PruneTail(refLsn) == ej.PruneTail(i).PruneTail(refLsn);  // because R <= i; smaller i are Forgotten
            // pm+(ej[..i][..R]+ej[..i][R..])
            assert eji.PruneTail(refLsn).Concat(eji.PruneHead(refLsn)) == eji;  // trigger
            // pm+ej[..i]
            // I(v)
          }
        }
      
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop); // case boilerplate
      }
    }
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
