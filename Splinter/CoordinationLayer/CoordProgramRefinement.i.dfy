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

  // Stitch together a base map, a journal, and the specified ephemeral request state.
  function IStitch(base: MapAdt, journal: Journal, progress: Async.EphemeralState, syncReqs: SyncReqs) : CrashTolerantMapSpecMod.Variables
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    // TODO suspicious that 0 is always the stable idx; that can't survive
    // journal truncation.
    CrashTolerantMapSpecMod.Variables(journal.VersionsFromBase(base), progress, syncReqs, 0)
  }

  function I(v: CoordProgramMod.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()
    else if v.ephemeral.Known?
      then IStitch(v.persistentSuperblock.mapadt, v.ephemeral.journal, v.ephemeral.progress, v.ephemeral.syncReqs)
      else IStitch(v.persistentSuperblock.mapadt, v.persistentSuperblock.journal,
        Async.InitEphemeralState(), map[])
  }

  predicate InvLSNTracksPersistentWhenJournalEmpty(v: CoordProgramMod.Variables)
  {
    // We need this extra condition to ensure that, when the ephemeral journal
    // is empty, the ephemeral map indeed matches the disk -- otherwise we won't
    // assign the right lsn to new puts.
    && (v.ephemeral.Known? && v.ephemeral.journal.msgSeq.IsEmpty() ==>
        v.ephemeral.mapadt.seqEnd == v.persistentSuperblock.mapadt.seqEnd
      )
  }

  predicate InvInFlightProperties(v: CoordProgramMod.Variables)
  {
    v.inFlightSuperblock.Some? ==>
      && v.ephemeral.Known?
      && v.ephemeral.journal.CanPruneTo(v.inFlightSuperblock.value.mapadt.seqEnd)
  }

  predicate Inv(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && (v.ephemeral.Known? ==>
      // Interpret ephemeral state by stitching ephemeral journal (which
      // invariantly matches ephemeral mapadt) with persistent mapadt (which
      // it can follow exactly without beheading).
      && v.ephemeral.journal.CanFollow(v.persistentSuperblock.mapadt.seqEnd)
      && InvLSNTracksPersistentWhenJournalEmpty(v)
      )
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
        assert Inv(v');
      }
      case CommitCompleteStep() => {
        assert Inv(v');
      }
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
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
      case RecoverStep(puts) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
      case QueryStep(key, val) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          uiop);
      }
      case PutStep() => {
//        assert 0<|I(v').versions|;
        var j := v.ephemeral.journal;
        var j' := v'.ephemeral.journal;
        var base := v.persistentSuperblock.mapadt;
        var base' := v'.persistentSuperblock.mapadt;
//        var s1 := j'.PruneTail(NextLSN(v)).VersionsFromBase(base');
//        var s2 := DropLast(j'.VersionsFromBase(base'));
//        assert |s1| == |s2|;

        // Rob-style SuperTrigger for some sequence rearrangement identity:
        assert forall i | 0<=i<|DropLast(j'.VersionsFromBase(base'))| ::
          var seqStart := j'.msgSeq.seqStart;
          j'.PruneTail(NextLSN(v)).PruneTail(i + seqStart) == j'.PruneTail(i + seqStart);

//        forall i | 0<=i<|s1| ensures s1[i]==s2[i] {
////          var seqStart := j'.msgSeq.seqStart;
////          assert seqStart == j'.PruneTail(NextLSN(v)).msgSeq.seqStart;
////          calc {
////            j'.PruneTail(NextLSN(v)).PruneTail(i + seqStart);
////            j'.PruneTail(i + seqStart);
////          }
//        }
//        calc {
//          v'.ephemeral.journal.PruneTail(NextLSN(v)).VersionsFromBase(v'.persistentSuperblock.mapadt);
//          DropLast(v'.ephemeral.journal.VersionsFromBase(v'.persistentSuperblock.mapadt));
//        }
        assert v.ephemeral.journal == v'.ephemeral.journal.PruneTail(NextLSN(v));
//        calc {
//          I(v).versions;
//          v.ephemeral.journal.VersionsFromBase(v.persistentSuperblock.mapadt);
//          v.ephemeral.journal.VersionsFromBase(v'.persistentSuperblock.mapadt);
//            { assert v.ephemeral.journal == v'.ephemeral.journal.PruneTail(NextLSN(v)); }
//          v'.ephemeral.journal.PruneTail(NextLSN(v)).VersionsFromBase(v'.persistentSuperblock.mapadt);
//          DropLast(v'.ephemeral.journal.VersionsFromBase(v'.persistentSuperblock.mapadt));
//          DropLast(I(v').versions);
//        }
        var key := uiop.baseOp.req.input.k;
        var val := uiop.baseOp.req.input.v;
        var singleton := MsgHistoryMod.Singleton(NextLSN(v), KeyedMessage(key, Define(val)));
        assert CrashTolerantMapSpecMod.OptionallyAppendVersion(I(v), I(v'));

        assert j.PruneTail(j.msgSeq.seqEnd).msgSeq == j'.PruneTail(j.msgSeq.seqEnd).msgSeq; // seq assembly trigger
        assert j'.PruneTail(j'.msgSeq.seqEnd) == j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton);  // seq assembly trigger
        var outerbase := JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp;
        var outer := outerbase.Put(key, Define(val));
        var inner := JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton)).asyncState.appv.interp;

        assert j'.PruneTail(j.msgSeq.seqEnd).msgSeq.seqEnd == j.msgSeq.seqEnd;
        assert JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp.seqEnd
          == j.msgSeq.seqEnd;
        assert inner.seqEnd
          == j.msgSeq.seqEnd + 1;
        assert j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton).msgSeq.seqEnd == j.msgSeq.seqEnd + 1;
        assert inner.seqEnd == j.msgSeq.seqEnd + 1;

        assert outer.seqEnd == inner.seqEnd;

        forall k
          ensures outer.mi[k] == inner.mi[k]
        {

          assert InterpMod.AnyKey(k); // trigger
          if k == key {
//            assert outer.mi[k] == Define(val);
            assert inner == JournalInterpTypeMod.VersionFor(base', j.Concat(singleton)).asyncState.appv.interp;
            calc {
              inner.mi[k];
              j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton).msgSeq.ApplyToInterp(base').mi[k];
              {
                var oldMessage := j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton).msgSeq.ApplyToInterpRecursive(base', )
              }
              Merge(oldMessage, newMessage);
            }
            assert Define(val) == inner.mi[k];
          } else {
//            assert outer.mi[k] == outerbase.mi[k];
            assert outerbase.mi[k] == inner.mi[k];
          }
        }
        calc {
          JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp.Put(key, Define(val));
            //here
          JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd).Concat(singleton)).asyncState.appv.interp;
          JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j'.msgSeq.seqEnd)).asyncState.appv.interp;
        }
        calc {
          Last(I(v).versions).asyncState.appv.interp.Put(key, Define(val));
//          Last(j.VersionsFromBase(base)).asyncState.appv.interp.Put(key, Define(val));
//          JournalInterpTypeMod.VersionFor(base, j.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp.Put(key, Define(val));
//          JournalInterpTypeMod.VersionFor(base, j'.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp.Put(key, Define(val));
//          JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j.msgSeq.seqEnd)).asyncState.appv.interp.Put(key, Define(val));
//          JournalInterpTypeMod.VersionFor(base', j'.PruneTail(j'.msgSeq.seqEnd)).asyncState.appv.interp;
//          Last(j'.VersionsFromBase(base')).asyncState.appv.interp;
          Last(I(v').versions).asyncState.appv.interp;
        }
        assert Last(I(v').versions).asyncState.appv.interp == Last(I(v).versions).asyncState.appv.interp.Put(key, Define(val));
        assert MapSpecMod.Put(
          Last(I(v).versions).asyncState.appv,
          Last(I(v').versions).asyncState.appv,
          key, val);

        assume Async.DoExecute( // TODO darn it
          Async.Variables(Last(I(v).versions).asyncState, I(v).asyncEphemeral),
          Async.Variables(Last(I(v').versions).asyncState, I(v').asyncEphemeral),
          uiop.baseOp.req,
          uiop.baseOp.reply);
        assert Async.NextStep(
          Async.Variables(Last(I(v).versions).asyncState, I(v).asyncEphemeral),
          Async.Variables(Last(I(v').versions).asyncState, I(v').asyncEphemeral),
          uiop.baseOp);
        assert CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep() => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
      case CompleteSyncStep() => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
      case FreezeJournalStep(newFrozenLSN) => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
      case FreezeMapAdtStep() => {
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
      case CommitStartStep(seqBoundary) => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
      case CommitCompleteStep() => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
    }
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
