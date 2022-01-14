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

  function VersionsFromBase(base: InterpMod.Interp, journal: Journal) : seq<CrashTolerantMapSpecMod.Version>
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    var numVersions := journal.Len()+1;
    seq(numVersions, i requires 0 <= i < numVersions => 
      var interp := InterpsFromBase(base, journal)[i];
      CrashTolerantMapSpecMod.Version(Async.PersistentState(MapSpecMod.Variables(interp))))
  }

  // Stitch together a base map, a journal, and the specified ephemeral request state.
  function IStitch(base: MapAdt, journal: Journal, progress: Async.EphemeralState, syncReqs: SyncReqs) : CrashTolerantMapSpecMod.Variables
    requires journal.WF()
    requires journal.CanFollow(base.seqEnd)
  {
    CrashTolerantMapSpecMod.Variables(VersionsFromBase(base, journal), progress, syncReqs, 0)
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
    && (v.ephemeral.Known? && v.ephemeral.journal.IsEmpty() ==>
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
        var j := v.ephemeral.journal;
        var j' := v'.ephemeral.journal;
        var base := v.persistentSuperblock.mapadt;
        var key := uiop.baseOp.req.input.k;
        var val := uiop.baseOp.req.input.v;

        assert j == j.PruneTail(j.Len() + j.seqStart);  // seq trigger
        assert j' == j'.PruneTail(j'.Len() + j'.seqStart);  // seq trigger
        ApplicationConcatenation(base, j, j.seqEnd, KeyedMessage(key, Define(val)));
        assert forall i | 0<=i<|I(v).versions| :: j'.PruneTail(i + j.seqStart) == j.PruneTail(i + j.seqStart);  // Rob Power Trigger
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
