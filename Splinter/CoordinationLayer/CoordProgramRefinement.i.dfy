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

  function I(v: CoordProgramMod.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()
    else if MapIsFresh(v)
      then v.ephemeral.journal.AsCrashTolerantMapSpec(v.persistentSuperblock.mapadt)
      else v.persistentSuperblock.journal.AsCrashTolerantMapSpec(v.persistentSuperblock.mapadt)
    
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
    assert JournalInterpTypeMod.Mkfs().SyncReqsAt(0) == {}; // trigger set comprehension
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
      case ReqSyncStep(syncReqId) => {
        assert Inv(v');
      }
      case CompleteSyncStep(syncReqId) => {
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
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
      case RecoverStep(puts) => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          CrashTolerantMapSpecMod.NoopOp);
      }
      case QueryStep(key, val) => {
        assert uiop.OperateOp?;
        assert uiop.baseOp.ExecuteOp?;
        assert Query(v, v', uiop, key, val);
        assert CrashTolerantMapSpecMod.async.DoExecute(
          Async.Variables(Last(I(v).versions).asyncState, v.ephemeral.journal.reqProgress),
          Async.Variables(Last(I(v').versions).asyncState, v.ephemeral.journal.reqProgress),
          uiop.baseOp.req, uiop.baseOp.reply);
        assert CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
          uiop);
//        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'),
//          CrashTolerantMapSpecMod.NoopOp);
      }
      case PutStep() => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
//    case JournalInternalStep(sk) => { assert Inv(v'); }
//    case SplinterTreeInternalStep(sk) => { assert Inv(v'); }
      case ReqSyncStep(syncReqId) => {
        assume false;
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), uiop);
      }
      case CompleteSyncStep(syncReqId) => {
        assume false;
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
