include "../IOSystem.s.dfy"
include "../ProofObligations.s.dfy"
include "CoordProgramMod.i.dfy"

// This module shows refinement of CoordProgram to CrashTolerantMapSpecMod,
// thereby functioning as the top layer in a refinement stack for program
// models in refinement layers below.
module CoordProgramRefinement {
  import opened CoordProgramMod
  import MapSpecMod

  function I(v: CoordProgramMod.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !Inv(v)
    then CrashTolerantMapSpecMod.InitState()
    else if v.phase.SuperblockUnknown?
      then v.stableSuperblock.journal.AsCrashTolerantMapSpec(v.stableSuperblock.mapadt)
      else v.journal.AsCrashTolerantMapSpec(v.mapadt)
    
  }

  predicate Inv(v: CoordProgramMod.Variables)
  {
    && v.WF()
    && v.stableSuperblock.mapadt.seqEnd == v.stableSuperblock.journal.msgSeq.seqStart
    && (!v.phase.SuperblockUnknown? ==>
      && v.mapadt.seqEnd == v.journal.msgSeq.seqStart
    )
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
      case RecoverStep(puts) => {
        assert Inv(v'); // here
      }
      case QueryStep(key, val) => {
        assert Inv(v');
      }
      case PutStep() => {
        assert Inv(v'); // here
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
        assert Inv(v'); // here
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
    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }
}
