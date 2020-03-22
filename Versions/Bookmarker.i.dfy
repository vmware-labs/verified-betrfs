include "TristateMap.i.dfy"
include "JournalChain.i.dfy"

// Combine TriStateMap and JournalChain.

module Bookmarker {
  import TriStateMap
  import JournalChain
  import SM = MapSpec
  import opened VersionOp
  import opened Options
  import opened Journal
  import opened Sequences

  import UI

  datatype Constants = Constants(
      tsm: TriStateMap.Constants,
      jc: JournalChain.Constants)

  datatype Variables = Variables(
      tsm: TriStateMap.Variables,
      jc: JournalChain.Variables)

  datatype Step = Step(vop: VOp) 

  predicate Init(k: Constants, s: Variables)
  {
    && TriStateMap.Init(k.tsm, s.tsm)
    && JournalChain.Init(k.jc, s.jc)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && TriStateMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalChain.Next(k.jc, s.jc, s'.jc, vop)
    && VOpAgreesUIOp(vop, uiop)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  {
    exists step: Step :: NextStep(k, s, s', step.vop, uiop)
  }

  /// Invariant definition

  function s1(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    s.tsm.disk[s.jc.persistentLoc]
  }

  function s2(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    if s.tsm.frozenState.Some? then
      s.tsm.frozenState.value
    else
      s1(s)
  }

  function s3(s: Variables) : SM.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    if s.tsm.ephemeralState.Some? then
      s.tsm.ephemeralState.value
    else
      s1(s)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && (s.jc.frozenLoc.Some? ==>
      && s.tsm.frozenLoc == s.jc.frozenLoc
    )
    && (s.tsm.persistentLoc.Some? ==>
      || s.jc.persistentLoc == s.tsm.persistentLoc.value
      || Some(s.jc.persistentLoc) == s.jc.frozenLoc
    )
    && (s.tsm.frozenLoc.Some? ==>
      && s.tsm.frozenLoc.value in s.tsm.disk
      && s.tsm.frozenState.Some?
      && s.tsm.disk[s.tsm.frozenLoc.value]
          == s.tsm.frozenState.value
    )
    && (s.tsm.frozenState.Some? ==>
      s.tsm.ephemeralState.Some?
    )
    && (s.tsm.ephemeralState.Some? ==>
      s.tsm.persistentLoc.Some?
    )
    && s.jc.persistentLoc in s.tsm.disk

    && SM.Inv(k.tsm.k, s1(s))
    && SM.Inv(k.tsm.k, s2(s))
    && SM.Inv(k.tsm.k, s3(s))

    //&& advances(k.tsm.k, s1(s), s.jc.j_gamma, s2(s), s.jc.j2)
    //&& advances(k.tsm.k, s2(s), s.jc.j2 + s.jc.j_delta, s3(s), s.jc.j3)
  }

  lemma InitImpliesInv(k: Constants, s: Variables, s': Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    SM.InitImpliesInv(k.tsm.k, s1(s));
  }

  lemma Move3PreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires JournalChain.Move3(k.jc, s.jc, s'.jc, vop)
  requires TriStateMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
  }

  lemma ReplayPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires JournalChain.Replay(k.jc, s.jc, s'.jc, vop)
  requires TriStateMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
  }

  lemma AdvancePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    if JournalChain.Move3(k.jc, s.jc, s'.jc, vop) {
      Move3PreservesInv(k, s, s', vop, uiop);
    } else if JournalChain.Replay(k.jc, s.jc, s'.jc, vop) {
      ReplayPreservesInv(k, s, s', vop, uiop);
    }
  }

  lemma FreezePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.FreezeOp?
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    assert JournalChain.Move2to3(k.jc, s.jc, s'.jc, vop);
    assert TriStateMap.Freeze(k.tsm, s.tsm, s'.tsm, vop);

    /*assert s.jc.frozenLoc != Some(s.jc.persistentLoc);
    if s.tsm.persistentLoc.Some? {
      if s.tsm.frozenLoc == Some(s.jc.persistentLoc) {
        assert s.tsm.frozenLoc != s.jc.frozenLoc;
      }
      assert s.jc.persistentLoc == s.tsm.persistentLoc.value;
    }*/
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var tsm_step :| TriStateMap.NextStep(k.tsm, s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalChain.NextStep(k.jc, s.jc, s'.jc, vop, jc_step);

    match vop {
      case SendPersistentLocOp(loc) => { }
      case AdvanceOp(_, _) => {
        AdvancePreservesInv(k, s, s', vop, uiop);
      }
      case CrashOp => {
        assert s1(s) == s1(s') == s2(s') == s3(s');
        assert JournalChain.Crash(k.jc, s.jc, s'.jc, vop);
        assert TriStateMap.Crash(k.tsm, s.tsm, s'.tsm, vop);
      }
      case FreezeOp => {
        FreezePreservesInv(k, s, s', vop, uiop);
      }
      case TristateInternalOp => { }
      case JournalInternalOp => {
        assert s.tsm == s'.tsm;
        if JournalChain.Move1to2(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalChain.ExtendLog1(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalChain.ExtendLog2(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else {
          assert s.jc == s'.jc;
        }
      }
      case SendFrozenLocOp(loc) => { }
      case CleanUpOp => {
        assert JournalChain.CleanUp(k.jc, s.jc, s'.jc, vop);
        assert TriStateMap.ForgetOld(k.tsm, s.tsm, s'.tsm, vop);
        assert Inv(k, s');
      }
      case PushSyncOp(id) => { }
      case PopSyncOp(id) => { }
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UI.Op)
  requires Next(k, s, s', uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var step: Step :| NextStep(k, s, s', step.vop, uiop);
    NextStepPreservesInv(k, s, s', step.vop, uiop);
  }
}
