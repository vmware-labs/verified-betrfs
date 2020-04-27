include "StatesViewMap.i.dfy"
include "JournalView.i.dfy"
include "../MapSpec/TSJMap.i.dfy"

// Combine StatesView and JournalView.

module CompositeView {
  import StatesViewMap
  import JournalView
  import SM = MapSpec
  import opened ViewOp
  import opened Options
  import opened Journal
  import opened Sequences
  import TSJ = TSJMap

  import UI

  datatype Constants = Constants(
      tsm: StatesViewMap.Constants,
      jc: JournalView.Constants)

  datatype Variables = Variables(
      tsm: StatesViewMap.Variables,
      jc: JournalView.Variables)

  datatype Step = Step(vop: VOp) 

  predicate Init(k: Constants, s: Variables)
  {
    exists loc ::
      && StatesViewMap.Init(k.tsm, s.tsm, loc)
      && JournalView.Init(k.jc, s.jc, loc)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && StatesViewMap.Next(k.tsm, s.tsm, s'.tsm, vop)
    && JournalView.Next(k.jc, s.jc, s'.jc, vop)
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

  function Ik(k: Constants) : TSJ.Constants
  {
    TSJ.Constants(k.tsm.k)
  }

  function I(k: Constants, s: Variables) : TSJ.Variables
  requires s.jc.persistentLoc in s.tsm.disk
  {
    TSJ.Variables(
      s1(s),
      s2(s),
      s3(s),
      s.jc.j1,
      s.jc.j2,
      s.jc.j3,
      s.jc.j_gamma,
      s.jc.j_delta,
      s.jc.syncReqs
    )
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

    && TSJ.Inv(Ik(k), I(k, s))
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
  {
    SM.InitImpliesInv(k.tsm.k, s1(s));
    TSJ.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma Move3PreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Move3(k.jc, s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    /*assert SM.Inv(k.tsm.k, s1(s'));
    assert SM.Inv(k.tsm.k, s2(s'));
    assert SM.Inv(k.tsm.k, s3(s'));
    assert s.tsm.ephemeralState.value == s3(s) == I(k,s).s3;
    assert s'.tsm.ephemeralState.value == s3(s') == I(k,s').s3;
    assert k.tsm.k == Ik(k).k;
    assert SM.Next(k.tsm.k, s.tsm.ephemeralState.value, s'.tsm.ephemeralState.value, vop.uiop);
    assert SM.Next(Ik(k).k, I(k,s).s3, I(k,s').s3, vop.uiop);
    assert TSJ.Move3(Ik(k), I(k, s), I(k, s'), uiop);*/
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move3Step);
    TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma ReplayPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Replay(k.jc, s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(k.tsm, s.tsm, s'.tsm, vop)
  requires Inv(k, s)
  ensures Inv(k, s')
  ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ReplayStep(vop.uiop));
    TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma AdvancePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    if JournalView.Move3(k.jc, s.jc, s'.jc, vop) {
      Move3PreservesInv(k, s, s', vop, uiop);
    } else if JournalView.Replay(k.jc, s.jc, s'.jc, vop) {
      ReplayPreservesInv(k, s, s', vop, uiop);
    }
  }

  lemma FreezePreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.FreezeOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert JournalView.Move2to3(k.jc, s.jc, s'.jc, vop);
    assert StatesViewMap.Freeze(k.tsm, s.tsm, s'.tsm, vop);

    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move2to3Step);
    TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);

    /*assert s.jc.frozenLoc != Some(s.jc.persistentLoc);
    if s.tsm.persistentLoc.Some? {
      if s.tsm.frozenLoc == Some(s.jc.persistentLoc) {
        assert s.tsm.frozenLoc != s.jc.frozenLoc;
      }
      assert s.jc.persistentLoc == s.tsm.persistentLoc.value;
    }*/
  }

  lemma CrashPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires vop.CrashOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  ensures TSJ.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    assert s1(s) == s1(s') == s2(s') == s3(s');
    assert JournalView.Crash(k.jc, s.jc, s'.jc, vop);
    assert StatesViewMap.Crash(k.tsm, s.tsm, s'.tsm, vop);

    assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.CrashStep);
    TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(k, s, s', vop, uiop)
  requires Inv(k, s)
  ensures Inv(k, s')
  {
    var tsm_step :| StatesViewMap.NextStep(k.tsm, s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalView.NextStep(k.jc, s.jc, s'.jc, vop, jc_step);

    match vop {
      case SendPersistentLocOp(loc) => { }
      case AdvanceOp(_, _) => {
        AdvancePreservesInv(k, s, s', vop, uiop);
      }
      case CrashOp => {
        CrashPreservesInv(k, s, s', vop, uiop);
      }
      case FreezeOp => {
        FreezePreservesInv(k, s, s', vop, uiop);
      }
      case StatesInternalOp => { }
      case JournalInternalOp => {
        assert s.tsm == s'.tsm;
        if JournalView.Move1to2(k.jc, s.jc, s'.jc, vop) {
          assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.Move1to2Step);
          TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
          assert Inv(k, s');
        }
        else if JournalView.ExtendLog1(k.jc, s.jc, s'.jc, vop) {
          assert Inv(k, s');
        }
        else if JournalView.ExtendLog2(k.jc, s.jc, s'.jc, vop) {
          assert TSJ.NextStep(Ik(k), I(k, s), I(k, s'), uiop, TSJ.ExtendLog2Step);
          TSJ.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
          assert Inv(k, s');
        }
        else {
          assert s.jc == s'.jc;
        }
      }
      case SendFrozenLocOp(loc) => { }
      case CleanUpOp => {
        assert JournalView.CleanUp(k.jc, s.jc, s'.jc, vop);
        assert StatesViewMap.ForgetOld(k.tsm, s.tsm, s'.tsm, vop);
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
