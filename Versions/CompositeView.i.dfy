include "StatesViewMap.i.dfy"
include "JournalView.i.dfy"

// Combine StatesView and JournalView.

module CompositeView {
  import StatesViewMap
  import JournalView
  import SM = MapSpec
  import opened ViewOp
  import opened Options
  import opened Journal
  import opened Sequences

  import UI

  datatype Variables = Variables(
      tsm: StatesViewMap.Variables,
      jc: JournalView.Variables)

  datatype Step = Step(vop: VOp) 

  predicate Init(s: Variables)
  {
    exists loc ::
      && StatesViewMap.Init(s.tsm, loc)
      && JournalView.Init(s.jc, loc)
  }

  predicate NextStep(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  {
    && StatesViewMap.Next(s.tsm, s'.tsm, vop)
    && JournalView.Next(s.jc, s'.jc, vop)
    && VOpAgreesUIOp(vop, uiop)
  }

  predicate Next(s: Variables, s': Variables, uiop: UI.Op)
  {
    exists step: Step :: NextStep(s, s', step.vop, uiop)
  }

  /// Invariant definition

  predicate Inv(s: Variables)
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
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
  }

  lemma Move3PreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Move3(s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(s.tsm, s'.tsm, vop)
  requires Inv(s)
  ensures Inv(s')
  {
    /*assert SM.Inv(s1(s'));
    assert SM.Inv(s2(s'));
    assert SM.Inv(s3(s'));
    assert s.tsm.ephemeralState.value == s3(s) == I(s).s3;
    assert s'.tsm.ephemeralState.value == s3(s') == I(s').s3;
    assert SM.Next(s.tsm.ephemeralState.value, s'.tsm.ephemeralState.value, vop.uiop);
    assert SM.Next(I(s).s3, I(s').s3, vop.uiop);
    assert TSJ.Move3(I(s), I(s'), uiop);*/
  }

  lemma ReplayPreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Replay(s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(s.tsm, s'.tsm, vop)
  requires Inv(s)
  ensures Inv(s')
  {
  }

  lemma AdvancePreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  {
    if JournalView.Move3(s.jc, s'.jc, vop) {
      Move3PreservesInv(s, s', vop, uiop);
    } else if JournalView.Replay(s.jc, s'.jc, vop) {
      ReplayPreservesInv(s, s', vop, uiop);
    }
  }

  lemma FreezePreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires vop.FreezeOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  {
    assert JournalView.Move2to3(s.jc, s'.jc, vop);
    assert StatesViewMap.Freeze(s.tsm, s'.tsm, vop);

    /*assert s.jc.frozenLoc != Some(s.jc.persistentLoc);
    if s.tsm.persistentLoc.Some? {
      if s.tsm.frozenLoc == Some(s.jc.persistentLoc) {
        assert s.tsm.frozenLoc != s.jc.frozenLoc;
      }
      assert s.jc.persistentLoc == s.tsm.persistentLoc.value;
    }*/
  }

  lemma CrashPreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires vop.CrashOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  {
    assert JournalView.Crash(s.jc, s'.jc, vop);
    assert StatesViewMap.Crash(s.tsm, s'.tsm, vop);
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  {
    var tsm_step :| StatesViewMap.NextStep(s.tsm, s'.tsm, vop, tsm_step);
    var jc_step :| JournalView.NextStep(s.jc, s'.jc, vop, jc_step);

    match vop {
      case SendPersistentLocOp(loc) => { }
      case AdvanceOp(_, _) => {
        AdvancePreservesInv(s, s', vop, uiop);
      }
      case CrashOp => {
        CrashPreservesInv(s, s', vop, uiop);
      }
      case FreezeOp => {
        FreezePreservesInv(s, s', vop, uiop);
      }
      case StatesInternalOp => { }
      case JournalInternalOp => {
        assert s.tsm == s'.tsm;
        if JournalView.Move1to2(s.jc, s'.jc, vop) {
          assert Inv(s');
        }
        else if JournalView.ExtendLog1(s.jc, s'.jc, vop) {
          assert Inv(s');
        }
        else if JournalView.ExtendLog2(s.jc, s'.jc, vop) {
          assert Inv(s');
        }
        else {
          assert s.jc == s'.jc;
        }
      }
      case SendFrozenLocOp(loc) => { }
      case CleanUpOp => {
        assert JournalView.CleanUp(s.jc, s'.jc, vop);
        assert StatesViewMap.ForgetOld(s.tsm, s'.tsm, vop);
        assert Inv(s');
      }
      case PushSyncOp(id) => { }
      case PopSyncOp(id) => { }
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UI.Op)
  requires Next(s, s', uiop)
  requires Inv(s)
  ensures Inv(s')
  {
    var step: Step :| NextStep(s, s', step.vop, uiop);
    NextStepPreservesInv(s, s', step.vop, uiop);
  }
}
