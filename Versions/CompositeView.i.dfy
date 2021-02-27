// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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

  function I(s: Variables) : TSJ.Variables
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

    && SM.Inv(s1(s))
    && SM.Inv(s2(s))
    && SM.Inv(s3(s))

    && TSJ.Inv(I(s))
  }

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)
  {
    SM.InitImpliesInv(s1(s));
    TSJ.InitImpliesInv(I(s));
  }

  lemma Move3PreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Move3(s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(s.tsm, s'.tsm, vop)
  requires Inv(s)
  ensures Inv(s')
  ensures TSJ.Next(I(s), I(s'), uiop)
  {
    /*assert SM.Inv(s1(s'));
    assert SM.Inv(s2(s'));
    assert SM.Inv(s3(s'));
    assert s.tsm.ephemeralState.value == s3(s) == I(s).s3;
    assert s'.tsm.ephemeralState.value == s3(s') == I(s').s3;
    assert SM.Next(s.tsm.ephemeralState.value, s'.tsm.ephemeralState.value, vop.uiop);
    assert SM.Next(I(s).s3, I(s').s3, vop.uiop);
    assert TSJ.Move3(I(s), I(s'), uiop);*/
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move3Step);
    TSJ.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma ReplayPreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires JournalView.Replay(s.jc, s'.jc, vop)
  requires StatesViewMap.Advance(s.tsm, s'.tsm, vop)
  requires Inv(s)
  ensures Inv(s')
  ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.ReplayStep(vop.uiop));
    TSJ.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma AdvancePreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires vop.AdvanceOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  ensures TSJ.Next(I(s), I(s'), uiop)
  {
    if JournalView.Move3(s.jc, s'.jc, vop) {
      Move3PreservesInv(s, s', vop, uiop);
    } else if JournalView.Replay(s.jc, s'.jc, vop) {
      ReplayPreservesInv(s, s', vop, uiop);
    }
  }

  lemma {:fuel SM.Inv,0} FreezePreservesInv(s: Variables, s': Variables, vop: VOp, uiop: UI.Op)
  requires NextStep(s, s', vop, uiop)
  requires vop.FreezeOp?
  requires VOpAgreesUIOp(vop, uiop)
  requires Inv(s)
  ensures Inv(s')
  ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert JournalView.Move2to3(s.jc, s'.jc, vop);
    assert StatesViewMap.Freeze(s.tsm, s'.tsm, vop);

    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move2to3Step);
    TSJ.NextPreservesInv(I(s), I(s'), uiop);

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
  ensures TSJ.Next(I(s), I(s'), uiop)
  {
    assert s1(s) == s1(s') == s2(s') == s3(s');
    assert JournalView.Crash(s.jc, s'.jc, vop);
    assert StatesViewMap.Crash(s.tsm, s'.tsm, vop);

    assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.CrashStep);
    TSJ.NextPreservesInv(I(s), I(s'), uiop);
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
          assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.Move1to2Step);
          TSJ.NextPreservesInv(I(s), I(s'), uiop);
          assert Inv(s');
        }
        else if JournalView.ExtendLog1(s.jc, s'.jc, vop) {
          assert Inv(s');
        }
        else if JournalView.ExtendLog2(s.jc, s'.jc, vop) {
          assert TSJ.NextStep(I(s), I(s'), uiop, TSJ.ExtendLog2Step);
          TSJ.NextPreservesInv(I(s), I(s'), uiop);
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
