// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree_Refines_Map.i.dfy"
include "StatesViewPivotBetree.i.dfy"
include "../Versions/StatesViewMap.i.dfy"

//
// Lifts the refinement:
//
//   PivotBetree -> Map
//
// to
//
//   StatesView PivotBetree -> StatesView Map
//
// via the StatesView functor
//

module StatesViewPivotBetree_Refines_StatesViewMap {
  import A = StatesViewPivotBetree
  import B = StatesViewMap
  import Ref = PivotBetree_Refines_Map
  import UI
  import opened ViewOp
  import opened Options
 
  function IDisk(disk: imap<Loc, A.SM.Variables>) : imap<Loc, B.SM.Variables>
  {
    imap loc | loc in disk && A.SM.Inv(disk[loc])
      :: Ref.I(disk[loc])
  }

  function IOptState(state: Option<A.SM.Variables>) : Option<B.SM.Variables>
  requires state.Some? ==> A.SM.Inv(state.value)
  {
    if state.Some? then Some(Ref.I(state.value)) else None
  }
  
  function I(s: A.Variables) : B.Variables
    requires A.Inv(s)
  {
    B.Variables(
      IDisk(s.disk),
      s.persistentLoc,
      s.frozenLoc,
      IOptState(s.frozenState),
      IOptState(s.ephemeralState))
  }

  lemma RefinesInit(s: A.Variables, loc: Loc)
    requires A.Init(s, loc)
    ensures A.Inv(s)
    ensures B.Init(I(s), loc)
  {
    A.SM.InitImpliesInv(s.disk[loc]);
    Ref.RefinesInit(s.disk[loc]);
  }

  lemma RefinesNextStep(s: A.Variables, s': A.Variables, vop: VOp, step: A.Step)
    requires A.Inv(s)
    requires A.NextStep(s, s', vop, step)
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), vop)
  {
    A.NextPreservesInv(s, s', vop);
    match step {
      case ObtainPersistentLocStep => {
        assert B.NextStep(I(s), I(s'), vop, B.ObtainPersistentLocStep);
      }
      case AdvanceStep => {
        Ref.RefinesNext(
          s.ephemeralState.value,
          s'.ephemeralState.value,
          vop.uiop);
        assert B.NextStep(I(s), I(s'), vop, B.AdvanceStep);
      }
      case CrashStep => {
        assert B.NextStep(I(s), I(s'), vop, B.CrashStep);
      }
      case FreezeStep => {
        assert B.NextStep(I(s), I(s'), vop, B.FreezeStep);
      }
      case DiskChangeStep => {
        assert B.NextStep(I(s), I(s'), vop, B.DiskChangeStep);
      }
      case ProvideFrozenLocStep => {
        assert B.NextStep(I(s), I(s'), vop, B.ProvideFrozenLocStep);
      }
      case ForgetOldStep => {
        assert B.NextStep(I(s), I(s'), vop, B.ForgetOldStep);
      }
      case StutterStep => {
        assert B.NextStep(I(s), I(s'), vop, B.StutterStep);
      }
    }
  }

  lemma RefinesNext(s: A.Variables, s': A.Variables, vop: VOp)
    requires A.Inv(s)
    requires A.Next(s, s', vop)
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), vop)
  {
    var step :| A.NextStep(s, s', vop, step);
    RefinesNextStep(s, s', vop, step);
  }
}
