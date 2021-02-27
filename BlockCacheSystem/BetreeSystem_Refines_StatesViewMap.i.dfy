// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BetreeSystem_Refines_StatesViewPivotBetree.i.dfy"
include "../PivotBetree/StatesViewPivotBetree_Refines_StatesViewMap.i.dfy"

//
// Composes the two refinements:
//
//   BetreeSystem -> StatesView PivotBetree
//   StatesView PivotBetree -> StatesView Map
//
// To yield
//
//   BetreeSystem -> StatesView Map
//

module BetreeSystem_Refines_StatesViewMap {
  import A = BetreeSystem
  import B = StatesViewPivotBetree
  import C = StatesViewMap

  import Ref_A = BetreeSystem_Refines_StatesViewPivotBetree
  import Ref_B = StatesViewPivotBetree_Refines_StatesViewMap
  
  import opened ViewOp

  function I(s: A.Variables) : C.Variables
  requires A.Inv(s)
  {
    Ref_B.I(
      Ref_A.I(s)
    )
  }

  lemma RefinesInit(s: A.Variables, loc: Loc)
    requires A.Init(s, loc)
    ensures A.Inv(s)
    ensures C.Init(I(s), loc)
  {
    Ref_A.RefinesInit(s, loc);
    Ref_B.RefinesInit(
      Ref_A.I(s),
      loc);
  }

  lemma RefinesNext(s: A.Variables, s': A.Variables, vop: VOp)
    requires A.Inv(s)
    requires A.Next(s, s', vop)
    ensures A.Inv(s')
    ensures C.Next(I(s), I(s'), vop)
  {
    Ref_A.RefinesNext(s, s', vop);
    Ref_B.RefinesNext(
      Ref_A.I(s),
      Ref_A.I(s'),
      vop);
  }
}
