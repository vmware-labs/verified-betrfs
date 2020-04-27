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

  function Ik(k: A.Constants) : C.Constants {
    Ref_B.Ik(Ref_A.Ik(k))
  }

  function I(k: A.Constants, s: A.Variables) : C.Variables
  requires A.Inv(k, s)
  {
    Ref_B.I(
      Ref_A.Ik(k),
      Ref_A.I(k, s)
    )
  }

  lemma RefinesInit(k: A.Constants, s: A.Variables, loc: Loc)
    requires A.Init(k, s, loc)
    ensures A.Inv(k, s)
    ensures C.Init(Ik(k), I(k, s), loc)
  {
    Ref_A.RefinesInit(k, s, loc);
    Ref_B.RefinesInit(
      Ref_A.Ik(k),
      Ref_A.I(k, s),
      loc);
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s': A.Variables, vop: VOp)
    requires A.Inv(k, s)
    requires A.Next(k, s, s', vop)
    ensures A.Inv(k, s')
    ensures C.Next(Ik(k), I(k, s), I(k, s'), vop)
  {
    Ref_A.RefinesNext(k, s, s', vop);
    Ref_B.RefinesNext(
      Ref_A.Ik(k),
      Ref_A.I(k, s),
      Ref_A.I(k, s'),
      vop);
  }
}
