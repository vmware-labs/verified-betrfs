include "../PivotBetree/ThreeStateVersionedPivotBetree_Refines_ThreeStateVersionedMap.i.dfy"
include "BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy"

//
// Composes the two refinements:
//
//   BetreeBlockCacheSystem -> ThreeStateVersioned PivotBetree
//   ThreeStateVersioned PivotBetree -> ThreeStateVersioned Map
//
// To yield
//
//   BetreeBlockCacheSystem -> ThreeStateVersioned Map
//

module BetreeBlockCacheSystem_Refines_ThreeStateVersionedMap {
  import A = BetreeBlockCacheSystem
  import B = ThreeStateVersionedPivotBetree
  import C = ThreeStateVersionedMap

  import Ref_A = BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree
  import Ref_B = ThreeStateVersionedPivotBetree_Refines_ThreeStateVersionedMap
  
  import UI

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

  lemma RefinesInit(k: A.Constants, s: A.Variables)
    requires A.Init(k, s)
    ensures A.Inv(k, s)
    ensures C.Init(Ik(k), I(k, s))
  {
    Ref_A.RefinesInit(k, s);
    Ref_B.RefinesInit(
      Ref_A.Ik(k),
      Ref_A.I(k, s));
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s': A.Variables, uiop: UI.Op)
    requires A.Inv(k, s)
    requires A.Next(k, s, s', uiop)
    ensures A.Inv(k, s')
    ensures C.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref_A.RefinesNext(k, s, s', uiop);
    Ref_B.RefinesNext(
      Ref_A.Ik(k),
      Ref_A.I(k, s),
      Ref_A.I(k, s'),
      uiop);
  }
}
