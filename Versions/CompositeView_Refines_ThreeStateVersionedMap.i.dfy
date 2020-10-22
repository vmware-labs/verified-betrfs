include "CompositeView_Refines_TSJMap.i.dfy"
include "../MapSpec/TSJMap_Refines_ThreeStateVersionedMap.i.dfy"

//
// Composes the two refinements:
//
//   CompositeView -> TSJMap
//   TSJMap -> ThreeStateVersioned Map
//
// To yield
//
//   CompositeView -> ThreeStateVersioned Map
//

module CompositeView_Refines_ThreeStateVersionedMap {
  import A = CompositeView
  import B = TSJMap
  import C = ThreeStateVersionedMap

  import Ref_A = CompositeView_Refines_TSJMap
  import Ref_B = TSJMap_Refines_ThreeStateVersionedMap
  
  import UI

  inductive predicate Reachable(s: A.Variables)
  {
    A.Init(s) || (exists s0, u :: Reachable(s0) && A.Next(s0, s, u))
  }

  inductive lemma ReachableImpliesInv(s: A.Variables)
  requires Reachable(s)
  ensures A.Inv(s)
  ensures B.Inv(Ref_A.I(s))
  {
    if A.Init(s) {
      A.InitImpliesInv(s);
      Ref_A.RefinesInit(s);
      B.InitImpliesInv(Ref_A.I(s));
    } else {
      var s0, u :| Reachable(s0) && A.Next(s0, s, u);
      ReachableImpliesInv(s0);
      A.NextPreservesInv(s0, s, u);
      Ref_A.RefinesNext(s0, s, u);
      B.NextPreservesInv(Ref_A.I(s0), Ref_A.I(s), u);
    }
  }

  function I(s: A.Variables) : C.Variables
  requires Reachable(s)
  {
    ReachableImpliesInv(s);

    Ref_B.I(
      Ref_A.I(s)
    )
  }

  lemma RefinesInit(s: A.Variables)
    requires A.Init(s)
    ensures A.Inv(s)
    ensures C.Init(I(s))
  {
    Ref_A.RefinesInit(s);
    Ref_B.RefinesInit(
      Ref_A.I(s));
  }

  lemma RefinesNext(s: A.Variables, s': A.Variables, uiop: UI.Op)
    requires Reachable(s)
    requires A.Next(s, s', uiop)
    ensures Reachable(s')
    ensures C.Next(I(s), I(s'), uiop)
  {
    ReachableImpliesInv(s);
    Ref_A.RefinesNext(s, s', uiop);
    Ref_B.RefinesNext(
      Ref_A.I(s),
      Ref_A.I(s'),
      uiop);
  }
}
