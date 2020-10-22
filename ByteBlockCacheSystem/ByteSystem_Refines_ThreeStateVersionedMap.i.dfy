include "ByteSystem_Refines_BetreeJournalSystem.i.dfy"
include "../BlockCacheSystem/BetreeJournalSystem_Refines_ThreeStateVersionedMap.i.dfy"

//
// Composes the two refinements:
//
//   ByteSystem -> BetreeJournalSystem
//   BetreeJournalSystem -> ThreeStateVersioned Map
//
// To yield
//
//   ByteSystem -> ThreeStateVersioned Map
//

module ByteSystem_Refines_ThreeStateVersionedMap {
  import A = ByteSystem
  import B = BetreeJournalSystem
  import C = ThreeStateVersionedMap

  import Ref_A = ByteSystem_Refines_BetreeJournalSystem
  import Ref_B = BetreeJournalSystem_Refines_ThreeStateVersionedMap
  
  import UI

  inductive predicate Reachable(s: A.Variables)
  {
    A.Init(s) || (exists s0, u :: Reachable(s0) && A.Next(s0, s, u))
  }

  inductive lemma ReachableImpliesInv(s: A.Variables)
  requires Reachable(s)
  ensures A.Inv(s)
  ensures Ref_B.Reachable(Ref_A.I(s))
  {
    if A.Init(s) {
      A.InitImpliesInv(s);
      Ref_A.RefinesInit(s);
      //B.InitImpliesInv(Ref_A.I(s));
    } else {
      var s0, u :| Reachable(s0) && A.Next(s0, s, u);
      ReachableImpliesInv(s0);
      A.NextPreservesInv(s0, s, u);
      Ref_A.RefinesNext(s0, s, u);
      //B.NextPreservesInv(Ref_A.I(s0), Ref_A.I(s), u);
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
