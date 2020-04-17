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
