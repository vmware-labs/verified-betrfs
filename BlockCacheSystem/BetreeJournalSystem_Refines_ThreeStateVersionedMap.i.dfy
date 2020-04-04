include "BetreeJournalSystem_Refines_CompositeView.i.dfy"
include "../Versions/CompositeView_Refines_ThreeStateVersionedMap.i.dfy"

//
// Composes the two refinements:
//
//   BetreeJournalSystem -> CompositeView
//   CompositeView -> ThreeStateVersioned Map
//
// To yield
//
//   BetreeJournalSystem -> ThreeStateVersioned Map
//

module BetreeJournalSystem_Refines_ThreeStateVersionedMap {
  import A = BetreeJournalSystem
  import B = CompositeView
  import C = ThreeStateVersionedMap

  import Ref_A = BetreeJournalSystem_Refines_CompositeView
  import Ref_B = CompositeView_Refines_ThreeStateVersionedMap
  
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
