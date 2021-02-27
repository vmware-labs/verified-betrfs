// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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

  function I(s: A.Variables) : C.Variables
  requires A.Inv(s)
  {
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
    requires A.Inv(s)
    requires A.Next(s, s', uiop)
    ensures A.Inv(s')
    ensures C.Next(I(s), I(s'), uiop)
  {
    Ref_A.RefinesNext(s, s', uiop);
    Ref_B.RefinesNext(
      Ref_A.I(s),
      Ref_A.I(s'),
      uiop);
  }
}
