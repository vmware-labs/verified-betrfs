include "CrashSafe.dfy"
include "BetreeBlockCacheSystemCrashSafeBetreeRefinement.dfy"

// This composes the two refinements:
//
//   BetreeBlockCacheSystem -> CrashSafe PivotBetree
//   CrashSafe PivotBetree -> CrashSafe Map
//
// To yield
//
//   BetreeBlockCacheSystem -> CrashSafe Map

module BetreeBlockCacheSystem_Refines_CrashSafeMap {
  import BBCS = BetreeBlockCacheSystem
  import CSPB = CrashSafePivotBetree
  import CSM = CrashSafeMap
  import Ref1 = BetreeBlockCacheSystem_Refines_CrashSafeBetree
  import Ref2 = CrashSafePivotBetree_Refines_CrashSafeMap

  type UIOp = Ref2.UIOp

  function Ik(k: BBCS.Constants) : CSM.Constants
  {
    Ref2.Ik(Ref1.Ik(k))
  }

  function I(k: BBCS.Constants, s: BBCS.Variables) : CSM.Variables
  requires BBCS.Inv(k, s)
  {
    Ref2.I(Ref1.Ik(k), Ref1.I(k, s))
  }

  lemma RefinesInit(k: BBCS.Constants, s: BBCS.Variables)
    requires BBCS.Init(k, s)
    ensures BBCS.Inv(k, s)
    ensures CSM.Init(Ik(k), I(k, s))
  {
    Ref1.RefinesInit(k, s);
    Ref2.RefinesInit(Ref1.Ik(k), Ref1.I(k, s));
  }

  lemma RefinesNext(k: BBCS.Constants, s: BBCS.Variables, s': BBCS.Variables, uiop: UIOp)
    requires BBCS.Inv(k, s)
    requires BBCS.Next(k, s, s', uiop)
    ensures BBCS.Inv(k, s')
    ensures CSM.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    Ref1.RefinesNext(k, s, s', uiop);
    Ref2.RefinesNext(Ref1.Ik(k), Ref1.I(k, s), Ref1.I(k, s'), uiop);
  }
}
