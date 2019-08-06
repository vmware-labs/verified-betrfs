include "ByteBetreeBlockCacheSystem.i.dfy"

module ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem {
  import A = ByteBetreeBlockCacheSystem 
  import B = BetreeBlockCacheSystem

  type UIOp = A.UIOp

  function Ik(k: A.Constants) : B.Constants
  {
    A.Ik(k)
  }
  
  function I(k: A.Constants, s: A.Variables) : B.Variables
  requires A.Inv(k, s)
  {
    A.I(k, s)
  }

  lemma RefinesInit(k: A.Constants, s: A.Variables)
  requires A.Init(k, s)
  ensures A.Inv(k, s)
  ensures B.Init(Ik(k), I(k, s))
  {
    A.InitImpliesInv(k, s);
  }

  lemma RefinesNext(k: A.Constants, s: A.Variables, s': A.Variables, uiop: UIOp)
  requires A.Inv(k, s)
  requires A.Next(k, s, s', uiop)
  ensures A.Inv(k, s')
  ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    A.NextRefines(k, s, s', uiop);
  }
}
