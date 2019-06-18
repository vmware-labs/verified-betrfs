include "BlockCacheSystem.dfy"
include "CrashSafe.dfy"

module BlockCacheSystemCrashSafeBlockInterfaceRefinement {
  import BCS = BlockCacheSystem
  import CSBI = CrashSafeBlockInterface

  function Ik(k: BCS.Constants) : CSBI.Constants
  {
    CSBI.Constants(k.machine.constants, k.machine.constants)
  }

  function I(k: BCS.Constants, s: BCS.Variables) : CSBI.Variables
  {
    CSBI.Variables(
  }
}
