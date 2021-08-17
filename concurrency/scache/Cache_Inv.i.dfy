include "CacheSM.i.dfy"

module Cache_Inv {
  import A = AsyncDiskSystemStateMachine(CacheIfc, CacheSSM)
  import opened CacheSSM

  predicate Inv(s: A.Variables) {
    s.
  }
}
