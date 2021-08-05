include "AbstractCacheSM.i.dfy"
include "SimpleCacheSM.i.dfy"

module SimpleCache_Refines_AbstractCache refines
    Refinement(CrashAsyncIfc(CacheIfc),
        SimpleCacheStateMachine,
        AbstractCacheStateMachine) {

  predicate Inv(s: A.Variables)

  lemma InitImpliesInv(s: A.Variables)
  requires A.Init(s)
  ensures Inv(s)

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  requires Inv(s)
  requires A.Next(s, s', op)
  ensures Inv(s')

  function I(s: A.Variables) : B.Variables
  requires Inv(s)

  lemma InitRefinesInit(s: A.Variables)
  requires A.Init(s)
  requires Inv(s)
  ensures B.Init(I(s))

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  requires Inv(s)
  requires Inv(s')
  requires A.Next(s, s', op)
  ensures B.Next(I(s), I(s'), op)

}
