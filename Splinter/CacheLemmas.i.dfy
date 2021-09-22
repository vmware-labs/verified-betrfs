include "CacheIfc.i.dfy"

module CacheLemmasMod {
  import opened CacheIfc

  lemma EquivalentCaches(cache: Variables, cache': Variables, cacheOps: Ops)
    requires WritesApplied(cache, cache', cacheOps)
    requires cacheOps == []
    ensures cache.dv == cache'.dv
  {
  }

}
