include "GlinearMap.s.dfy"

module GlinearMap_i {
  import opened GlinearMap

  glinear method glmap_take_inout<K, V>(glinear inout g: map<K, V>, ghost k: K)
  returns (glinear v': V)
  requires k in old_g
  ensures g == old_g - {k}
  ensures v' == old_g[k]
  {
    g, v' := glmap_take(g, k);
  }

  glinear method glmap_insert_inout<K, V>(glinear inout g: map<K, V>, ghost k: K, glinear v: V)
    ensures g == old_g[k := v]
  {
    g := glmap_insert(g, k, v);
  }
}
