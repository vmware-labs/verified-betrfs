module GlinearMap {
  function method {:extern} gmap_borrow<K, V>(gshared m: map<K, V>, ghost k: K)
      : (gshared v': V)
  requires k in m
  ensures v' == m[k]

  glinear method {:extern} glmap_take<K, V>(glinear g: map<K, V>, ghost k: K)
  returns (glinear g': map<K, V>, glinear v': V)
  requires k in g
  ensures g' == g - {k}
  ensures v' == g[k]

  glinear method {:extern} glmap_empty<K, V>()
  returns (glinear g': map<K, V>)
  ensures g' == map[]

  glinear method {:extern} glmap_insert<K, V>(glinear g: map<K, V>, ghost k: K, glinear v: V)
  returns (glinear g': map<K, V>)
  ensures g' == g[k := v]

}
