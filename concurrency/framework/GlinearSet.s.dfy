module GlinearSet {
  glinear method {:extern} glset_take<K>(glinear g: set<K>, ghost gk: K)
  returns (glinear g': set<K>, glinear k: K)
  requires gk in g
  ensures g' == g - {gk}
  ensures k == gk

  glinear method {:extern} glset_empty<K>()
  returns (glinear g': set<K>)
  ensures g' == {}

  glinear method {:extern} glset_insert<K>(glinear g: set<K>, glinear k: K)
  returns (glinear g': set<K>)
  ensures g' == g + {k}

  function {:extern} glset<K>(g: set<K>): set<K>
  ensures glset(g) == g

}
