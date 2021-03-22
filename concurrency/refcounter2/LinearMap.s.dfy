// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module LinearMaps {
  type LinearMap<K, V>

  function map_of<K, V>(m: LinearMap<K, V>) : map<K, V>

  function method {:extern} empty<K, V>() : (linear m: LinearMap<K, V>)
  ensures map_of(m) == map[]

  method {:extern} discard<K, V>(linear m: LinearMap<K, V>)
  requires map_of(m) == map[]

  function method {:extern} add<K, V>(linear m: LinearMap<K, V>, ghost k: K, linear v: V)
    : (linear m': LinearMap<K, V>)
  requires k !in map_of(m)
  ensures map_of(m') == map_of(m)[k := v]

  method {:extern} remove<K, V>(linear m: LinearMap<K, V>, ghost k: K)
    returns (linear m': LinearMap<K, V>, linear v: V)
  requires k in map_of(m)
  ensures k !in map_of(m')
  ensures map_of(m')[k := v] == map_of(m)

}
