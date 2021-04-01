// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module {:extern "Mutexes"} Mutexes {
  type {:extern} Atomic<V, G>

  type {:extern} Mutex<V>
  {
    predicate {:extern} inv(v: V)
  }

  datatype MutexHandle<V> = MutexHandle(m: Mutex<V>)

  method {:extern} new_mutex<V>(linear v: V, ghost inv: (V) -> bool)
  returns (m: Mutex)
  requires inv(v)
  ensures m.inv == inv

  method {:extern} acquire<V>(m: Mutex<V>)
  returns (linear v: V, glinear handle: MutexHandle<V>)
  ensures m.inv(v)
  ensures handle.m == m

  method {:extern} release<V>(m: Mutex<V>, linear v: V, glinear handle: MutexHandle<V>)
  requires m.inv(v)
  requires handle.m == m
}
