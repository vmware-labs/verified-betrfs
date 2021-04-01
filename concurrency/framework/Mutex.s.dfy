// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module {:extern "Mutexes"} Mutexes {
  type {:extern} Atomic<V, G>

  datatype MutexHandle<V> = MutexHandle(m: Mutex<V>)

  type {:extern} Mutex<V>
  {
    predicate {:extern} inv(v: V)

    method {:extern} acquire()
    returns (linear v: V, glinear handle: MutexHandle<V>)
    ensures this.inv(v)
    ensures handle.m == this

    method {:extern} release(linear v: V, glinear handle: MutexHandle<V>)
    requires this.inv(v)
    requires handle.m == this
  }

  method {:extern} new_mutex<V>(linear v: V, ghost inv: (V) -> bool)
  returns (m: Mutex)
  requires inv(v)
  ensures m.inv == inv
}
