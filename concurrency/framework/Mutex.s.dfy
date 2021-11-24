// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module {:extern "Mutexes"} Mutexes {
  /*
   * Mutex that protects a piece of data with some invariant.
   */

  type {:extern} Mutex(==)<!V>
  {
    predicate {:extern} inv(v: V)

    /*
     * `acquire`
     * Note that there is no deadlock prevention.
     */

    shared method {:extern} acquire()
    returns (linear v: V, glinear handle: MutexHandle<V>)
    ensures this.inv(v)
    ensures handle.m == this

    /*
     * `release`
     */

    shared method {:extern} release(linear v: V, glinear handle: MutexHandle<V>)
    requires this.inv(v)
    requires handle.m == this
  }

  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method {:extern} new_mutex<V>(linear v: V, ghost inv: (V) -> bool)
  returns (linear m: Mutex)
  requires inv(v)
  ensures m.inv == inv

  /*
   * A MutexHandle is a special ghost object you get when you
   * call `acquire` on a Mutex. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  datatype MutexHandle<V> = MutexHandle(m: Mutex<V>)
}
