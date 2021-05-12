module LinearMutexes {
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
  returns (m: Mutex)
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

  /*
   * Mutex that protects a piece of data with some invariant.
   */

  type {:extern} Mutex(==)<V>
  {
    predicate {:extern} inv(v: V)

    /*
     * `acquire`
     * Provides the client with the guarantee that the data
     * inside meets the invariant.
     */

    method {:extern} acquire()
    returns (linear v: V, glinear handle: MutexHandle<V>)
    ensures this.inv(v)
    ensures handle.m == this

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    method {:extern} release(linear v: V, glinear handle: MutexHandle<V>)
    requires this.inv(v)
    requires handle.m == this
  }
}
