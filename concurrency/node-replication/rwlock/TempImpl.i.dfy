module RwLockImpl {
  // TODO implement this

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
  returns (linear m: RwLock<V>)
  requires inv(v)
  ensures m.inv == inv

  /*
   * An ExclusiveGuard is a special ghost object you get when you
   * call `acquire` on a RwLock. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  datatype ExclusiveGuard<V> = ExclusiveGuard(ghost m: RwLock<V>)

  /*
   * A SharedGuard is for shared access.
   * Use the `borrow_shared` method below to obtain shared access
   * to the data structure stored in the mutex.
   */

  datatype SharedGuard<V> = SharedGuard(ghost m: RwLock<V>, ghost v: V)

  /*
   * RwLock that protects a piece of data with some invariant.
   */

  type {:extern} RwLock(==)<!V>
  {
    predicate {:extern} inv(v: V)

    /*
     * `acquire`
     * Provides the client with the guarantee that the data
     * inside meets the invariant.
     */

    shared method {:extern} acquire()
    returns (linear v: V, glinear handle: ExclusiveGuard<V>)
    ensures this.inv(v)
    ensures handle.m == this

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    shared method {:extern} release(linear v: V, glinear handle: ExclusiveGuard<V>)
    requires this.inv(v)
    requires handle.m == this

    /*
     * `acquire_shared`
     * Like acquire, but can be held by more than one client at a time.
     * Returns a handle that can be borrowed from
     */

    shared method acquire_shared()
    returns (linear handle: SharedGuard<V>)
    ensures this.inv(handle.v)
    ensures handle.m == this

    /*
     * `acquire_release`
     */

    shared method release_shared(linear handle: SharedGuard<V>)
    requires handle.m == this
  }

  function method {:extern} borrow_shared<V>(shared handle: SharedGuard<V>)
      : (shared v: V)
  ensures v == handle.v
}
