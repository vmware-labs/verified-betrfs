module RwLock {
  // TODO implement this

  type V // TODO fill this in

  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method {:extern} new_mutex(glinear v: V, ghost inv: (V) -> bool)
  returns (m: RwLock)
  requires inv(v)
  ensures m.inv == inv

  /*
   * An ExclusiveHandle is a special ghost object you get when you
   * call `acquire` on a RwLock. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  datatype ExclusiveHandle = ExclusiveHandle(m: RwLock)

  /*
   * A SharedHandle is for shared access.
   */

  datatype SharedHandle = SharedHandle(m: RwLock, v: V)

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

    method {:extern} acquire()
    returns (glinear v: V, glinear handle: ExclusiveHandle)
    ensures this.inv(v)
    ensures handle.m == this

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    method {:extern} release(glinear v: V, glinear handle: ExclusiveHandle)
    requires this.inv(v)
    requires handle.m == this

    /*
     * `acquire_shared`
     * Like acquire, but can be held by more than one client at a time.
     * Returns a handle that can be borrowed from
     */

    method acquire_shared()
    returns (glinear handle: SharedHandle)
    ensures this.inv(handle.v)
    ensures handle.m == this

    /*
     * `acquire_release`
     */

    method release_shared(glinear handle: SharedHandle)
    requires handle.m == this
  }

  function method {:extern} borrow_shared(gshared handle: SharedHandle)
      : (gshared v: V)
  ensures v == handle.v
}