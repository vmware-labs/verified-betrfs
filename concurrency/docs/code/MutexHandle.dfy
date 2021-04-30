module Mutexes {
  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method {:extern} new_mutex<V>(v: V, ghost inv: (V) -> bool)
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
    returns (v: V, glinear handle: MutexHandle<V>)
    ensures this.inv(v)
    ensures handle.m == this

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    method {:extern} release(v: V, glinear handle: MutexHandle<V>)
    requires this.inv(v)
    requires handle.m == this
  }
}

module Example {
  import opened Mutexes

  /*
   * Create a mutex that will only store even integers,
   * i.e., it has an invariant that the integer x stored in
   * satisfies (x % 2 == 0).
   */
  method create_mutex_for_even_int()
  returns (m: Mutex<int>)
  ensures forall x :: m.inv(x) <==> x % 2 == 0
  {
    // Lambda predicate for testing if an integer is even.
    // Note that the invariant is only a proof artifact;
    // this isn't a lambda function that will appear in any
    // compiled code.

    ghost var inv := (x) => x % 2 == 0;

    // Create the mutex with the invariant.
    // The initial value we store in the mutex is 6.
    // (It's a pretty good number.)

    var mutex := new_mutex(6, (x) => x % 2 == 0);
    return mutex;
  }

  method add_two(m: Mutex<int>)
  requires forall x :: m.inv(x) <==> x % 2 == 0
  {
    // When we call acquire, we get a `glinear` handle.
    var the_integer;
    glinear var handle;
    the_integer, handle := m.acquire();

    // This should hold because of the mutex invariant.
    assert the_integer % 2 == 0;

    the_integer := the_integer + 2;

    // Should still hold.
    assert the_integer % 2 == 0;

    // We can release the mutex because we've met the invariant again.
    // We return the handle when we call `release`.
    m.release(the_integer, handle);

    // If we try to call `release` again, we'll get a linear type error.
    m.release(the_integer, handle); // ERROR
  }

  method Main() {
    var mutex := create_mutex_for_even_int();

    // We haven't added any fork/join primitives yet -
    // but we can imagine passing the mutex around to different
    // threads and having them call `add_two` simultaneously.

    add_two(mutex);
    add_two(mutex);
    add_two(mutex);
    add_two(mutex);
  }
}
