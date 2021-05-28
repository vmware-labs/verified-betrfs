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
   * Mutex that protects a piece of data with some invariant.
   */

  type {:extern} Mutex(==)<!V>
  {
    predicate {:extern} inv(v: V)

    /*
     * `acquire`
     * Provides the client with the guarantee that the data
     * inside meets the invariant.
     */

    method {:extern} acquire()
    returns (v: V)
    ensures this.inv(v)

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    method {:extern} release(v: V)
    requires this.inv(v)
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
    var the_integer := m.acquire();

    // This should hold because of the mutex invariant.
    assert the_integer % 2 == 0;

    the_integer := the_integer + 1;

    // Invariant doesn't hold here!!! But that's okay,
    // `the_integer` is just a local variable.
    // Nobody else can access it.

    the_integer := the_integer + 1;

    // Should still hold.
    assert the_integer % 2 == 0;

    // We can release the mutex because we've met the invariant again.
    m.release(the_integer);
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
