
In this intro, we'll aim to answer the questions:

**How can we write an API specification for a mutex?**

While all this code is written in the ‘Linear-Dafny’ language, it’s worth noting that Linear-Dafny is inspired by Rust, and as we develop these concepts, we frequently imagine that we’re verifying Rust instead. So we’ll frequently make reference to Rust concepts.

To start, Linear-Dafny’s linear type is a lot like Rust’s types, in that they have unique ownership. Furthermore, a `linear` variable in Dafny can in some cases be converted to a `shared` type (although this `shared` type must ‘expire’ before access to the `linear` type is returned). While not as powerful, it is analogous to shared-borrows in Rust.

We expect, therefore, that our verified Mutexes should be similar to Rust mutexes in some way. In particular, a program should not have access to the data behind a mutex except when it has acquired the lock. For much the same reason - the contents of the mutex could be manipulated by other threads at any time!

Of course, this leaves open the question of how to do verification on mutexes at all.

The first answer will be by using an invariant. The idea is that any mutex has an invariant (a logical predicate on the mutex state). The invariant is fixed for the mutex, so all parties that have access to the mutex can agree on what the invariant is. When a thread acquires a mutex, it obtains the guarantee that the data meets the invariant. When the thread releases the mutex, it must prove that the data it is returning meets the invariant.

If the thread then acquires the mutex again later, it will again see that it maintains the invariant—although it won’t have any guarantee of it being, say, the exact same value as before.

[code/SimpleMutexExample.dfy](code/SimpleMutexExample.dfy)

```dafny
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

  type {:extern} Mutex(==)<V>
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

    var mutex := new_mutex(6, inv);
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
```

At this point, there are several things to wonder:

- How do we ensure that a client never calls `release` without first acquiring the lock / how do we ensure it only calls `release` once?
- What if we want a fine-grained locking policy, i.e., what if have multiple mutexes? How can we describe relationships between the data?
- How do we ensure deadlock freedom?

While the last problem is currently out of scope, we’ll address the first two issues next.
