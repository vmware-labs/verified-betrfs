
In [the previous page](MutexIntro.md) we pointed out that our Mutex API had no way to enforce that any client of the mutex obey the rule that it only call `release` after first calling `acquire`.

It turns out that this is easy to fix—and it also provides an opportunity to show one of the simplest uses of `ghost linear`.

Initially, the purpose of `ghost linear` might seem strange to one unfamiliar with separation logic. After all, the ordinary `linear` type is in some sense a compiler optimization: semantically, we imagine all objects are immutable, but the compiler is allowed to emit updates-in-place rather than deep copies, as justified by the linear type system. (Again, see the Dafny linear type system documentation.) So then what’s the point of `ghost linear`? If an object is purely `ghost` (i.e., not compiled, it may seem like there is no point to optimizing out deep copies.

In fact, with `ghost linear`, we will actually be using the linear type system to enforce verification-relevant properties—like the mutex acquire/release property.

Here’s the idea: when a client calls `acquire`, it gets some sort of handle. In order to call `release`, it must supply that handle. This handle requires a few properties:

- It should be “zero cost”, that is, it shouldn’t actually appear in compiled code. Its only purpose is in verification.
- It should be linear—once we return the handle via a mutex `release`, we shouldn’t be able to use it to call `release` again. The handle serves as a ‘right’ to call `release` exactly once, so we should relinquish that right once we make the call.

So there we have it: we want this handle to be ‘ghost linear’.

In Linear-Dafny, we use the keyword `glinear` for ghost linear things. (There is also `gshared` for ‘ghost shared,’ and we’ll get to that later.) Let’s see the improved mutex API:

[code/MutexHandle.dfy](code/MutexHandle.dfy)

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
```

And here’s an example usage:

```dafny
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
```

