Let's implement a spin-lock out of a simpler primitive: an atomic memory cell.

The implementation will very simple. We will have two fields: `exc_bit`, a boolean field
that indicates whether any thread has taken the lock, and `store`, where the actual data
will be stored.

 * To acquire the mutex (returning a value `V`)
   * Atomically set the `exc_bit` from `false` to `true` (using a `compare_exchange` primitive).
   * Return the value in the `store` field.
 * To release the mutex (taking as input a value `V`)
   * Assign the value to the `store` field.
   * Set the `exc_bit` to `false`.

The implementation of an exclusive spin lock (unlike more advanced implementations) is simple enough that we won't need to create a ShardedStateMachine for it. Instead, we'll focus this example on the two new primitives we need: atomics and pointers.

## Atomics

Our `atomic` primitive will be based off the [C++ std::atomic library](https://en.cppreference.com/w/cpp/atomic/atomic) and similar to [Rust's std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/). For now, *we will only use the ‘sequentially consistent’ guarantee* (and in fact the Mutexes we examined earlier need to implemented with sequentially consistent guarantees).

(However, the [GPS: Navigating Weak Memory with Ghosts, Protocols, and Separation](http://plv.mpi-sws.org/gps/paper.pdf) paper provides some good reading on logics suitable for Acquire/Release primitives, which we will hopefully make use of in the future.)

So, how should we think of the atomic cell primitive?

We can actually think of an atomic as being similar to a mutex. An atomic cell will hold (i) some physical value (usually a small datatype, like a `uint64` or a pointer) (ii) some user-chosen ghost state, and (iii) an invariant between them.

To perform an operation, we can imagine that we:

 * ”Take out” the physical and ghost values, obtaining the invariant.
 * Perform the operation on the physical state.
 * Perform some user-defined update on the ghost state, to restore the invariant.
 * ”Put back” the new physical and new ghost values.

I've added some special syntax to our Dafny extension to support this code structure. The
syntax looks like:

```
atomic_block var result := ATOMIC_OPERATION {
  ghost_acquire g;
  // ghost code here
  ghost_release g;
}
```

The `atomic_block` requires that the operation after the `:=` be a specially designated
“atomic” operation. It also ensures that the code inside the atomic block is all ghost code.

The standard atomic operations are available (`store`, `load`, `compare_exchange`, `fetch_add`, and so on). Each of these operations is specified by a ternary relation on three values: `old_value`, `new_value`, and `return_value`. For example, here is the ternary specification for `compare_exchange` on an atomic cell storing a value `V`.

```
compare_exhange(v1: V, v2: V) 
atomic operation: old_value -> new_value
returns (return_value : bool)
ensures (
  && (old_value == v1 ==>
    new_value == v2 && return_value == true)
  && (new_value != v1 ==>
    new_value == old_value && return_value == false)
)
```

The full atomic operations and there ternarny specifications are
available in [Atomic.s.dfy](code/Atomic.s.dfy)
and implemented in (trusted) C++ in [ExternAtomic.h](code/ExternAtomic.h)
(essentially just a thin wrapper around `std::atomic`).

The `old_value` and `new_value` are both available as special variables within the atomic block.
The ghost state is available by the `ghost_acquire` statement (which must be the first statement
in the atomic block). The statement `ghost_acquire g;` assigns the atomic cell's ghost state
to the variable `g`. Furthermore, it provides the user with the logical assertion of
`inv(old_value, g)` (where `inv` is the user-specified invariant). When the user then calls
`ghost_release g;` they must ensure that `inv(new_value, g)` is met.

Before we dig into the use-case of a spin lock, let's briefly introduce one more concept.

## Pointers and memory

To implement a spin lock, we're going to need some concept of _permission to access a memory location_. In traditional separation logic, this is the “points-to” assertion, usually denoted (_p_ `↪` _v_) for a pointer _p_ and value _v_. The pointer itself can be passed around and shared freely. However, (_p_ `↪` _v_) denotes _exclusive_ permission to actually read or write to the location _p_ (and specifically, to read the value _v_).

We use this concept in our [pointers library](code/Ptrs.s.dfy).
We introduce two types:

* `Ptr` (a concrete value which is essentially a `volatile void *`)
* `PointsTo`, a ghost object to represent the points-to (_p_ `↪` _v_).

```dafny
datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
```

Here's the specification for writing to a pointer (taking a pointer as an implicit `this` parameter).

```dafny
method {:extern} write<V>(glinear inout d: PointsTo<V>, v: V)
requires old_d.ptr == this
ensures d.ptr == this
ensures d.v == v
```

Note that `inout` just denotes a parameter that is both an in-parameter _and_ an out-parameter. An alternative (without `inout`) would look like this:

```dafny
method {:extern} write<V>(glinear old_d: PointsTo<V>, v: V)
returns (glinear d: PointsTo<V>)
requires old_d.ptr == this
ensures d.ptr == this
ensures d.v == v
```

The requirement to write to the pointer `this` is to provide the `PointsTo` as a ghost value.
The contract of `write`, then, updates the points-to value to the new value being written,
which lets us verify we get the same value back when we do a read:

```dafny
method {:extern} read<V>(gshared d: PointsTo<V>)
returns (v: V)
requires d.ptr == this
ensures v == d.v
```

Here's an example of the library in action:

[code/SimplePtrExample.dfy](code/SimplePtrExample.dfy)
```dafny
method Main() {
  var ptr;
  glinear var points_to;

  ptr, points_to := alloc(5);

  // read a value, check that it is 5:
  var r := ptr.read(points_to);
  assert r == 5;

  // write a value
  ptr.write(inout points_to, 9);

  // we managed to update its value to 9:
  assert points_to.v == 9;

  // ... which can we see if we read it again:
  var q := ptr.read(points_to);
  assert q == 9;

  // free memory
  ptr.free(points_to);
}
```

## A spin-lock implementation

Let's dive into the spin-lock implementation. Our implementation will roughly match
the specification in [code/MutexHandle.s.dfy](code/MutexHandle.dfy).

The full code is at [code/MutexImpl.dfy](code/MutexImpl.dfy).

There is a lot to take in here, in part because of syntactic kludges.  Furthermore, due to technical reasons, it doesn't work to write `f == g` where `f` and `g` are functions—we instead need to write `forall x :: f x == g x`; this isn't a huge deal, but it does make things harder to read. We'll go through it slowly.

First, we're going to have an atomic boolean cell which holds some ghost state: that ghost state will be either a `PointsTo` value (when the boolean state is set to `false`) or “nothing” (when the boolean state is set to `true`). Thus we need a concept of “nothing”, so we will start by introducing an option datatype:

```dafny
glinear datatype glOption<V> = Some(glinear value: V) | None
```

Next, our `Mutex` datatype. We'll have three fields: the two fields mentioned previously (an atomic boolean field `exc_bit`, a pointer `store` to the data store, and a third (ghost) field to keep track of the mutex inv:

```dafny
datatype Mutex<!V(!new)> = Mutex(
    exc_bit: Atomic<bool, glOption<PointsTo<V>>>,
    store: Ptr,
    ghost inv: (V) -> bool)
```

(The declaration of the Mutex template argument `!V(!new)` is a little funky.
The `(!new)` just means that we won't hold any “allocated references”, but that's a concept
from Dafny Classic, and doesn't really apply here at all. The _other_ `!`, the one before the
`V`, is a variance marker, and it is required to allow to use the `(V) -> bool` type. It otherwise won't have much impact here.)

Now, one thing to keep track of is that there are _two_ invariants of interest. The boolean atomic cell will have an invariant, which we will call `ainv`, which protects the contents of the atomic cell.

The mutex _also_ has an invariant, which we call `inv`, which protects the contents of the mutex. Furthermore, the `ainv` will be defined in terms of `inv`:

```dafny
predicate ainv<V>(store: Ptr, inv: (V) -> bool, v_exc: bool, g: glOption<PointsTo<V>>)
{
  && (!v_exc ==> (g.Some? && g.value.ptr == store && inv(g.value.v)))
  && (v_exc ==> g.None?)
}
```

The way to think of the `ainv` is that it is a relation between the boolean value (`v_exc`) and the ghost state (`g`) inside the atomic cell, but this relation is also parameterized by properties of the mutex: the `store` pointer and the mutex invariant `inv`.

This invariant simply says, in English:

 * If the boolean value is `false`, then the ghost state is a `PointsTo` value pointing to the pointer `store` and storing some value which meets the mutex invariant.
 * If the boolean value is `true`, then the ghost state has nothing (more precisely, `None`).

Let's add a `well_formed` predicate to our mutex that actually connects this `ainv` to the atomic invariant.

```dafny
datatype Mutex<!V(!new)> = Mutex(
    exc_bit: Atomic<bool, glOption<PointsTo<V>>>,
    store: Ptr,
    ghost inv: (V) -> bool)
{
  predicate well_formed() {
    forall v_exc, g :: atomic_inv(this.exc_bit, v_exc, g) <==>
        ainv(this.store, this.inv, v_exc, g)
  }
}
```

The `well_formed` predicate is yet _another_ thing that looks like an “invariant”, but unlike the other two invariants, this predicate is not acquired and released—rather, it is just shared by everybody who holds the mutex.

To recap, here is everything we have so far:

```dafny
glinear datatype glOption<V> = Some(glinear value: V) | None

predicate ainv<V>(store: Ptr, inv: (V) -> bool, v_exc: bool, g: glOption<PointsTo<V>>)
{
  && (!v_exc ==> (g.Some? && g.value.ptr == store && inv(g.value.v)))
  && (v_exc ==> g.None?)
}

datatype Mutex<!V(!new)> = Mutex(
    exc_bit: Atomic<bool, glOption<PointsTo<V>>>,
    store: Ptr,
    ghost inv: (V) -> bool)
{
  predicate well_formed() {
    forall v_exc, g :: atomic_inv(exc_bit, v_exc, g) <==>
        ainv(store, inv, v_exc, g)
  }
}
```

Let's create a mutex:

```dafny
method {:extern} new_mutex<V(!new)>(v: V, ghost inv: (V) -> bool)
returns (m: Mutex)
requires inv(v)
ensures m.well_formed()
ensures m.inv == inv
{
  var store;
  glinear var points_to;
  store, points_to := alloc(v);
  var atomic_cell := new_atomic(false, Some(points_to), (v, g) => ainv(store, inv, v, g), {});
  m := Mutex(atomic_cell, store, inv);
}
```

First, we call `alloc`, to allocate some memory to store a value in. We initialize that memory with the input value `v`. In doing so, we get both the raw pointer `store` and the `points_to` value representing permission to access the memory.

Next, we create the atomic cell with `new_atomic`. We initialize it with the value `false` and the `points_to` ghost state. We also declare that the atomic cell will have the invariant given by `ainv`.

Finally, we package all those things into a `Mutex` object and return it via the out-parameter `m`.

Now, before we build the `acquire` and `release` methods, we need a concept of `MutexHandle`. It turns out that we can just make that the `PointsTo` object that we're already using:

```dafny
type MutexHandle<V> = PointsTo<V>

predicate is_handle_for<V(!new)>(handle: MutexHandle<V>, m: Mutex<V>)
{
  handle.ptr == m.store
}
```

Now, it would be perfectly fine to build a Mutex that just accepts and returns a
`PointsTo` object for the client to manipulate at will. We'll stick to our [code/MutexHandle.dfy](code/MutexHandle.dfy) specification, which says that `acquire` should return an actual `V` value, while `release` should take one as input. This means that our `acquire` and `release` implementations will actually need to `read` and `write`.

```dafny
method acquire<V(!new)>(m: Mutex<V>)
returns (v: V, glinear handle: MutexHandle<V>)
decreases *
requires m.well_formed()
ensures m.inv(v)
ensures is_handle_for(handle, m)
{
  var success := false;

  glinear var handle_opt: glOption<PointsTo<V>> := None;
  
  while !success
  invariant !success ==> handle_opt == None
  invariant success ==> handle_opt.Some?
        && handle_opt.value.ptr == m.store
        && m.inv(handle_opt.value.v)
  decreases *
  {
    atomic_block success := execute_atomic_compare_and_set_strong(m.exc_bit, false, true) {
      ghost_acquire g;

      assert ainv(m.store, m.inv, old_value, g);

      if success {
        assert ainv(m.store, m.inv, false, g); // old_value = false

        glinear var tmp := handle_opt;
        handle_opt := g;
        g := tmp;

        assert ainv(m.store, m.inv, true, g); // new_value = true
      }

      assert ainv(m.store, m.inv, new_value, g);

      ghost_release g;
    }
  }

  glinear var Some(handle_out) := handle_opt;
  handle := handle_out;

  v := m.store.read(handle);
}
```

Phew! Let's go through it. First, the `decreases *` means that the method isn't guaranteed to terminate (in particular, we haven't proved deadlock prevention).

_Physically_, what we do here is:

 * Set up a `success` flag and loop (“spin”) until it hits `true`.
 * In each iteration, we do a `compare_and_set`, trying to move from `false` to `true`.
    Our `compare_and_set` primitive returns `true` if it succeeds. Thus, we end up looping
    until the `compare_and_set` succeeds.
 * We read from the pointer `store` and return that value.

Notice that _physically_, there is nothing that actually that ties the spin-loop to the pointer read. That all comes in with the ghost state.

So let's talk through the code in the ghost world:

 * Set up a `success` flag.
 * Set up a `handle_opt` variable. We initialize it to `None`, but we will store the `PointsTo` object in this variable when the spin-loop succeeds.
 * Start the loop.
   * Perform the `compare_and_set` and open the ghost block.
     * If `success` is true, then that means we are transition from `old_value = false` to `old_value = true`. We have to make sure that invariant `ainv` is maintained. The `assert` statements here document this process, although they aren't strictly needed.
     * To maintain the invariant, we just swap `handle_opt` and `g`.
 * When the loop ends, `success` is true, and we have set up a loop invariant to ensure that `handle_opt` is the correct value when it exits.
 * We destruct the `glOption` value that is `handle_opt`, taking out the `PointsTo` value (`handle_out`).
 * Set `handle` (the output parameter of the method) to `handle_out`.
 * Read from the pointer (validating this with the `handle`) and return the resulting value `v`.

Now, `release` is similar. We just need to set the value back to `false` and return the ghost state. There's only one question to consider: what happens if, when we perform our store operation, the value is already set to `false`? In that case, there would already be some ghost state (a `PointsTo` object, necessarily) in the atomic cell. What would we do then? We could either:

 * Dispose of that state.
 * Prove that this case is impossible in the first place.

Well, our library doesn't actually have a way to dispose of a `PointsTo` object without calling `free` on the memory (and we'd like to keep it that way, just to prevent memory leaks). Let's do the second thing instead.

How could we prove this case is impossible? Well, the `release` method requires the user to pass the handle back. The handle is just the `PointsTo` object. Furthermore, you can't have two `PointsTo` objects for the same pointer. Therefore, you cannot have one already stored in the atomic cell.

Perfect let's do that. All we need to complete this is the axiom about not having two `PointsTo` objects (a standard axiom in “normal” separation logic) which can be found in our pointers library as `points_to_exclusive`.

```dafny
method {:extern} release<V(!new)>(m: Mutex<V>, v: V, glinear handle: MutexHandle<V>)
requires m.well_formed()
requires m.inv(v)
requires is_handle_for(handle, m)
{
  glinear var handle' := handle;
  m.store.write(inout handle', v);

  atomic_block var _ := execute_atomic_store(m.exc_bit, false) {
    ghost_acquire g;

    glinear match g {
      case None => {
        assert ainv(m.store, m.inv, true, g);

        /* we must be in this case */
      }
      case Some(internal_ptr) => {
        assert ainv(m.store, m.inv, false, g);

        points_to_exclusive(inout handle', inout internal_ptr);
        assert false;
        consume_if_false(internal_ptr);
      }
    }

    g := Some(handle');

    assert ainv(m.store, m.inv, false, g);

    ghost_release g;
  }
}
```

So physically, what's going on is:

 * We write the input value `v` into the memory location.
 * Perform an atomic store operation, writing `false` into the atomic cell. 

And ghostily:
 
 * When we write the value `v` to the memory location, we end up updating the `PointsTo` object. Since `release` demands that `v` satisfies the mutex invariant, we'll be able to meet the atomic invariant when we put the `PointsTo` object back inside.
 * We perform the store operation and open the ghost atomic block:
   * We split on cases based on what object was inside `g`.
     * In the `None` case, there is no linear ghost state to dispose of.
     * In the `Some` case, we show that this case is impossible. We call the `points_to_exclusive` “lemma” as described earlier. Then we call `consume_if_false`, an axiom that lets us dispose of any resource in a branch where we have proved `false`.
   * Finally, we release the `PointsTo` object into the atomic cell, and we're done.

Again, you can find the full code at [code/MutexHandle.dfy](code/MutexHandle.dfy).

In the next section, we'll do some more advanced locking mechanisms, where the interesting logic is in constructing a ShardedStateMachine.
