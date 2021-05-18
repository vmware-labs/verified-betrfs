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

## Atomics

Our `atomic` primitive will be based off the [C++ std::atomic library](https://en.cppreference.com/w/cpp/atomic/atomic) and similar like [Rust's std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/). For now, *we will only use the ‘sequentially consistent’ guarantee* for now (and in fact the Mutexes we examined earlier need to implemented with sequentially consistent guaranees).

(However, the [GPS: Navigating Weak Memory with Ghosts, Protocols, and Separation](http://plv.mpi-sws.org/gps/paper.pdf) paper provides some good reading on logics suitable for Acquire/Release primitives, which we will hopefully make use of in the future.)

So, how should we think of the atomic cell primitive?

We can actually think of an atomic as being similar to a mutex. An atomic cell will hold (i) some physical value (usually a small datatype, like a `uint64` or a pointer) (ii) some user-chosen ghost state, and (iii) an invariant between them.

To perform an operation, we can imagine that we:

 * ”Take out” the physical and ghost values, obtaining the invariant.
 * Perform the operation on the physical state.
 * Perform some user-defined update on the ghost state, to restore the invariant.
 * ”Put back” the new physical and new ghost values.

I've added some special syntax to our Dafnye extension to support this code structure. The
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

The full atomic operations available in [Atomic.s.dfy](code/Atomic.s.dfy)
and implemented in (trusted) C++ in [ExternAtomic.h](code/ExternAtomic.h)
(essentially just a thin wrapper around `std::atomic`).

The `old_value` and `new_value` are both available as special variables within the atomic block.
The ghost state is available by the `ghost_acquire` statement (which must be the first statement
in the atomic block). The statement `ghost_acquire g;` assigns the atomic cell's ghost state
to the variable `g`. Furthermore, it provides the user with the logical assertion of
`inv(old_value, g)` (where `inv` is the user-specified invariant). When the user then calls
`ghost_release g;` they must make sure that `inv(new_value, g)` is met.

Before we dig into the use-case of a spin lock, let's introduce one more concept real quick.

## Atomics

To implement a spin lock, we're going to need some concept of _permission to access a memory location_. In traditional separation logic, this is the “points-to” assertion, usually denoted (_p_ ↪ _v_) for a pointer _p_ and value _v_. The pointer itself can be passed around shared freely. However, (_p_ ↪ _v_) denotes _exclusive_ permission to actually read or write to the location _p_ (and specifically, to read the value _v_).

We use this concept in our [pointers library](code/Ptrs.s.dfy), which a ghost object
to represent the points-to (_p_ ↪ _v_).

```
datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
```

Here's the specification for writing to a pointer (taking a pointer as an implicit `this` parameter).

```dafny
method {:extern} write<V>(glinear inout d: PointsTo<V>, v: V)
requires old_d.ptr == this
ensures d.ptr == this
ensures d.v == v
```

Note that `inout` just denotes a paramter that is both an in-parameter _and_ an out-parameter. An alternative (without `inout`) would look like this:

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

## A spin-lock implementation
