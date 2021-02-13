module Ptrs {
  type {:extern} PtrInternalOpaqueType(!new,==)

  // Non-ghosty

  datatype Ptr = Ptr(_internal: PtrInternalOpaqueType)

  function method {:extern} nullptr() : Ptr

  // Ghosty

  // TODO there needs to be some way to enforce that the
  // impl cannot conjure these out of nowhere

  // Normal ptrs

  datatype Deref<V> = Deref(ptr: Ptr, v: V)

  method {:extern} malloc<V>()
  returns (p: Ptr, ghost linear d: Deref<V>)
  ensures d.ptr == p

  method {:extern} ptr_write<V>(p: Ptr, ghost inout linear d: Deref<V>, v: V)
  requires old_d.ptr == p
  ensures d.ptr == p
  ensures d.v == v

  method {:extern} ptr_read<V>(p: Ptr, ghost shared d: Deref<V>)
  returns (v: V)
  requires d.ptr == p
  ensures v == d.v

  // Array ptrs

  datatype ArrayDeref<V> = ArrayDeref(ptr: Ptr, s: seq<V>)

  method {:extern} malloc_array<V>(n: int)
  returns (p: Ptr, ghost linear d: ArrayDeref<V>)
  ensures d.ptr == p
  ensures |d.s| == n

  method {:extern} array_write<V>(p: Ptr, ghost linear inout d: ArrayDeref, i: int, v: V)
  requires old_d.ptr == p
  requires 0 <= i < |old_d.s|
  ensures d == d.(s := old_d.s[i := v])

  method {:extern} array_read<V>(p: Ptr, ghost shared d: ArrayDeref<V>, i: int)
  returns (v: V)
  requires d.ptr == p
  requires 0 <= i < |d.s|
  ensures v == d.s[i]

  // Read-only

  datatype Const<A> = Const(a: A)
}
