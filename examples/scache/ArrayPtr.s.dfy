module Ptrs {
  type {:extern} PtrInternalOpaqueType(!new,==)

  // Non-ghosty

  datatype Ptr = Ptr(_internal: PtrInternalOpaqueType)

  function method nullptr() : Ptr

  // Ghosty

  // TODO there needs to be some way to enforce that the
  // impl cannot conjure these out of nowhere

  // Normal ptrs

  datatype Deref<V> = Deref(ptr: Ptr, v: V)

  method {:extern} ptr_read<V>(p: Ptr, shared d: Deref<V>)
  returns (v: V)
  requires d.ptr == p
  ensures v == d.v

  // Array ptrs

  datatype R<V> =
    | ArrayReadCount(ptr: Ptr, s: seq<V>, refcount: int)
    | ConstArrayDeref(ptr: Ptr, s: seq<V>)

  type ArrayDeref<V> = r: R<V> | r.ArrayReadCount? && r.refcount == 0
      witness ArrayReadCount(nullptr(), [], 0)

  type ConstArrayDeref<V> = r: R<V> | r.ConstArrayDeref?
      witness ConstArrayDeref(nullptr(), [])

  method {:extern} array_write<V>(p: Ptr, linear inout d: ArrayDeref, i: int, v: V)
  requires old_d.ptr == p
  requires 0 <= i < |old_d.s|
  ensures d == d.(s := old_d.s[i := v])

  method {:extern} array_read<V>(p: Ptr, shared d: ArrayDeref<V>, i: int)
  returns (v: V)
  requires d.ptr == p
  requires 0 <= i < |d.s|
  ensures v == d.s[i]

  method {:extern} const_array_read<V>(p: Ptr, shared d: ConstArrayDeref<V>, i: int)
  returns (v: V)
  requires d.ptr == p
  requires 0 <= i < |d.s|
  ensures v == d.s[i]

  predicate transform<V(!new)>(a: multiset<R<V>>, b: multiset<R<V>>)
  {
    || (exists ptr, s, refcount ::
      && a == multiset{ArrayReadCount(ptr, s, refcount)}
      && b == multiset{ArrayReadCount(ptr, s, refcount + 1), ConstArrayDeref(ptr, s)}
    )
    || (exists ptr, s, refcount, s' ::
      && a == multiset{ArrayReadCount(ptr, s, refcount), ConstArrayDeref(ptr, s')}
      && b == multiset{ArrayReadCount(ptr, s, refcount - 1)}
    ) 
  }

  /*method main(p: Ptr, linear d: ArrayDeref<int>)
  returns (linear d': ArrayDeref<int>)
  requires |d.s| == 1
  requires d.ptr == p
  {
    var a := array_read(p, d, 0);
    d' := d;
  }*/

  // forall C, D . rel(C, D) ==> exists C', D' . (A+C) ==> (A'+C') & (B+D) ==> (B'+D') & rel(C',D')
  // ------
  // A+B ==> A'+B'
}
