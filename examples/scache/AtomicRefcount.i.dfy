include "Atomic.s.dfy"
include "RWLock.i.dfy"
include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"

module AtomicRefcount {
  import opened NativeTypes
  import opened Ptrs
  import opened AtomicSpec
  import ReadWriteLockResources

  type AtomicRefcount = Atomic<uint8, ReadWriteLockResources.Q>

  predicate state_inv(v: uint8, g: ReadWriteLockResources.Q, ptr: Ptr, t: int)
  {
    g == ReadWriteLockResources.ReadRefCount(ptr, t, v)
  }

  predicate atomic_refcount_inv(a: AtomicRefcount, ptr: Ptr, t: int)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, ptr, t)
  }

  method unsafe_obtain<R>() returns (linear r: R)
  method unsafe_dispose<R>(linear r: R)

  method is_refcount_zero(a: AtomicRefcount, ptr: Ptrs.Ptr, t: int,
      linear m: ReadWriteLockResources.Q)
  returns (is_zero: bool, linear m': ReadWriteLockResources.Q)
  requires atomic_refcount_inv(a, ptr, t)
  requires m == ReadWriteLockResources.WritePending(ptr, t)
  ensures is_zero ==> m' == ReadWriteLockResources.WritePending(ptr, t + 1)
  ensures !is_zero ==> m' == ReadWriteLockResources.WritePending(ptr, t)
  {
    var c := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: ReadWriteLockResources.Q := unsafe_obtain();
    assume new_v == old_v;
    assume c == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    if c == 0 {
      new_g, m' := ReadWriteLockResources.transform_TakeWriteCheckReadZero(
          ptr, t, old_g, m);
    } else {
      m' := m;
      new_g := old_g;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    is_zero := (c == 0);
  }
}
