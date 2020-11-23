include "Atomic.s.dfy"
include "RWLock.i.dfy"
include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"

module AtomicRefcountImpl {
  import opened NativeTypes
  import opened AtomicSpec
  import RWLock

  type AtomicRefcount = Atomic<uint8, RWLock.R>

  predicate state_inv(v: uint8, g: RWLock.R, key: RWLock.Key, t: int)
  {
    g == RWLock.Internal(RWLock.ReadRefCount(key, t, v))
  }

  predicate atomic_refcount_inv(a: AtomicRefcount, key: RWLock.Key, t: int)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, key, t)
  }

  method unsafe_obtain<R>() returns (linear r: R)
  method unsafe_dispose<R>(linear r: R)

  method is_refcount_zero(a: AtomicRefcount, key: RWLock.Key, t: int,
      linear m: RWLock.R)
  returns (is_zero: bool, linear m': RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.WritePending(key, t))
  ensures is_zero ==> m' == RWLock.Internal(RWLock.WritePending(key, t + 1))
  ensures !is_zero ==> m' == RWLock.Internal(RWLock.WritePending(key, t))
  {
    var c := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == old_v;
    assume c == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    if c == 0 {
      new_g, m' := RWLock.transform_TakeWriteCheckReadZero(
          key, t, old_g, m);
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
