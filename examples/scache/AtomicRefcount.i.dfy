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
    g == RWLock.Internal(RWLock.SharedLockRefCount(key, t, v))
  }

  predicate atomic_refcount_inv(a: AtomicRefcount, key: RWLock.Key, t: int)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, key, t)
  }

  method unsafe_obtain<R>() returns (linear r: R)
  method unsafe_dispose<R>(linear r: R)

  method is_refcount_eq(a: AtomicRefcount, val: uint8,
      key: RWLock.Key, my_t: int, t: int,
      linear m: RWLock.R)
  returns (is_zero: bool, linear m': RWLock.R)
  requires t == my_t ==> val == 1
  requires t != my_t ==> val == 0
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t))
  ensures is_zero ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t + 1))
  ensures !is_zero ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t))
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
    if c == val {
      m' := RWLock.transform_TakeExcLockCheckSharedLockZero(
          key, my_t, t, old_g, m);
      new_g := old_g;
    } else {
      m' := m;
      new_g := old_g;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    is_zero := (c == val);
  }

  method inc_refcount_for_reading(a: AtomicRefcount, key: RWLock.Key, t: int,
      linear m: RWLock.R)
  returns (linear m': RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.ReadingPending(key))
  ensures m' == RWLock.Internal(RWLock.ReadingPendingCounted(key, t))
  {
    var orig_value := fetch_add_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == (
        if old_v as int + added as int < 0x100 then
          (old_v as int + added as int) as uint8
        else
          (old_v as int + added as int - 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    new_g, m' := RWLock.transform_ReadingIncCount(key, t, old_v, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method inc_refcount_for_shared(a: AtomicRefcount,
      key: RWLock.Key, t: int)
  returns (linear m': RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  ensures m' == RWLock.Internal(RWLock.SharedLockPending(key, t))
  {
    var orig_value := fetch_add_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == (
        if old_v as int + added as int < 0x100 then
          (old_v as int + added as int) as uint8
        else
          (old_v as int + added as int - 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    new_g, m' := RWLock.transform_SharedIncCount(key, t, old_v, old_g);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_pending(a: AtomicRefcount,
      key: RWLock.Key, t: int, linear m: RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.SharedLockPending(key, t))
  {
    var orig_value := fetch_sub_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == (
        if old_v as int - added as int >= 0 then
          (old_v as int - added as int) as uint8
        else
          (old_v as int - added as int + 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    new_g := RWLock.transform_SharedDecCountPending(
        key, t, old_v, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_obtained(a: AtomicRefcount,
      key: RWLock.Key, t: int, linear m: RWLock.R,
      linear handle: RWLock.Handle)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.SharedLockObtained(key, t))
  requires handle.is_handle(key)
  {
    var orig_value := fetch_sub_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == (
        if old_v as int - added as int >= 0 then
          (old_v as int - added as int) as uint8
        else
          (old_v as int - added as int + 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    new_g := RWLock.transform_SharedDecCountObtained(
        key, t, old_v, old_g, m, handle);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

}
