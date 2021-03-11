// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Atomic.s.dfy"
include "RWLock.i.dfy"
include "RWLockMethods.i.dfy"
include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"

module AtomicRefcountImpl {
  import opened NativeTypes
  import opened AtomicSpec
  import RWLock
  import RWLockMethods

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
  requires m.Internal? && m.q.ExcLockPending?
  requires m == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t, m.q.clean))
  ensures is_zero ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t + 1, m.q.clean))
  ensures !is_zero ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, my_t, t, m.q.clean))
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
      var clean := m.q.clean;
      m' := RWLockMethods.transform_TakeExcLockSharedLockZero(
          key, my_t, t, clean, old_g, m);
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
      linear client: RWLock.R, linear m: RWLock.R)
  returns (linear m': RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires client == RWLock.Internal(RWLock.Client(t))
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
    new_g, m' := RWLockMethods.transform_ReadingIncCount(key, t, old_v, client, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method inc_refcount_for_shared(a: AtomicRefcount,
      key: RWLock.Key, t: int,
      linear client: RWLock.R)
  returns (linear m': RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires client == RWLock.Internal(RWLock.Client(t))
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
    new_g, m' := RWLockMethods.transform_SharedIncCount(key, t, old_v, client, old_g);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_pending(a: AtomicRefcount,
      key: RWLock.Key, t: int, linear m: RWLock.R)
  returns (linear client: RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.SharedLockPending(key, t))
  ensures client == RWLock.Internal(RWLock.Client(t))
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
    new_g, client := RWLockMethods.transform_SharedDecCountPending(
        key, t, old_v, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_obtained(a: AtomicRefcount,
      key: RWLock.Key, t: int, linear m: RWLock.R,
      linear handle: RWLock.Handle)
  returns (linear client: RWLock.R)
  requires atomic_refcount_inv(a, key, t)
  requires m == RWLock.Internal(RWLock.SharedLockObtained(key, t))
  requires handle.is_handle(key)
  ensures client == RWLock.Internal(RWLock.Client(t))
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
    new_g, client := RWLockMethods.transform_SharedDecCountObtained(
        key, t, old_v, old_g, m, handle);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

}
