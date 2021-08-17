include "../framework/Atomic.s.dfy"
include "rwlock/RwLock.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"

module AtomicRefcountImpl {
  import opened NativeTypes
  import opened Atomics
  import opened CacheHandle
  import opened GhostLoc
  import RwLock
  import T = RwLockToken

  type AtomicRefcount = Atomic<uint8, T.Token>

  predicate state_inv(v: uint8, g: T.Token, t: int, rwlock_loc: Loc)
  {
    && g.loc == rwlock_loc
    && g.val == RwLock.RefCount(t, v as nat)
  }

  predicate atomic_refcount_inv(a: AtomicRefcount, t: int, rwlock_loc: Loc)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, t, rwlock_loc)
  }

  method unsafe_obtain<R>() returns (glinear r: R)
  method unsafe_dispose<R>(glinear r: R)

  method is_refcount_eq(a: AtomicRefcount, val: uint8,
      ghost my_t: int, ghost t: int,
      glinear m: T.Token)
  returns (is_zero: bool, glinear m': T.Token)
  requires t == my_t ==> val == 1
  requires t != my_t ==> val == 0
  requires atomic_refcount_inv(a, key, t)
  requires m.Internal? && m.q.ExcLockPending?
  requires m == RwLock.Internal(RwLock.ExcLockPending(key, my_t, t, m.q.clean))
  ensures is_zero ==> m' == RwLock.Internal(RwLock.ExcLockPending(key, my_t, t + 1, m.q.clean))
  ensures !is_zero ==> m' == RwLock.Internal(RwLock.ExcLockPending(key, my_t, t, m.q.clean))
  {
    var c := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    glinear var old_g: T.Token := unsafe_obtain();
    assume new_v == old_v;
    assume c == old_v;
    assume atomic_inv(a, old_v, old_g);
    glinear var new_g;
    ///// Transfer:
    if c == val {
      var clean := m.q.clean;
      m' := RwLockMethods.transform_TakeExcLockSharedLockZero(
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

  method inc_refcount_for_reading(a: AtomicRefcount, key: Key, t: int,
      glinear client: T.Token, glinear m: T.Token)
  returns (glinear m': T.Token)
  requires atomic_refcount_inv(a, key, t)
  requires client == RwLock.Internal(RwLock.Client(t))
  requires m == RwLock.Internal(T.TokeneadingPending(key))
  ensures m' == RwLock.Internal(T.TokeneadingPendingCounted(key, t))
  {
    var orig_value := fetch_add_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    glinear var old_g: T.Token := unsafe_obtain();
    assume new_v == (
        if old_v as int + added as int < 0x100 then
          (old_v as int + added as int) as uint8
        else
          (old_v as int + added as int - 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    glinear var new_g;
    ///// Transfer:
    new_g, m' := RwLockMethods.transform_ReadingIncCount(key, t, old_v, client, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method inc_refcount_for_shared(a: AtomicRefcount,
      key: Key, t: int,
      glinear client: T.Token)
  returns (glinear m': T.Token)
  requires atomic_refcount_inv(a, key, t)
  requires client == RwLock.Internal(RwLock.Client(t))
  ensures m' == RwLock.Internal(RwLock.SharedLockPending(key, t))
  {
    var orig_value := fetch_add_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    glinear var old_g: T.Token := unsafe_obtain();
    assume new_v == (
        if old_v as int + added as int < 0x100 then
          (old_v as int + added as int) as uint8
        else
          (old_v as int + added as int - 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    glinear var new_g;
    ///// Transfer:
    new_g, m' := RwLockMethods.transform_SharedIncCount(key, t, old_v, client, old_g);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_pending(a: AtomicRefcount,
      key: Key, t: int, glinear m: T.Token)
  returns (glinear client: T.Token)
  requires atomic_refcount_inv(a, key, t)
  requires m == RwLock.Internal(RwLock.SharedLockPending(key, t))
  ensures client == RwLock.Internal(RwLock.Client(t))
  {
    var orig_value := fetch_sub_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    glinear var old_g: T.Token := unsafe_obtain();
    assume new_v == (
        if old_v as int - added as int >= 0 then
          (old_v as int - added as int) as uint8
        else
          (old_v as int - added as int + 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    glinear var new_g;
    ///// Transfer:
    new_g, client := RwLockMethods.transform_SharedDecCountPending(
        key, t, old_v, old_g, m);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method dec_refcount_for_shared_obtained(a: AtomicRefcount,
      key: Key, t: int, glinear m: T.Token,
      glinear handle: Handle)
  returns (glinear client: T.Token)
  requires atomic_refcount_inv(a, key, t)
  requires m == RwLock.Internal(RwLock.SharedLockObtained(key, t))
  requires handle.is_handle(key)
  ensures client == RwLock.Internal(RwLock.Client(t))
  {
    var orig_value := fetch_sub_uint8(a, 1);

    ///// Begin jank
    ///// Setup:
    var added: uint8 := 1;
    var old_v: uint8;
    var new_v: uint8;
    glinear var old_g: T.Token := unsafe_obtain();
    assume new_v == (
        if old_v as int - added as int >= 0 then
          (old_v as int - added as int) as uint8
        else
          (old_v as int - added as int + 0x100) as uint8
    );
    assume orig_value == old_v;
    assume atomic_inv(a, old_v, old_g);
    glinear var new_g;
    ///// Transfer:
    new_g, client := RwLockMethods.transform_SharedDecCountObtained(
        key, t, old_v, old_g, m, handle);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

}
