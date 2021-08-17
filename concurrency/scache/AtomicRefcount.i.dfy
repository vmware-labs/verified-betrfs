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

  predicate state_inv(v: uint8, g: T.Token, t: nat, rwlock_loc: Loc)
  {
    && g.loc == rwlock_loc
    && g.val == RwLock.RefCount(t, v as nat)
  }

  predicate atomic_refcount_inv(a: AtomicRefcount, t: nat, rwlock_loc: Loc)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, t, rwlock_loc)
  }

  method unsafe_obtain<R>() returns (glinear r: R)
  method unsafe_dispose<R>(glinear r: R)

  method is_refcount_eq(a: AtomicRefcount, val: uint8,
      ghost user_t: nat, ghost t: nat,
      glinear m: T.Token, ghost rwlock_loc: Loc)
  returns (is_zero: bool, glinear m': T.Token)
  requires t == user_t ==> val == 1
  requires t != user_t ==> val == 0
  requires atomic_refcount_inv(a, t, rwlock_loc)
  requires m.loc == rwlock_loc
  requires m.val.M? && m.val.exc.ExcPending?
  requires m.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t, m.val.exc.clean, m.val.exc.b))
  ensures m'.loc == m.loc
  ensures is_zero ==> m'.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t + 1, m.val.exc.clean, m.val.exc.b))
  ensures !is_zero ==> m'.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t, m.val.exc.clean, m.val.exc.b))
  {
    atomic_block var c := execute_atomic_load(a) {
      ghost_acquire old_g;
      glinear var new_g;
      if c == val {
        m', new_g := T.perform_TakeExcLockCheckRefCount(m, old_g);
      } else {
        m' := m;
        new_g := old_g;
      }
      ghost_release new_g;
    }

    is_zero := (c == val);
  }

  method inc_refcount_for_reading(a: AtomicRefcount,
      ghost t: nat, ghost rwlock_loc: Loc,
      //glinear client: T.Token,
      glinear m: T.Token)
  returns (glinear m': T.Token)
  requires atomic_refcount_inv(a, t, rwlock_loc)
  //requires client == RwLock.Internal(RwLock.Client(t))
  requires m.val == RwLock.ReadHandle(RwLock.ReadPending)
  requires m.loc == rwlock_loc
  ensures m'.loc == m.loc
  ensures m'.val == RwLock.ReadHandle(RwLock.ReadPendingCounted(t))
  {
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g, m' := T.perform_ReadingIncCount(m, old_g, t);
      ghost_release new_g;
    }
  }

  method inc_refcount_for_shared(a: AtomicRefcount,
      ghost t: nat, ghost rwlock_loc: Loc)
      //glinear client: T.Token)
  returns (glinear m': T.Token)
  requires atomic_refcount_inv(a, t, rwlock_loc)
  //requires client == RwLock.Internal(RwLock.Client(t))
  ensures m'.val == RwLock.SharedHandle(RwLock.SharedPending(t))
  ensures m'.loc == rwlock_loc
  {
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g, m' := T.perform_SharedIncCount(old_g, t);
      ghost_release new_g;
    }
  }

  method dec_refcount_for_shared_pending(a: AtomicRefcount,
      ghost t: nat, ghost rwlock_loc: Loc,
      glinear m: T.Token)
  //returns (glinear client: T.Token)
  requires atomic_refcount_inv(a, t, rwlock_loc)
  requires m.loc == rwlock_loc
  requires m.val == RwLock.SharedHandle(RwLock.SharedPending(t))
  //ensures client == RwLock.Internal(RwLock.Client(t))
  {
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g := T.perform_SharedDecCountPending(old_g, m, t);
      ghost_release new_g;
    }
  }

  method dec_refcount_for_shared_obtained(a: AtomicRefcount,
      ghost t: nat, ghost rwlock_loc: Loc, ghost b: Handle,
      glinear m: T.Token)
  //returns (glinear client: T.Token)
  requires atomic_refcount_inv(a, t, rwlock_loc)
  requires m.loc == rwlock_loc
  requires m.val == RwLock.SharedHandle(RwLock.SharedObtained(t, b))
  //ensures client == RwLock.Internal(RwLock.Client(t))
  {
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g := T.perform_SharedDecCountObtained(old_g, m, t, b);
      ghost_release new_g;
    }
  }
}
