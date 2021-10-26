include "../framework/Atomic.s.dfy"
include "rwlock/RwLock.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"
include "ClientCounter.i.dfy"

module AtomicRefcountImpl {
  import opened NativeTypes
  import opened Atomics
  import opened CacheHandle
  import opened GhostLoc
  import opened Constants
  import opened ClientCounter
  import opened Ptrs
  import RwLock
  import T = RwLockToken

  glinear datatype RG = RG(
    glinear token: T.Token,
    glinear counter: Clients
  )

  predicate state_inv(v: uint8, g: RG, t: nat, rwlock_loc: Loc, counter_loc: Loc)
  {
    && g.token.loc == rwlock_loc
    && g.token.val == RwLock.RefCount(t, v as nat)
    && g.counter.loc == counter_loc
    && g.counter.n == v as int
    && 0 <= t < RC_WIDTH as int
  }

  linear datatype AtomicRefcount = AtomicRefcount(
    linear a: Atomic<uint8, RG>,
    ghost rwlock_loc: Loc,
    ghost counter_loc: Loc
  )
  {
    predicate inv(t: nat) {
      && (forall v, g :: atomic_inv(a, v, g) <==>
          state_inv(v, g, t, this.rwlock_loc, this.counter_loc))
    }
  }

  method is_refcount_eq(shared a: AtomicRefcount, val: uint8,
      ghost user_t: int, ghost t: nat,
      glinear m: T.Token)
  returns (is_zero: bool, glinear m': T.Token)
  requires t == user_t ==> val == 1
  requires t != user_t ==> val == 0
  requires a.inv(t)
  requires m.loc == a.rwlock_loc
  requires m.val.M? && m.val.exc.ExcPending?
  requires m.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t, m.val.exc.clean, m.val.exc.b))
  ensures m'.loc == m.loc
  ensures is_zero ==> m'.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t + 1, m.val.exc.clean, m.val.exc.b))
  ensures !is_zero ==> m'.val == RwLock.ExcHandle(RwLock.ExcPending(user_t, t, m.val.exc.clean, m.val.exc.b))
  {
    atomic_block var c := execute_atomic_load(a.a) {
      ghost_acquire old_g;
      glinear var new_g;
      if c == val {
        glinear var RG(t, counter) := old_g;
        m', t := T.perform_TakeExcLockCheckRefCount(m, t);
        new_g := RG(t, counter);
      } else {
        m' := m;
        new_g := old_g;
      }
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }

    is_zero := (c == val);
  }

  method inc_refcount_for_reading(shared a: AtomicRefcount,
      ghost t: nat,
      glinear client: Client,
      glinear m: T.Token)
  returns (glinear m': T.Token)
  requires a.inv(t)
  //requires client == RwLock.Internal(RwLock.Client(t))
  requires m.val == RwLock.ReadHandle(RwLock.ReadPending)
  requires m.loc == a.rwlock_loc
  requires client.loc == a.counter_loc
  ensures m'.loc == m.loc
  ensures m'.val == RwLock.ReadHandle(RwLock.ReadPendingCounted(t))
  {
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      glinear var RG(token, counter) := old_g;
      m', token := T.perform_ReadingIncCount(m, token, t);
      //assert new_value == old_value + 1;
      //assert old_g.val == RwLock.RefCount(t, old_value as int);
      //assert old_g.val.refCounts[t] == old_value as int;
      //assert new_g.val == RwLock.RefCount(t, new_value as int);
      //assert state_inv(new_value, new_g, t, rwlock_loc);
      counter := merge(counter, client);
      get_bound(counter);
      new_g := RG(token, counter);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }

  method inc_refcount_for_shared(shared a: AtomicRefcount,
      ghost t: nat,
      glinear client: Client)
  returns (glinear m': T.Token)
  requires a.inv(t)
  requires client.loc == a.counter_loc
  //requires client == RwLock.Internal(RwLock.Client(t))
  ensures m'.val == RwLock.SharedHandle(RwLock.SharedPending(t))
  ensures m'.loc == a.rwlock_loc
  {
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      glinear var RG(token, counter) := old_g;
      token, m' := T.perform_SharedIncCount(token, t);
      counter := merge(counter, client);
      get_bound(counter);
      new_g := RG(token, counter);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }

  method inc_refcount_for_exc(shared a: AtomicRefcount,
      glinear m: T.Token,
      ghost t: nat,
      glinear client: Client)
  returns (glinear m': T.Token)
  requires a.inv(t)
  //requires client == RwLock.Internal(RwLock.Client(t))
  requires m.loc == a.rwlock_loc
  requires m.val.M? && m.val.exc.ExcObtained?
  requires m.val == RwLock.ExcHandle(RwLock.ExcObtained(-1, m.val.exc.clean))
  requires client.loc == a.counter_loc
  ensures m'.val == RwLock.ExcHandle(RwLock.ExcObtained(t, m.val.exc.clean))
  ensures m'.loc == a.rwlock_loc
  {
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      glinear var RG(token, counter) := old_g;
      token, m' := T.perform_ExcIncCount(token, m, t);
      counter := merge(counter, client);
      get_bound(counter);
      new_g := RG(token, counter);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }

  method dec_refcount_for_shared_pending(shared a: AtomicRefcount,
      ghost t: nat,
      glinear m: T.Token)
  returns (glinear client: Client)
  requires a.inv(t)
  requires m.loc == a.rwlock_loc
  requires m.val == RwLock.SharedHandle(RwLock.SharedPending(t))
        || m.val == RwLock.SharedHandle(RwLock.SharedPending2(t))
  ensures client.loc == a.counter_loc
  {
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      glinear var RG(token, counter) := old_g;
      if m.val == RwLock.SharedHandle(RwLock.SharedPending(t)) {
        token := T.perform_SharedDecCountPending(token, m, t);
      } else {
        token := T.perform_SharedDecCountPending2(token, m, t);
      }
      counter, client := split(counter);
      new_g := RG(token, counter);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }

  method dec_refcount_for_shared_obtained(shared a: AtomicRefcount,
      ghost t: nat, ghost b: Handle,
      glinear m: T.Token)
  returns (glinear client: Client)
  requires a.inv(t)
  requires m.loc == a.rwlock_loc
  requires m.val == RwLock.SharedHandle(RwLock.SharedObtained(t, b))
  ensures client.loc == a.counter_loc
  {
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      glinear var RG(token, counter) := old_g;
      token := T.perform_SharedDecCountObtained(token, m, t, b);
      counter, client := split(counter);
      new_g := RG(token, counter);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }
}
