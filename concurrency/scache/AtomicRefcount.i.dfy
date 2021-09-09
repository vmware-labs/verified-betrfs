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

  predicate state_inv(v: uint8, g: T.Token, t: nat, rwlock_loc: Loc)
  {
    && g.loc == rwlock_loc
    && g.val == RwLock.RefCount(t, v as nat)
    && 0 <= t < RC_WIDTH as int
  }

  linear datatype AtomicRefcount = AtomicRefcount(
    linear a: Atomic<uint8, T.Token>,
    ghost rwlock_loc: Loc
  )
  {
    predicate inv(t: nat) {
      forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, t, this.rwlock_loc)
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
        m', new_g := T.perform_TakeExcLockCheckRefCount(m, old_g);
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
  ensures m'.loc == m.loc
  ensures m'.val == RwLock.ReadHandle(RwLock.ReadPendingCounted(t))
  {
    dispose_anything(client);
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      m', new_g := T.perform_ReadingIncCount(m, old_g, t);
      assume old_value < 255; // TODO
      //assert new_value == old_value + 1;
      //assert old_g.val == RwLock.RefCount(t, old_value as int);
      //assert old_g.val.refCounts[t] == old_value as int;
      //assert new_g.val == RwLock.RefCount(t, new_value as int);
      //assert state_inv(new_value, new_g, t, rwlock_loc);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }

  method inc_refcount_for_shared(shared a: AtomicRefcount,
      ghost t: nat,
      glinear client: Client)
  returns (glinear m': T.Token)
  requires a.inv(t)
  //requires client == RwLock.Internal(RwLock.Client(t))
  ensures m'.val == RwLock.SharedHandle(RwLock.SharedPending(t))
  ensures m'.loc == a.rwlock_loc
  {
    dispose_anything(client);
    atomic_block var orig_value := execute_atomic_fetch_add_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g, m' := T.perform_SharedIncCount(old_g, t);
      assume old_value < 255; // TODO
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
  //ensures client == RwLock.Internal(RwLock.Client(t))
  {
    client := hack_new_client();
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g := T.perform_SharedDecCountPending(old_g, m, t);
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
  //ensures client == RwLock.Internal(RwLock.Client(t))
  {
    client := hack_new_client();
    atomic_block var orig_value := execute_atomic_fetch_sub_uint8(a.a, 1) {
      ghost_acquire old_g;
      glinear var new_g;
      new_g := T.perform_SharedDecCountObtained(old_g, m, t, b);
      assert atomic_inv(a.a, new_value, new_g);
      ghost_release new_g;
    }
  }
}
