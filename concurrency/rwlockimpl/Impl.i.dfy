include "RwLock.i.dfy"
include "../framework/GlinearOption.i.dfy"
include "../framework/Atomic.s.dfy"

abstract module RwLockImpl(stm: StoredTypeModule) {
  import RwLock = RwLock(stm)
  import RwLockTokens = RwLockTokens(stm)
  import Wrap = RwLockTokens.T.Wrap

  import opened NativeTypes
  import opened Atomics
  import opened GhostLoc
  import opened Options
  import opened GlinearOption

  predicate exc_inv(b: bool, t: RwLockTokens.Token, loc: Loc) {
    && t.val == RwLock.PhysExcHandle(b)
    && t.loc == loc
  }

  predicate rc_inv(rc: uint32, t: RwLockTokens.Token, loc: Loc) {
    && t.val == RwLock.PhysRcHandle(rc as nat)
    && t.loc == loc
  }

  predicate central_inv(t: RwLockTokens.Token, loc: Loc) {
    && t.val.M?
    && t.val.central.CentralState?
    && t.val == RwLock.CentralHandle(t.val.central)
    && t.loc == loc
  }

  datatype RWLock = RWLock(
    exc: Atomic<bool, RwLockTokens.Token>,
    rc: Atomic<uint32, RwLockTokens.Token>,

    ghost central: GhostAtomic<RwLockTokens.Token>,
    ghost loc: Loc
  )
  {
    predicate Inv() {
      && (forall v, g :: atomic_inv(this.exc, v, g) <==> exc_inv(v, g, this.loc))
      && (forall v, g :: atomic_inv(this.rc, v, g) <==> rc_inv(v, g, this.loc))
      && (forall v, g :: atomic_inv(this.central, v, g) <==> central_inv(g, this.loc))
      && (this.central.namespace() == 1)
      && (this.exc.namespace() == 2)
      && (this.rc.namespace() == 3)
      && (loc.ExtLoc? && loc.base_loc == Wrap.singleton_loc())
    }

    method acquire_exc()
    returns (glinear base_token: stm.StoredType, glinear handle: RwLockTokens.Token)
    decreases *
    requires Inv()
    ensures handle.val == RwLock.ExcTakenHandle()
    {
      var got_exc := false;
      glinear var pending_handle := RwLockTokens.T.get_unit(this.loc);

      while !got_exc
      invariant got_exc ==> pending_handle.val == RwLock.ExcPendingHandle()
      invariant got_exc ==> pending_handle.loc == this.loc
      decreases *
      {
        atomic_block got_exc := execute_atomic_compare_and_set_strong(this.exc, false, true) {
          ghost_acquire g;
          if got_exc {
            RwLockTokens.T.dispose(pending_handle);
            g, pending_handle := RwLockTokens.perform_exc_pending(g);
          }
          ghost_release g;
        }
      }

      glinear var baseTokenOpt := glNone;

      var is_rc_zero := false;

      while !is_rc_zero
      invariant !is_rc_zero ==> pending_handle.val == RwLock.ExcPendingHandle()
      invariant is_rc_zero ==> pending_handle.val == RwLock.ExcTakenHandle()
      invariant !is_rc_zero ==> baseTokenOpt.glNone?
      invariant is_rc_zero ==> baseTokenOpt.glSome?
      invariant pending_handle.loc == this.loc
      invariant this.Inv()
      decreases *
      {
        atomic_block var ret_value := execute_atomic_load(this.rc) {
          ghost_acquire rc_g;
          atomic_block var _ := execute_atomic_noop(this.central) {
            ghost_acquire central_g;

            if old_value == 0 {
              dispose_glnone(baseTokenOpt);
              glinear var bt;
              rc_g, central_g, pending_handle, bt :=
                RwLockTokens.perform_exc_finish(rc_g, central_g, pending_handle, central_g.val.central.held_value);
              baseTokenOpt := glSome(bt);
            }

            ghost_release central_g;
          }
          ghost_release rc_g;
        }

        if ret_value == 0 {
          is_rc_zero := true;
        }
      }

      base_token := unwrap_value(baseTokenOpt);
      handle := pending_handle;
    }

    method release_exc(glinear base_token: stm.StoredType, glinear handle: RwLockTokens.Token)
    requires Inv()
    requires handle.val == RwLock.ExcTakenHandle()
    requires handle.loc == this.loc
    {
      atomic_block var _ := execute_atomic_store(this.exc, false) {
        ghost_acquire g;
        atomic_block var _ := execute_atomic_noop(this.central) {
          ghost_acquire central_g;

          g, central_g :=
            RwLockTokens.perform_exc_release(g, central_g, handle, base_token,
                central_g.val.central.held_value, g.val.phys_exc.value);

          ghost_release central_g;
        }
        ghost_release g;
      }
    }

    /*private*/ method wait_for_exc_false()
    decreases *
    requires Inv()
    {
      var exc_value := true;
      while exc_value
      decreases *
      {
        atomic_block exc_value := execute_atomic_load(this.exc) { }
      }
    }

    /*private*/ method load_rc()
    returns (rc: uint32)
    requires Inv()
    {
      atomic_block rc := execute_atomic_load(this.rc) { }
    }

    method acquire_shared()
    returns (glinear handle: RwLockTokens.Token)
    requires Inv()
    ensures exists a :: handle.val == RwLock.SharedTakenHandle(a)
    ensures handle.loc == this.loc
    decreases *
    {
      handle := RwLockTokens.T.get_unit(this.loc);

      var done := false;

      while !done
      invariant done ==> exists a :: handle.val == RwLock.SharedTakenHandle(a)
      invariant done ==> handle.loc == this.loc
      decreases *
      {
        this.wait_for_exc_false();
        var cur_rc := this.load_rc();

        if cur_rc != 0xffff_ffff {
          // increment rc

          atomic_block var ret_value := execute_atomic_compare_and_set_strong(this.rc, cur_rc, cur_rc + 1) {
            ghost_acquire g;
            if ret_value {
              RwLockTokens.T.dispose(handle);
              g, handle := RwLockTokens.perform_shared_pending(g, cur_rc as nat);
            }
            ghost_release g;
          }

          if ret_value {
            // check exc is false

            atomic_block var exc_value := execute_atomic_load(this.exc) {
              ghost_acquire g;
              atomic_block var _ := execute_atomic_noop(this.central) {
                ghost_acquire central_g;
                if !exc_value {
                  g, central_g, handle := RwLockTokens.perform_shared_finish(
                        g, central_g, handle, central_g.val.central.held_value);
                }
                ghost_release central_g;
              }
              ghost_release g;
            }

            if !exc_value {
              done := true;
            } else {
              // abort

              atomic_block var _ := execute_atomic_fetch_sub_uint32(this.rc, 1) {
                ghost_acquire g;
                g := RwLockTokens.perform_abort_shared(g, handle, old_value as nat);
                handle := RwLockTokens.T.get_unit(handle.loc);
                ghost_release g;
              }
            }
          }
        }
      }
    }

    method release_shared(glinear handle: RwLockTokens.Token)
    requires Inv()
    requires exists a :: handle.val == RwLock.SharedTakenHandle(a)
    requires handle.loc == this.loc
    {
      atomic_block var _ := execute_atomic_fetch_sub_uint32(this.rc, 1) {
        ghost_acquire g;
        atomic_block var _ := execute_atomic_noop(this.central) {
          ghost_acquire central_g;
          ghost var a :| handle.val == RwLock.SharedTakenHandle(a);
          g, central_g :=
            RwLockTokens.perform_release_shared(g, central_g, handle,
                central_g.val.central.held_value, a, g.val.phys_rc.value);
          ghost_release central_g;
        }
        ghost_release g;
      }
    }
  }

  method rwlock_new(glinear init_value: stm.StoredType)
  returns (rwlock: RWLock)
  ensures rwlock.Inv()
  {
    glinear var pe, rc, central := RwLockTokens.initialize(init_value);

    ghost var loc := pe.loc; 
    var exc_atomic := new_atomic(false, pe, (v, g) => exc_inv(v, g, loc), 2);
    var rc_atomic := new_atomic(0 as uint32, rc, (v, g) => rc_inv(v, g, loc), 3);
    ghost var central_atomic := new_ghost_atomic(central, (g) => central_inv(g, loc), 1);

    rwlock := RWLock(exc_atomic, rc_atomic, central_atomic, loc);
  }
}

module TrivialSTM refines StoredTypeModule {
  glinear datatype Trivial = Trivial
  type StoredType = Trivial
}

module ConcreteRwLockImpl {
  import Impl = RwLockImpl(TrivialSTM)  
}
