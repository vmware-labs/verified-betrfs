include "RWLock.dfy"
include "../framework/Atomic.s.dfy"

module RWLockImpl {
  import opened RWLockExt
  import opened RWLockExtToken
  import opened NativeTypes
  import opened Atomics
  import opened GhostLoc
  import opened Options

  predicate exc_inv(b: bool, t: Token, loc: Loc) {
    && t.get() == PhysExcHandle(b)
    && t.loc() == loc
  }

  predicate rc_inv(rc: uint32, t: Token, loc: Loc) {
    && t.get() == PhysRcHandle(rc as nat)
    && t.loc() == loc
  }

  predicate central_inv(t: Token, loc: Loc) {
    && t.get().central.Some?
    && t.get() == CentralHandle(t.get().central.value)
    && t.loc() == loc
  }

  datatype RWLock = RWLock(
    exc: Atomic<bool, Token>,
    rc: Atomic<uint32, Token>,

    ghost central: GhostAtomic<Token>,
    ghost loc: Loc
  )
  {
    predicate Inv() {
      && this.loc.ExtLoc?
      && (forall v, g :: atomic_inv(this.exc, v, g) <==> exc_inv(v, g, this.loc))
      && (forall v, g :: atomic_inv(this.rc, v, g) <==> rc_inv(v, g, this.loc))
      && (forall v, g :: atomic_inv(this.central, v, g) <==> central_inv(g, this.loc))
      //&& (this.exc.identifier() != this.rc.identifier()) // strictly speaking we don't need this one
      && (this.exc.identifier() != this.central.identifier())
      && (this.rc.identifier() != this.central.identifier())
    }

    method acquire_exc()
    returns (glinear base_token: Base.Token, glinear handle: RWLockExtToken.Token)
    decreases *
    requires Inv()
    ensures handle.get() == RWLockExt.ExcTakenHandle()
    ensures handle.loc().ExtLoc? && handle.loc().base_loc == base_token.loc()
    {
      var got_exc := false;
      glinear var pending_handle := RWLockExtToken.SEPCM.get_unit(this.loc);

      while !got_exc
      invariant got_exc ==> pending_handle.get() == RWLockExt.ExcPendingHandle()
      invariant got_exc ==> pending_handle.loc() == this.loc
      decreases *
      {
        atomic_block ret_value := execute_atomic_compare_and_set_strong(this.exc, false, true) {
          ghost_acquire g;
          ghost var ghostme := true;
          if ghostme && ret_value {
            RWLockExtToken.SEPCM.dispose(pending_handle);
            g, pending_handle := RWLockExtToken.perform_exc_pending(g);
          }
          ghost_release g;
        }

        got_exc := ret_value;
      }

      base_token := Base.get_unit(this.loc.base_loc);

      var is_rc_zero := false;

      while !is_rc_zero
      invariant !is_rc_zero ==> pending_handle.get() == RWLockExt.ExcPendingHandle()
      invariant is_rc_zero ==> pending_handle.get() == RWLockExt.ExcTakenHandle()
      invariant pending_handle.loc().ExtLoc? && pending_handle.loc().base_loc == base_token.loc()
      invariant pending_handle.loc() == this.loc
      invariant this.Inv()
      decreases *
      {
        atomic_block ret_value := execute_atomic_load(this.rc) {
          ghost_acquire rc_g;
          atomic_block _ := execute_atomic_noop(this.central) {
            ghost_acquire central_g;
            /*assert b_orig_value == ();
            assume central_inv(central_g, this.loc);
            assume rc_inv(old_value, rc_g, this.loc);*/

            if old_value == 0 {
              Base.dispose(base_token);
              rc_g, central_g, pending_handle, base_token :=
                perform_exc_finish(rc_g, central_g, pending_handle, central_g.get().central.value);
            }
            assume central_inv(central_g, this.loc);

            ghost_release central_g;
          }
          ghost_release rc_g;
        }

        if ret_value == 0 {
          is_rc_zero := true;
        }
      }

      handle := pending_handle;
    }

    method release_exc(glinear base_token: Base.Token, glinear handle: RWLockExtToken.Token)
    requires Inv()
    requires handle.get() == RWLockExt.ExcTakenHandle()
    requires handle.loc().ExtLoc? && handle.loc().base_loc == base_token.loc()
    requires handle.loc() == this.loc
    {
      atomic_block ret_value := execute_atomic_store(this.exc, false) {
        ghost_acquire g;
        atomic_block _ := execute_atomic_noop(this.central) {
          ghost_acquire central_g;

          g, central_g :=
            RWLockExtToken.perform_exc_release(g, central_g, handle, base_token,
                central_g.get().central.value, g.get().phys_exc.value);

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
        atomic_block ret_value := execute_atomic_load(this.exc) { }
        exc_value := ret_value;
      }
    }

    /*private*/ method load_rc()
    returns (rc: uint32)
    requires Inv()
    {
      atomic_block ret_value := execute_atomic_load(this.rc) { }
      rc := ret_value;
    }

    method acquire_shared()
    returns (glinear handle: RWLockExtToken.Token)
    requires Inv()
    ensures exists a :: handle.get() == RWLockExt.SharedTakenHandle(a)
    ensures handle.loc() == this.loc
    decreases *
    {
      handle := RWLockExtToken.SEPCM.get_unit(this.loc);

      var done := false;

      while !done
      invariant done ==> exists a :: handle.get() == RWLockExt.SharedTakenHandle(a)
      invariant done ==> handle.loc() == this.loc
      decreases *
      {
        this.wait_for_exc_false();
        var cur_rc := this.load_rc();

        if cur_rc != 0xffff_ffff {
          // increment rc

          atomic_block ret_value := execute_atomic_compare_and_set_strong(this.rc, cur_rc, cur_rc + 1) {
            ghost_acquire g;
            ghost var ghostme := true;
            if ghostme && ret_value {
              RWLockExtToken.SEPCM.dispose(handle);
              g, handle := RWLockExtToken.perform_shared_pending(g, cur_rc as nat);
            }
            ghost_release g;
          }

          if ret_value {
            // check exc is false

            atomic_block exc_value := execute_atomic_load(this.exc) {
              ghost_acquire g;
              atomic_block _ := execute_atomic_noop(this.central) {
                ghost_acquire central_g;
                ghost var ghostme := true;
                if ghostme && !exc_value {
                  g, central_g, handle := RWLockExtToken.perform_shared_finish(
                        g, central_g, handle, central_g.get().central.value);
                }
                ghost_release central_g;
              }
              ghost_release g;
            }

            if !exc_value {
              done := true;
            } else {
              // abort

              atomic_block ret_value := execute_atomic_fetch_sub_uint32(this.rc, 1) {
                ghost_acquire g;
                g := perform_abort_shared(g, handle, old_value as nat);
                handle := RWLockExtToken.SEPCM.get_unit(handle.loc());
                ghost_release g;
              }
            }
          }
        }
      }
    }

    method release_shared(glinear handle: RWLockExtToken.Token)
    requires Inv()
    requires exists a :: handle.get() == RWLockExt.SharedTakenHandle(a)
    requires handle.loc() == this.loc
    {
      atomic_block _ := execute_atomic_fetch_sub_uint32(this.rc, 1) {
        ghost_acquire g;
        atomic_block _ := execute_atomic_noop(this.central) {
          ghost_acquire central_g;
          ghost var a :| handle.get() == RWLockExt.SharedTakenHandle(a);
          g, central_g :=
            RWLockExtToken.perform_release_shared(g, central_g, handle,
                central_g.get().central.value, a, g.get().phys_rc.value);
          ghost_release central_g;
        }
        ghost_release g;
      }
    }
  }

  method rwlock_new(glinear init_value: Base.Token)
  returns (rwlock: RWLock)
  ensures rwlock.Inv()
  {
    glinear var big_token := RWLockExtToken.init(init_value, 
        RWLockExt.M(Some(false), Some(0),
            Some(CentralState(false, 0, Some(init_value.get()))),
            false, false, 0, zero_map()));
    glinear var pe, rest := RWLockExtToken.split(big_token,
        PhysExcHandle(false),
        RWLockExt.M(None, Some(0),
            Some(CentralState(false, 0, Some(init_value.get()))),
            false, false, 0, zero_map()));
    glinear var rc, central := RWLockExtToken.split(rest,
        PhysRcHandle(0),
        CentralHandle(CentralState(false, 0, Some(init_value.get()))));

    ghost var loc := big_token.loc(); 
    var exc_atomic := new_atomic(false, pe, (v, g) => exc_inv(v, g, loc), {});
    var rc_atomic := new_atomic(0 as uint32, rc, (v, g) => rc_inv(v, g, loc), {});
    ghost var central_atomic := new_ghost_atomic(central, (g) => central_inv(g, loc),
        {exc_atomic.identifier(), rc_atomic.identifier()});

    rwlock := RWLock(exc_atomic, rc_atomic, central_atomic, loc);
  }
}
