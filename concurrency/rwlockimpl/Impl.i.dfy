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
      && (forall    g :: atomic_inv(this.central, (), g) <==> central_inv(g, this.loc))
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
        var exc_atomic := this.exc;
        var ret_value: bool;
        ghost var orig_value: bool, new_value: bool;
        glinear var g;
        ret_value, orig_value, new_value, g :=
            execute_atomic_compare_and_set_strong(exc_atomic, false, true);

        ghost var ghostme := true;
        if ghostme && ret_value {
          RWLockExtToken.SEPCM.dispose(pending_handle);
          g, pending_handle := RWLockExtToken.perform_exc_pending(g);
        }

        finish_atomic(exc_atomic, new_value, g);

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
        var rc_atomic := this.rc;
        ghost var central_atomic := this.central;

        var ret_value;
        ghost var orig_value, new_value;
        glinear var rc_g;

        ghost var b_orig_value, b_new_value, b_ret_value;
        glinear var central_g;

        ret_value, orig_value, new_value, rc_g := execute_atomic_load(rc_atomic);
        assert rc_atomic.identifier() != central_atomic.identifier();
        b_ret_value, b_orig_value, b_new_value, central_g := execute_atomic_noop(central_atomic);

        assert b_orig_value == ();
        assert central_inv(central_g, this.loc);
        assert rc_inv(orig_value, rc_g, this.loc);

        if orig_value == 0 {
          Base.dispose(base_token);
          rc_g, central_g, pending_handle, base_token :=
            perform_exc_finish(rc_g, central_g, pending_handle, central_g.get().central.value);
        }

        finish_atomic(central_atomic, b_new_value, central_g);
        finish_atomic(rc_atomic, new_value, rc_g);

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
      var exc_atomic := this.exc;
      ghost var ret_value;
      ghost var orig_value, new_value;
      glinear var g;

      ghost var b_orig_value, b_new_value, b_ret_value;
      glinear var central_g;

      ghost var central_atomic := this.central;

      ret_value, orig_value, new_value, g :=
          execute_atomic_store(exc_atomic, false);

      assert exc_atomic.identifier() != central_atomic.identifier();
      b_ret_value, b_orig_value, b_new_value, central_g := execute_atomic_noop(central_atomic);

      assert b_orig_value == ();
      assert central_inv(central_g, this.loc);
      assert exc_inv(orig_value, g, this.loc);

      g, central_g :=
        RWLockExtToken.perform_exc_release(g, central_g, handle, base_token,
            central_g.get().central.value, g.get().phys_exc.value);

      assert central_inv(central_g, this.loc);
      assert exc_inv(new_value, g, this.loc);

      finish_atomic(central_atomic, b_new_value, central_g);
      finish_atomic(exc_atomic, new_value, g);
    }

    /*private*/ method wait_for_exc_false()
    decreases *
    requires Inv()
    {
      var exc_value := true;
      while exc_value
      decreases *
      {
        var exc_atomic := this.exc;
        ghost var orig_value, new_value;
        glinear var g;
        exc_value, orig_value, new_value, g := execute_atomic_load(exc_atomic);
        finish_atomic(exc_atomic, new_value, g);
      }
    }

    method load_rc()
    returns (rc: uint32)
    requires Inv()
    {
      var rc_atomic := this.rc;
      ghost var orig_value, new_value;
      glinear var g;
      rc, orig_value, new_value, g := execute_atomic_load(rc_atomic);
      finish_atomic(rc_atomic, new_value, g);
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

          var rc_atomic := this.rc;
          var ret_value: bool;
          ghost var orig_value: uint32, new_value: uint32;
          glinear var g;
          ret_value, orig_value, new_value, g :=
              execute_atomic_compare_and_set_strong(rc_atomic, cur_rc, cur_rc + 1);

          ghost var ghostme := true;
          if ghostme && ret_value {
            RWLockExtToken.SEPCM.dispose(handle);
            g, handle := RWLockExtToken.perform_shared_pending(g, cur_rc as nat);
          }

          finish_atomic(rc_atomic, new_value, g);

          if ret_value {
            // check exc is false

            var exc_atomic := this.exc;
            var exc_value: bool;

            ghost var b_ret_value, b_orig_value, b_new_value;
            glinear var central_g;
            ghost var central_atomic := this.central;

            ghost var orig_value: bool, new_value: bool;

            exc_value, orig_value, new_value, g := execute_atomic_load(exc_atomic);

            assert exc_atomic.identifier() != central_atomic.identifier();
            b_ret_value, b_orig_value, b_new_value, central_g := execute_atomic_noop(central_atomic);

            assert b_orig_value == ();
            assert central_inv(central_g, this.loc);
            assert exc_inv(orig_value, g, this.loc);

            ghost var ghostme := true;
            if ghostme && !exc_value {
              g, central_g, handle := RWLockExtToken.perform_shared_finish(
                    g, central_g, handle, central_g.get().central.value);
            }

            finish_atomic(central_atomic, b_new_value, central_g);
            finish_atomic(exc_atomic, new_value, g);

            if !exc_value {
              done := true;
            } else {
              // abort

              var ret_value;
              ghost var orig_value, new_value: uint32;

              ret_value, orig_value, new_value, g :=
                  execute_atomic_fetch_sub_uint32(rc_atomic, 1);
              
              g := perform_abort_shared(g, handle, orig_value as nat);
              handle := RWLockExtToken.SEPCM.get_unit(handle.loc());

              finish_atomic(rc_atomic, new_value, g);
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
      var rc_atomic := this.rc;
      ghost var ret_value;
      ghost var orig_value, new_value;
      glinear var g;

      ghost var b_orig_value, b_new_value, b_ret_value;
      glinear var central_g;

      ghost var central_atomic := this.central;

      ret_value, orig_value, new_value, g :=
          execute_atomic_fetch_sub_uint32(rc_atomic, 1);

      assert rc_atomic.identifier() != central_atomic.identifier();
      b_ret_value, b_orig_value, b_new_value, central_g := execute_atomic_noop(central_atomic);

      assert b_orig_value == ();
      assert central_inv(central_g, this.loc);
      assert rc_inv(orig_value, g, this.loc);

      ghost var a :| handle.get() == RWLockExt.SharedTakenHandle(a);

      g, central_g :=
        RWLockExtToken.perform_release_shared(g, central_g, handle,
            central_g.get().central.value, a, g.get().phys_rc.value);

      assert central_inv(central_g, this.loc);
      assert rc_inv(new_value, g, this.loc);

      finish_atomic(central_atomic, b_new_value, central_g);
      finish_atomic(rc_atomic, new_value, g);
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
