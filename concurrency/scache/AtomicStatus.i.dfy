include "../framework/Atomic.s.dfy"
include "rwlock/RWLock.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "CacheResources.i.dfy"
include "GlinearOption.i.dfy"

module AtomicStatusImpl {
  import opened NativeTypes
  import opened Atomics
  import opened GlinearOption
  import opened GhostLoc

  import RW = RWLockExtToken
  import opened RWLockBase
  import RWLock

  import CacheResources

  const flag_zero : uint8 := 0;

  const flag_writeback : uint8 := 1;
  const flag_exc : uint8 := 2;
  const flag_accessed : uint8 := 4;
  const flag_unmapped : uint8 := 8;
  const flag_reading : uint8 := 16;
  const flag_clean : uint8 := 32;

  const flag_writeback_clean : uint8 := 33;
  const flag_exc_clean : uint8 := 34;
  const flag_accessed_clean : uint8 := 36;
  const flag_unmapped_clean : uint8 := 40;
  const flag_reading_clean : uint8 := 48;
  const flag_writeback_exc : uint8 := 3;
  const flag_writeback_accessed : uint8 := 5;
  const flag_exc_accessed : uint8 := 6;
  const flag_writeback_exc_accessed : uint8 := 7;
  const flag_accessed_reading : uint8 := 20;
  const flag_exc_reading : uint8 := 18;
  const flag_exc_accessed_reading : uint8 := 22;
  const flag_writeback_exc_clean : uint8 := 35;
  const flag_writeback_accessed_clean : uint8 := 37;
  const flag_exc_accessed_clean : uint8 := 38;
  const flag_writeback_exc_accessed_clean : uint8 := 39;
  const flag_accessed_reading_clean : uint8 := 52;
  const flag_exc_reading_clean : uint8 := 50;
  const flag_exc_accessed_reading_clean : uint8 := 54;

  glinear datatype G = G(
    glinear rwlock: RW.Token,
    glinear status: glOption<CacheResources.CacheStatus>
  )

  predicate state_inv(v: uint8, g: G, key: Key, rwlock_loc: Loc)
  {
    && g.rwlock.val.central.CentralState?
    && g.rwlock.val == RWLock.CentralHandle(g.rwlock.val.central)

    && g.rwlock.val.central.stored_value.is_handle(key)

    && g.rwlock.loc == rwlock_loc
    && rwlock_loc.ExtLoc?
    && rwlock_loc.base_loc == RWLock.Base.singleton_loc()

    && var flag := g.rwlock.val.central.flag;

    && flags_field_inv(v, flag, key)
    /*&& (g.rwlock.q.flags == RWLock.Reading_ExcLock ==>
      g.status.glNone?
    )*/
    && (g.status.glNone? ==>
        && (
        || v == flag_exc
        || v == flag_exc_accessed
        || v == flag_exc_reading
        || v == flag_exc_accessed_reading
        || v == flag_exc_clean
        || v == flag_exc_accessed_clean
        || v == flag_exc_reading_clean
        || v == flag_exc_accessed_reading_clean
        || v == flag_reading_clean
        || v == flag_accessed_reading_clean
    ))
    && (g.status.glSome? ==>
      && g.status.value.cache_idx == key.cache_idx
      && status_inv(v, g.status.value.status, key)
    )
    //&& (flag == RWLock.ExcLock_Clean ==> g.status.glNone?)
    //&& (flag == RWLock.ExcLock_Dirty ==> g.status.glNone?)
    && (flag == RWLock.PendingExcLock ==> g.status.glSome?)
  }

  predicate flags_field_inv(v: uint8, flag: RWLock.Flag, key: Key)
  {
    && (flag == RWLock.Available ==> (
      || v == flag_zero
      || v == flag_accessed
      || v == flag_clean
      || v == flag_accessed_clean
    ))
    && (flag == RWLock.Writeback ==> (
      || v == flag_writeback
      || v == flag_writeback_accessed
    ))
    && (flag == RWLock.ExcLock_Clean ==> (
      || v == flag_exc_clean
      || v == flag_exc_accessed_clean
    ))
    && (flag == RWLock.ExcLock_Dirty ==> (
      || v == flag_exc
      || v == flag_exc_accessed
    ))
    && (flag == RWLock.PendingExcLock ==> (
      || v == flag_exc
      || v == flag_exc_accessed
      || v == flag_exc_clean
      || v == flag_exc_accessed_clean
    ))
    && (flag == RWLock.Writeback_PendingExcLock ==> (
      || v == flag_writeback_exc
      || v == flag_writeback_exc_accessed
      || v == flag_writeback_exc_clean
      || v == flag_writeback_exc_accessed_clean
    ))
    && (flag == RWLock.Unmapped ==> v == flag_unmapped)
    && (flag == RWLock.Reading ==>
      || v == flag_reading
      || v == flag_reading_clean
      || v == flag_accessed_reading_clean
    )
    && (flag == RWLock.Reading_ExcLock ==> v == flag_exc_reading || v == flag_exc_accessed_reading)
  }
  
  predicate status_inv(v: uint8, status: CacheResources.Status, key: Key)
  {
    && (status == CacheResources.Empty ==> (
      v == flag_unmapped
    ))
    && (status == CacheResources.Reading ==> (
      false
    ))
    && (status == CacheResources.Clean ==> (
      || v == flag_clean
      || v == flag_exc_clean
      || v == flag_accessed_clean
      || v == flag_exc_accessed_clean
    ))
    && (status == CacheResources.Dirty ==> (
      || v == flag_zero
      || v == flag_accessed
    ))
    && (status == CacheResources.Writeback ==> (
      || v == flag_writeback
      || v == flag_writeback_exc
      || v == flag_writeback_accessed
      || v == flag_writeback_exc_accessed
    ))
  }
  
  datatype AtomicStatus = AtomicStatus(
    atomic: Atomic<uint8, G>,
    ghost rwlock_loc: Loc,
    ghost key: Key
  )
  {
    predicate inv()
    {
      forall v, g :: atomic_inv(this.atomic, v, g) <==> state_inv(v, g, key, this.rwlock_loc)
    }

    method try_acquire_writeback(with_access: bool)
    returns (success: bool,
        glinear m: glOption<RW.WritebackObtainedToken>,
        glinear disk_write_ticket: glOption<CacheResources.DiskWriteTicket>)
    requires this.inv()
    ensures !success ==> m.glNone?
    ensures !success ==> disk_write_ticket.glNone?
    ensures success ==>
        && m.glSome?
        && m.value.is_handle(key)
        && disk_write_ticket.glSome?
        && disk_write_ticket.value.writes(
            m.value.b.idx.v as uint64,
            m.value.b.data.s)
    {
      atomic_block var cur_flag := execute_atomic_load(this.atomic) { }

      if !(cur_flag == flag_zero
          || (with_access && cur_flag == flag_accessed)) {
        m := glNone;
        disk_write_ticket := glNone;
        success := false;
      } else {
        atomic_block var did_set :=
            execute_atomic_compare_and_set_strong(this.atomic, flag_zero, flag_writeback)
        {
          ghost_acquire old_g;

          glinear var new_g;

          ghost var ghosty := true;
          if did_set && ghosty {
            glinear var handle, ticket, stat;
            glinear var G(rwlock, status) := old_g;

            rwlock, handle := RW.perform_TakeWriteback(rwlock);

            assert unwrap_value(status).cache_idx == key.cache_idx;
            assert RW.borrow_wb(handle).cache_entry.cache_idx == key.cache_idx;
            stat, ticket := CacheResources.initiate_writeback(
                RW.borrow_wb(handle).cache_entry, unwrap_value(status));

            new_g := G(rwlock, glSome(stat));
            m := glSome(RW.WritebackObtainedToken(handle.val.writeback.b, handle));
            disk_write_ticket := glSome(ticket);
            assert state_inv(new_value, new_g, key, this.rwlock_loc);
          } else {
            m := glNone;
            new_g := old_g;
            disk_write_ticket := glNone;
            assert state_inv(new_value, new_g, key, this.rwlock_loc);
          }
          assert state_inv(new_value, new_g, key, this.rwlock_loc);

          ghost_release new_g;
        }

        if did_set {
          success := true;
        } else if !with_access {
          success := false;
        } else {
          atomic_block var did_set :=
              execute_atomic_compare_and_set_strong(this.atomic, flag_accessed, flag_writeback_accessed)
          {
            ghost_acquire old_g;
            glinear var new_g;
            dispose_glnone(m);
            dispose_glnone(disk_write_ticket);

            if did_set {
              glinear var handle, stat, ticket;
              glinear var G(rwlock, status) := old_g;
              rwlock, handle := RW.perform_TakeWriteback(rwlock);
              stat, ticket := CacheResources.initiate_writeback(
                  RW.borrow_wb(handle).cache_entry, unwrap_value(status));
              new_g := G(rwlock, glSome(stat));
              m := glSome(RW.WritebackObtainedToken(handle.val.writeback.b, handle));
              disk_write_ticket := glSome(ticket);
            } else {
              new_g := old_g;
              m := glNone;
              disk_write_ticket := glNone;
            }
            assert state_inv(new_value, new_g, key, this.rwlock_loc);

            ghost_release new_g;
          }

          success := did_set;
        }
      }
    }

    method release_writeback(
        glinear handle: RW.WritebackObtainedToken,
        glinear disk_write_stub: CacheResources.DiskWriteStub)
    requires this.inv()
    requires handle.token.loc == this.rwlock_loc
    //requires disk_write_stub.loc == key.cr_loc
    requires handle.is_handle(key)
    requires 0 <= handle.b.cache_entry.disk_idx
               < 0x1_0000_0000_0000_0000
    requires disk_write_stub.disk_idx == handle.b.cache_entry.disk_idx as uint64
    {
      glinear var wb;
      glinear match handle { case WritebackObtainedToken(_, t) => { wb := t; } }

      // Unset Writeback; set Clean
      atomic_block var _ := execute_atomic_fetch_xor_uint8(this.atomic, flag_writeback_clean) {
        ghost_acquire old_g;
        glinear var new_g;

        //var fl := old_g.rwlock.val.central.flag;
        glinear var G(rwlock, status) := old_g;

        rwlock, wb := RW.pre_ReleaseWriteback(rwlock, wb);

        glinear var stat := CacheResources.finish_writeback(
            RW.borrow_wb(wb).cache_entry, unwrap_value(status), disk_write_stub);

        rwlock := RW.perform_ReleaseWriteback(rwlock, wb);
        new_g := G(rwlock, glSome(stat));

        assert state_inv(new_value, new_g, key, this.rwlock_loc);

        ghost_release new_g;
      }
    }

    method try_check_writeback_isnt_set(ghost t: int, glinear m: RW.Token)
    returns (success: bool, clean: bool, glinear m': RW.Token,
        glinear status: glOption<CacheResources.CacheStatus>)
    requires this.inv()
    requires m.val.exc.ExcPendingAwaitWriteback?
    requires m.val == RWLock.ExcHandle(RWLock.ExcPendingAwaitWriteback(t,
        m.val.exc.b))
    requires m.loc == rwlock_loc
    ensures !success ==> m' == m
    ensures !success ==> status.glNone?
    ensures success ==> m'.val == RWLock.ExcHandle(RWLock.ExcPending(t, 0, clean, m.val.exc.b))
        && m'.loc == rwlock_loc
    ensures success ==> status.glSome? && status.value.is_status(key.cache_idx,
          (if clean then CacheResources.Clean else CacheResources.Dirty))
    {
      atomic_block var f := execute_atomic_load(this.atomic) {
        ghost_acquire old_g;
        glinear var new_g;

        var fl := old_g.rwlock.val.central.flag;
        if fl == RWLock.Writeback || fl == RWLock.Writeback_PendingExcLock
        {
          new_g := old_g;
          m' := m;
          status := glNone;
          assert state_inv(new_value, new_g, key, rwlock_loc);
        } else {
          glinear var G(rwlock, status0) := old_g;
          assert m.val.exc == RWLock.ExcPendingAwaitWriteback(t, m.val.exc.b);
          assert m.val == RWLock.ExcHandle(m.val.exc);
          rwlock, m' := RW.perform_TakeExcLockFinishWriteback(
            rwlock, m, bit_and_uint8(f, flag_clean) != 0);
          assert status0.glSome?;
          assert bit_and_uint8(f, flag_clean) != 0 ==>
              status0.value.status == CacheResources.Clean;
          assert bit_and_uint8(f, flag_clean) == 0 ==>
              status0.value.status == CacheResources.Dirty;
          status := status0;
          new_g := G(rwlock, glNone);
          assert state_inv(new_value, new_g, key, rwlock_loc);
        }

        ghost_release new_g;
      }

      success := bit_and_uint8(f, flag_writeback) == 0;
      clean := bit_and_uint8(f, flag_clean) != 0;
    }

    method try_alloc()
    returns (success: bool,
        glinear m: glOption<RW.Token>,
        glinear handle_opt: glOption<Handle>,
        glinear status: glOption<CacheResources.CacheStatus>)
    requires this.inv()
    ensures !success ==> m.glNone?
    ensures !success ==> handle_opt.glNone?
    ensures !success ==> status.glNone?
    ensures success ==> m.glSome?
        && m.value.val == RWLock.ReadHandle(RWLock.ReadPending)
        && m.value.loc == rwlock_loc
        && handle_opt.glSome?
        && handle_opt.value.is_handle(key)
        && status.glSome?
        && status.value.is_status(key.cache_idx, CacheResources.Empty)
    {
      // check first to reduce contention
      atomic_block var f := execute_atomic_load(atomic) { }

      if f != flag_unmapped {
        success := false;
        m := glNone;
        handle_opt := glNone;
        status := glNone;
      } else {
        atomic_block var did_set := execute_atomic_compare_and_set_strong(
            atomic, flag_unmapped, flag_exc_reading)
        {
          ghost_acquire old_g;
          glinear var new_g;

          assert atomic_inv(this.atomic, old_value, old_g);
          assert state_inv(old_value, old_g, key, rwlock_loc);

          if did_set {
            glinear var exc_handle, h;
            glinear var G(rwlock, status0) := old_g;
            rwlock, exc_handle, h := RW.perform_Withdraw_Alloc(rwlock);
            status := status0;
            new_g := G(rwlock, glNone);
            m := glSome(exc_handle);
            handle_opt := glSome(h);
            assert status.glSome?;
            assert status.value.status == CacheResources.Empty;
            assert new_g.rwlock.val.central.stored_value
                == old_g.rwlock.val.central.stored_value;
            assert old_g.rwlock.val.central.stored_value.is_handle(key);
            assert new_g.rwlock.val.central.stored_value.is_handle(key);
            assert state_inv(new_value, new_g, key, rwlock_loc);
          } else {
            m := glNone;
            handle_opt := glNone;
            status := glNone;
            new_g := old_g;
            assert state_inv(new_value, new_g, key, rwlock_loc);
          }
          assert state_inv(new_value, new_g, key, rwlock_loc);

          ghost_release new_g;
        }

        success := did_set;
      }
    }

    /*

    method clear_exc_bit_during_load_phase(t:int,
        glinear r: RW.Token)
    returns (glinear q: RW.Token)
    requires this.inv()
    requires r == RWLock.Internal(RWLock.ReadingPendingCounted(key, t))
    ensures q == RWLock.Internal(RWLock.ReadingObtained(key, t))
    {
      atomic_write(atomic, flag_accessed_reading_clean);

      ///// Begin jank
      ///// Setup:
      var v := flag_accessed_reading_clean;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume new_value == v;
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      var fl := old_g.rwlock.q.flags;
      glinear var G(rwlock, status) := old_g;
      rwlock, q := RW.perform_ObtainReading(key, t, fl, rwlock, r);
      new_g := G(rwlock, status);
      assert status.glNone?;
      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method load_phase_finish(t: int,
        glinear r: RW.Token, glinear handle: RWLock.Handle,
        glinear status: CacheResources.R)
    returns (glinear q: RW.Token, /*readonly*/ glinear handle_out: RWLock.Handle)
    requires this.inv()
    requires r == RWLock.Internal(RWLock.ReadingObtained(key, t))
    requires handle.is_handle(key)
    requires status == CacheResources.CacheStatus(key.cache_idx,
        CacheResources.Clean)
    ensures q == RWLock.Internal(RWLock.SharedLockObtained(key, t))
    ensures handle_out == handle
    {
      var orig_value := fetch_and(atomic, 0xff - flag_reading);

      ///// Begin jank
      ///// Setup:
      var v := 0xff - flag_reading;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume orig_value == old_v;
      assume new_value == bit_and(old_v, v);
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      var fl := old_g.rwlock.q.flags;
      glinear var G(rwlock, status_empty) := old_g;
      RW.pre_ReadingToShared(key, t, fl, rwlock, r);
      dispose_glnone(status_empty);
      rwlock, q, handle_out :=
          RW.perform_ReadingToShared(key, t, fl, rwlock, r, handle);
      new_g := G(rwlock, glSome(status));

      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method quicktest_is_exc_locked()
    returns (is_exc_locked: bool)
    {
      var v := atomic_read(atomic);
      return ((v as bv8) & (flag_exc as bv8)) as uint8 != 0;
    }

    method is_exc_locked_or_free(
        t: int,
        glinear r: RW.Token)
    returns (success: bool, is_accessed: bool, glinear r': RW.Token)
    requires this.inv()
    requires r == RWLock.Internal(RWLock.SharedLockPending(key, t))
    ensures !success ==> r == r'
    ensures success ==> r' == 
        RWLock.Internal(RWLock.SharedLockPending2(key, t))
    {
      var f := atomic_read(atomic);

      ///// Begin jank
      ///// Setup:
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume new_value == old_v;
      assume f == old_v;
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      var fl := old_g.rwlock.q.flags;
      if fl == RWLock.Available || fl == RWLock.Writeback
          || fl == RWLock.Reading {
        r' := RW.perform_SharedCheckExcFree(
            key, t, old_g.rwlock.q.flags,
            r, old_g.rwlock);
        new_g := old_g;
      } else {
        r' := r;
        new_g := old_g;
      }
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank

      success := bit_and(f, bit_or(flag_exc, flag_unmapped)) == 0;
      is_accessed := bit_and(f, flag_accessed) != 0;
    }

    method mark_accessed(
        t: int,
        shared r: RW.Token)
    requires this.inv()
    requires r == RWLock.Internal(RWLock.SharedLockPending2(key, t))
    {
      var orig_value := fetch_or(atomic, flag_accessed);

      ///// Begin jank
      ///// Setup:
      var v := flag_accessed;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume orig_value == old_v;
      assume new_value == bit_or(old_v, v);
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      RW.possible_flags_SharedLockPending2(key, t, old_g.rwlock.q.flags,
          r, old_g.rwlock);
      new_g := old_g;
      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method clear_accessed()
    requires this.inv()
    {
      var orig_value := fetch_and(atomic, 0xff - flag_accessed);

      ///// Begin jank
      ///// Setup:
      var v := 0xff - flag_accessed;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume orig_value == old_v;
      assume new_value == bit_and(old_v, v);
      assume atomic_inv(atomic, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      new_g := old_g;
      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method is_reading(
        t: int,
        glinear r: RW.Token)
    returns (
      success: bool,
      glinear r': RW.Token,
      /*readonly*/ glinear handle: glOption<RWLock.Handle>
    )
    requires this.inv()
    requires r == RWLock.Internal(RWLock.SharedLockPending2(key, t))
    ensures !success ==> r == r'
    ensures !success ==> handle == glNone
    ensures success ==>
        && r' == RWLock.Internal(RWLock.SharedLockObtained(key, t))
        && handle.glSome?
        && handle.value.is_handle(key)
    {
      var f := atomic_read(atomic);

      ///// Begin jank
      ///// Setup:
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume new_value == old_v;
      assume f == old_v;
      assume atomic_inv(atomic, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      var fl := old_g.rwlock.q.flags;
      if fl != RWLock.Reading && fl != RWLock.Reading_ExcLock {
        glinear var hand;
        r', hand := RW.perform_SharedCheckReading(
            key, t, old_g.rwlock.q.flags,
            r, old_g.rwlock);
        new_g := old_g;
        handle := glSome(hand);
      } else {
        r' := r;
        new_g := old_g;
        handle := glNone;
      }
      ///// Teardown:
      assert atomic_inv(atomic, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank

      success := bit_and(f, flag_reading) == 0;
    }

    method take_exc_if_eq_clean()
    returns (
      success: bool,
      glinear m': glOption<RW.Token>,
      glinear status: glOption<CacheResources.R>,
      /*readonly*/ glinear handle: glOption<RWLock.Handle>
    )
    requires this.inv()
    //requires m == RWLock.Internal(RWLock.SharedLockPending(key, t))
    ensures !success ==> m'.glNone? && status.glNone? && handle.glNone?
    ensures success ==>
        && m' == glSome(RWLock.Internal(RWLock.ExcLockPending(key, -1, 0, true)))
        && status == glSome(CacheResources.CacheStatus(
            key.cache_idx, CacheResources.Clean))
        && handle.glSome?
        && handle.value.is_handle(key)
    {
      var did_set := compare_and_set(atomic, flag_clean, flag_exc_clean);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_clean;
      var v2 := flag_exc_clean;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume old_v == v1 ==> new_value == v2 && did_set;
      assume old_v != v1 ==> new_value == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:
      if did_set {
        //m' := perform_SharedCheckExcFree(
        //    key, t, RWLock.Available, m, old_g.rwlock);
        //m' := perform_SharedCheckReading(
        //    key, t, RWLock.Available, m', old_g.rwlock);
        
        glinear var G(rwlock, status0) := old_g;
        glinear var m0, handle';

        var fl := rwlock.q.flags;
        rwlock, m0, handle' := RW.perform_ThreadlessExc(key, rwlock, fl);

        //m', rwlock := perform_SharedToExc(
        //    key, t, RWLock.Available, m', rwlock);

        rwlock, m0 := RW.perform_TakeExcLockFinishWriteback(
            key, -1, RWLock.PendingExcLock, true, rwlock, m0);

        new_g := G(rwlock, glNone);
        status := status0;
        m' := glSome(m0);
        handle := glSome(handle');
        assert state_inv(new_value, new_g, key, rwlock_loc);
      } else {
        new_g := old_g;
        m' := glNone;
        status := glNone;
        handle := glNone;
        assert state_inv(new_value, new_g, key, rwlock_loc);
      }
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank

      success := did_set;
    }

    method set_to_free(
        glinear handle: RWLock.Handle,
        glinear status: CacheResources.R,
        glinear r: RW.Token)
    requires this.inv()
    requires handle.is_handle(key)
    requires status == CacheResources.CacheStatus(
        key.cache_idx,
        CacheResources.Empty)
    requires r == RWLock.Internal(RWLock.ExcLockObtained(key, -1, true))
    {
      atomic_write(atomic, flag_unmapped);

      ///// Begin jank
      ///// Setup:
      var v := flag_unmapped;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume new_value == v;
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;
      ///// Transfer:

      glinear var G(rwlock, empty_status) := old_g;

      var fl := rwlock.q.flags;
      rwlock := RW.perform_unmap(key, fl, true, rwlock, handle, r);

      dispose_glnone(empty_status);
      new_g := G(rwlock, glSome(status));

      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method abandon_exc(
        glinear status: CacheResources.R,
        glinear r: RW.Token,
        /*readonly*/ glinear handle: RWLock.Handle)
    requires this.inv()
    requires status == CacheResources.CacheStatus(
        key.cache_idx,
        CacheResources.Clean)
    requires r.Internal? && r.q.ExcLockPending?
    requires r == RWLock.Internal(RWLock.ExcLockPending(key, -1,
        r.q.visited, true))
    requires handle.is_handle(key)
    {
      var orig_value := fetch_and(atomic, 0xff - flag_exc);

      ///// Begin jank
      ///// Setup:
      var v := 0xff - flag_exc;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume orig_value == old_v;
      assume new_value == bit_and(old_v, v);
      assume atomic_inv(atomic, old_v, old_g);
      glinear var new_g;
      ///// Transfer:

      glinear var G(rwlock, empty_status) := old_g;

      var fl := rwlock.q.flags;
      var visited := r.q.visited;
      rwlock := RW.abandon_ExcLockPending(key, fl, visited, true, r, rwlock, handle);

      dispose_glnone(empty_status);
      new_g := G(rwlock, glSome(status));

      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(atomic, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }

    method abandon_reading_pending(
        glinear status: CacheResources.R,
        glinear r: RW.Token,
        /*readonly*/ glinear handle: RWLock.Handle)
    requires this.inv()
    requires status == CacheResources.CacheStatus(
        key.cache_idx,
        CacheResources.Empty)
    requires r == RWLock.Internal(RWLock.ReadingPending(key))
    requires handle.is_handle(key)
    {
      atomic_write(atomic, flag_unmapped);

      ///// Begin jank
      ///// Setup:
      var v := flag_unmapped;
      var old_v: uint8;
      var new_value: uint8;
      glinear var old_g: G := unsafe_obtain();
      assume new_value == v;
      assume atomic_inv(a, old_v, old_g);
      glinear var new_g;

      ///// Transfer:

      glinear var G(rwlock, empty_status) := old_g;

      var fl := rwlock.q.flags;
      rwlock := RW.abandon_ReadingPending(key, fl, r, rwlock, handle);

      dispose_glnone(empty_status);
      new_g := G(rwlock, glSome(status));

      assert state_inv(new_value, new_g, key, rwlock_loc);
      ///// Teardown:
      assert atomic_inv(a, new_value, new_g);
      unsafe_dispose(new_g);
      ///// End jank
    }*/
  }
}
