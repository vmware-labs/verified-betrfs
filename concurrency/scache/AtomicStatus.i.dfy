include "../framework/Atomic.s.dfy"
include "rwlock/RwLock.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "cache/CacheResources.i.dfy"
include "../framework/GlinearOption.i.dfy"

module AtomicStatusImpl {
  import opened NativeTypes
  import opened Atomics
  import opened GlinearOption
  import opened GhostLoc
  import opened BitOps
  import opened Ptrs

  import opened CacheHandle
  import opened Constants
  import RwLock
  import Rw = RwLockToken

  import CacheResources
  import opened CacheStatusType

  const flag_zero : uint8 := 0;

  const flag_writeback : uint8 := 1;
  const flag_exc : uint8 := 2;
  const flag_accessed : uint8 := 4;
  const flag_unmapped : uint8 := 8;
  const flag_reading : uint8 := 16;
  const flag_clean : uint8 := 32;
  const flag_claim : uint8 := 64;

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

  const flag_exc_clean_claim : uint8 := 98;
  const flag_exc_accessed_clean_claim : uint8 := 102;
  const flag_exc_claim : uint8 := 66;
  const flag_exc_accessed_claim : uint8 := 70;
  const flag_accessed_claim : uint8 := 68;
  const flag_accessed_clean_claim : uint8 := 100;
  const flag_clean_claim : uint8 := 96;
  const flag_writeback_claim : uint8 := 65;
  const flag_writeback_accessed_claim : uint8 := 69;
  const flag_writeback_clean_claim : uint8 := 97;
  const flag_writeback_accessed_clean_claim : uint8 := 101;
  const flag_writeback_exc_claim : uint8 := 67;
  const flag_writeback_exc_accessed_claim : uint8 := 71;
  const flag_writeback_exc_clean_claim : uint8 := 99;
  const flag_writeback_exc_accessed_clean_claim : uint8 := 103;

  glinear datatype G = G(
    glinear rwlock: Rw.Token,
    glinear status: glOption<CacheResources.CacheStatus>
  )

  predicate state_inv(v: uint8, g: G, key: Key, rwlock_loc: Loc)
  {
    && g.rwlock.val.M?
    && g.rwlock.val.central.CentralState?
    && g.rwlock.val == RwLock.CentralHandle(g.rwlock.val.central)

    && g.rwlock.val.central.stored_value.is_handle(key)

    && g.rwlock.loc == rwlock_loc

    && var flag := g.rwlock.val.central.flag;

    && flags_field_inv(v, flag, key)
    /*&& (g.rwlock.val.central.flag == RwLock.Reading_ExcLock ==>
      g.status.glNone?
    )*/
    && (g.status.glNone? ==>
        && (
        || v == flag_unmapped
        || v == flag_exc_claim
        || v == flag_exc_accessed_claim
        || v == flag_exc_reading
        || v == flag_exc_accessed_reading
        || v == flag_exc_clean_claim
        || v == flag_exc_accessed_clean_claim
        || v == flag_exc_reading_clean
        || v == flag_exc_accessed_reading_clean
        || v == flag_reading_clean
        || v == flag_accessed_reading_clean
        )
        && (v == flag_unmapped ==>
          && g.rwlock.val.central.stored_value.CacheEmptyHandle?
        )
        && (v == flag_exc_claim || v == flag_exc_accessed_claim || v == flag_exc_clean_claim
            || v == flag_exc_accessed_clean_claim ==>
          && g.rwlock.val.central.stored_value.CacheEntryHandle?
        )
    )
    && (g.status.glSome? ==>
      && g.status.value.cache_idx == key.cache_idx
      && status_inv(v, g.status.value.status, key)
      && g.rwlock.val.central.stored_value.CacheEntryHandle?
    )
    && (flag == RwLock.ExcLock_Clean ==> g.status.glNone?)
    && (flag == RwLock.ExcLock_Dirty ==> g.status.glNone?)
    && (flag == RwLock.PendingExcLock ==> g.status.glSome?)
  }

  predicate flags_field_inv(v: uint8, flag: RwLock.Flag, key: Key)
  {
    && (flag == RwLock.Available ==> (
      || v == flag_zero
      || v == flag_accessed
      || v == flag_clean
      || v == flag_accessed_clean
    ))
    && (flag == RwLock.Writeback ==> (
      || v == flag_writeback
      || v == flag_writeback_accessed
    ))
    && (flag == RwLock.ExcLock_Clean ==> (
      || v == flag_exc_clean_claim
      || v == flag_exc_accessed_clean_claim
    ))
    && (flag == RwLock.ExcLock_Dirty ==> (
      || v == flag_exc_claim
      || v == flag_exc_accessed_claim
    ))
    && (flag == RwLock.Claimed ==> (
      || v == flag_claim
      || v == flag_accessed_claim
      || v == flag_clean_claim
      || v == flag_accessed_clean_claim
    ))
    && (flag == RwLock.Writeback_Claimed ==> (
      || v == flag_writeback_claim
      || v == flag_writeback_accessed_claim
      || v == flag_writeback_clean_claim
      || v == flag_writeback_accessed_clean_claim
    ))
    && (flag == RwLock.PendingExcLock ==> (
      || v == flag_exc_claim
      || v == flag_exc_accessed_claim
      || v == flag_exc_clean_claim
      || v == flag_exc_accessed_clean_claim
    ))
    && (flag == RwLock.Writeback_PendingExcLock ==> (
      || v == flag_writeback_exc_claim
      || v == flag_writeback_exc_accessed_claim
      || v == flag_writeback_exc_clean_claim
      || v == flag_writeback_exc_accessed_clean_claim
    ))
    && (flag == RwLock.Unmapped ==> v == flag_unmapped)
    && (flag == RwLock.Reading ==>
      || v == flag_reading
      || v == flag_reading_clean
      || v == flag_accessed_reading_clean
    )
    && (flag == RwLock.Reading_ExcLock ==> v == flag_exc_reading || v == flag_exc_accessed_reading)
  }

  predicate status_inv(v: uint8, status: Status, key: Key)
  {
    && (status == Clean ==> (
      || v == flag_clean
      || v == flag_clean_claim
      || v == flag_exc_clean_claim
      || v == flag_accessed_clean
      || v == flag_accessed_clean_claim
      || v == flag_exc_accessed_clean_claim
    ))
    && (status == Dirty ==> (
      || v == flag_zero
      || v == flag_claim
      || v == flag_exc_claim
      || v == flag_accessed
      || v == flag_accessed_claim
      || v == flag_exc_accessed_claim
    ))
    && (status == Writeback ==> (
      || v == flag_writeback
      || v == flag_writeback_claim
      || v == flag_writeback_exc_claim
      || v == flag_writeback_accessed
      || v == flag_writeback_accessed_claim
      || v == flag_writeback_exc_accessed_claim
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
        glinear m: glOption<Rw.WritebackObtainedToken>,
        glinear disk_write_ticket: glOption<CacheResources.DiskWriteTicket>)
    requires this.inv()
    ensures !success ==> m.glNone?
    ensures !success ==> disk_write_ticket.glNone?
    ensures success ==>
        && m.glSome?
        && m.value.is_handle(key)
        && m.value.b.CacheEntryHandle?
        && disk_write_ticket.glSome?
        && disk_write_ticket.value.writes(
            m.value.b.idx.v as int,
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

            rwlock, handle := Rw.perform_TakeWriteback(rwlock);

            assert unwrap_value(status).cache_idx == key.cache_idx;
            assert Rw.borrow_wb(handle).cache_entry.cache_idx == key.cache_idx;
            stat, ticket := CacheResources.initiate_writeback(
                Rw.borrow_wb(handle).cache_entry, unwrap_value(status));

            new_g := G(rwlock, glSome(stat));
            m := glSome(Rw.WritebackObtainedToken(handle.val.writeback.b, handle));
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
              rwlock, handle := Rw.perform_TakeWriteback(rwlock);
              stat, ticket := CacheResources.initiate_writeback(
                  Rw.borrow_wb(handle).cache_entry, unwrap_value(status));
              new_g := G(rwlock, glSome(stat));
              m := glSome(Rw.WritebackObtainedToken(handle.val.writeback.b, handle));
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
        glinear handle: Rw.WritebackObtainedToken,
        glinear disk_write_stub: CacheResources.DiskWriteStub)
    requires this.inv()
    requires handle.token.loc == this.rwlock_loc
    //requires disk_write_stub.loc == key.cr_loc
    requires handle.is_handle(key)
    requires handle.b.CacheEntryHandle?
    requires 0 <= handle.b.cache_entry.disk_idx
               < 0x1_0000_0000_0000_0000
    requires disk_write_stub.disk_idx == handle.b.cache_entry.disk_idx
    {
      glinear var wb;
      glinear match handle { case WritebackObtainedToken(_, t) => { wb := t; } }

      // Unset Writeback; set Clean
      atomic_block var _ := execute_atomic_fetch_xor_uint8(this.atomic, flag_writeback_clean) {
        ghost_acquire old_g;
        glinear var new_g;

        //var fl := old_g.rwlock.val.central.flag;
        glinear var G(rwlock, status) := old_g;

        rwlock, wb := Rw.pre_ReleaseWriteback(rwlock, wb);

        glinear var stat := CacheResources.finish_writeback(
            Rw.borrow_wb(wb).cache_entry, unwrap_value(status), disk_write_stub);

        rwlock := Rw.perform_ReleaseWriteback(rwlock, wb);
        new_g := G(rwlock, glSome(stat));

        assert state_inv(new_value, new_g, key, this.rwlock_loc);

        ghost_release new_g;
      }
    }

    method try_check_writeback_isnt_set(ghost t: int, glinear m: Rw.Token)
    returns (success: bool, clean: bool, glinear m': Rw.Token,
        glinear status: glOption<CacheResources.CacheStatus>)
    requires this.inv()
    requires m.val.M?
    requires m.val.exc.ExcPendingAwaitWriteback?
    requires m.val == RwLock.ExcHandle(RwLock.ExcPendingAwaitWriteback(t,
        m.val.exc.b))
    requires m.loc == rwlock_loc
    ensures !success ==> m' == m
    ensures !success ==> status.glNone?
    ensures success ==> m'.val == RwLock.ExcHandle(RwLock.ExcPending(t, 0, clean, m.val.exc.b))
        && m'.loc == rwlock_loc
    ensures success ==> status.glSome? && status.value.is_status(key.cache_idx,
          (if clean then Clean else Dirty))
    {
      atomic_block var f := execute_atomic_load(this.atomic) {
        ghost_acquire old_g;
        glinear var new_g;

        var fl := old_g.rwlock.val.central.flag;
        if fl == RwLock.Writeback || fl == RwLock.Writeback_PendingExcLock
        {
          new_g := old_g;
          m' := m;
          status := glNone;
          assert state_inv(new_value, new_g, key, rwlock_loc);
        } else {
          glinear var G(rwlock, status0) := old_g;
          assert m.val.exc == RwLock.ExcPendingAwaitWriteback(t, m.val.exc.b);
          assert m.val == RwLock.ExcHandle(m.val.exc);
          rwlock, m' := Rw.perform_TakeExcLockFinishWriteback(
            rwlock, m, bit_and_uint8(f, flag_clean) != 0);
          assert status0.glSome?;
          assert bit_and_uint8(f, flag_clean) != 0 ==>
              status0.value.status == Clean;
          assert bit_and_uint8(f, flag_clean) == 0 ==>
              status0.value.status == Dirty;
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
        glinear m: glOption<Rw.Token>,
        glinear handle_opt: glOption<Handle>)
    requires this.inv()
    ensures !success ==> m.glNone?
    ensures !success ==> handle_opt.glNone?
    ensures success ==> m.glSome?
        && m.value.val == RwLock.ReadHandle(RwLock.ReadPending)
        && m.value.loc == rwlock_loc
        && handle_opt.glSome?
        && handle_opt.value.is_handle(key)
        && handle_opt.value.CacheEmptyHandle?
    {
      // check first to reduce contention
      atomic_block var f := execute_atomic_load(atomic) { }

      if f != flag_unmapped {
        success := false;
        m := glNone;
        handle_opt := glNone;
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
            rwlock, exc_handle, h := Rw.perform_Withdraw_Alloc(rwlock);
            new_g := G(rwlock, status0);
            m := glSome(exc_handle);
            handle_opt := glSome(h);
            assert new_g.rwlock.val.central.stored_value
                == old_g.rwlock.val.central.stored_value;
            assert old_g.rwlock.val.central.stored_value.is_handle(key);
            assert new_g.rwlock.val.central.stored_value.is_handle(key);
            assert state_inv(new_value, new_g, key, rwlock_loc);
          } else {
            m := glNone;
            handle_opt := glNone;
            new_g := old_g;
            assert state_inv(new_value, new_g, key, rwlock_loc);
          }
          assert state_inv(new_value, new_g, key, rwlock_loc);

          ghost_release new_g;
        }

        success := did_set;
      }
    }

    method clear_exc_bit_during_load_phase(
        //ghost t:int,
        glinear r: Rw.Token)
    returns (glinear q: Rw.Token)
    requires this.inv()
    requires r.loc == this.rwlock_loc
    requires r.val.M?
    requires r.val.read.ReadPendingCounted?
    requires r.val == RwLock.ReadHandle(RwLock.ReadPendingCounted(r.val.read.t))
    ensures q.loc == this.rwlock_loc
    ensures q.val == RwLock.ReadHandle(RwLock.ReadObtained(r.val.read.t))
    {
      atomic_block var _ := execute_atomic_store(atomic, flag_accessed_reading_clean) {
        ghost_acquire old_g;
        glinear var new_g;
        var fl := old_g.rwlock.val.central.flag;
        glinear var G(rwlock, status) := old_g;
        rwlock, q := Rw.perform_ObtainReading(rwlock, r);
        new_g := G(rwlock, status);
        assert status.glNone?;
        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }

    method load_phase_finish(
        glinear r: Rw.Token,
        glinear handle: Handle,
        glinear status: CacheResources.CacheStatus)
    returns (glinear q: Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val.read.ReadObtained?
    requires r.val == RwLock.ReadHandle(RwLock.ReadObtained(r.val.read.t))
    requires handle.is_handle(key)
    requires handle.CacheEntryHandle?
    requires status.is_status(key.cache_idx, Clean)
    ensures q.loc == rwlock_loc
    ensures q.val == RwLock.SharedHandle(RwLock.SharedObtained(r.val.read.t, handle))
    {
      atomic_block var _ := execute_atomic_fetch_and_uint8(atomic, 0xff - flag_reading) {
        ghost_acquire old_g;
        glinear var new_g;
        var fl := old_g.rwlock.val.central.flag;
        glinear var G(rwlock, status_empty) := old_g;
        rwlock, q :=
            Rw.perform_Deposit_ReadingToShared(rwlock, r, handle);
        dispose_glnone(status_empty);
        new_g := G(rwlock, glSome(status));

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }


    method quicktest_is_exc_locked()
    returns (is_exc_locked: bool)
    {
      atomic_block var v := execute_atomic_load(atomic) { }
      return ((v as bv8) & (flag_exc as bv8)) as uint8 != 0;
    }

    method is_exc_locked_or_free(
        ghost t: int,
        glinear r: Rw.Token)
    returns (success: bool, is_accessed: bool, glinear r': Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val == RwLock.SharedHandle(RwLock.SharedPending(t))
    ensures !success ==> r == r'
    ensures success ==>
        && r'.val == RwLock.SharedHandle(RwLock.SharedPending2(t))
        && r'.loc == rwlock_loc
    {
      atomic_block var f := execute_atomic_load(atomic) {
        ghost_acquire old_g;
        glinear var new_g;
        var fl := old_g.rwlock.val.central.flag;
        if fl == RwLock.Available || fl == RwLock.Writeback
            || fl == RwLock.Claimed || fl == RwLock.Writeback_Claimed
            || fl == RwLock.Reading {
          glinear var G(rwlock, status) := old_g;
          rwlock, r' := Rw.perform_SharedCheckExc(rwlock, r, t);
          new_g := G(rwlock, status);
        } else {
          r' := r;
          new_g := old_g;
        }
        ghost_release new_g;
      }

      success := bit_and_uint8(f, bit_or_uint8(flag_exc, flag_unmapped)) == 0;
      is_accessed := bit_and_uint8(f, flag_accessed) != 0;
    }

    method mark_accessed(
        ghost t: int,
        glinear r: Rw.Token)
    returns (glinear r': Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val == RwLock.SharedHandle(RwLock.SharedPending2(t))
    requires 0 <= t < NUM_THREADS
    ensures r' == r
    {
      atomic_block var _ := execute_atomic_fetch_or_uint8(atomic, flag_accessed) {
        ghost_acquire old_g;
        glinear var new_g;

        glinear var G(rwlock, status) := old_g;
        rwlock, r' := Rw.possible_flags_SharedPending2(rwlock, r, t);

        new_g := G(rwlock, status);
        assert state_inv(new_value, new_g, key, rwlock_loc);

        ghost_release new_g;
      }
    }

    method clear_accessed()
    requires this.inv()
    {
      atomic_block var orig_value := execute_atomic_fetch_and_uint8(atomic, 0xff - flag_accessed)
      {
        ghost_acquire g;
        assert state_inv(new_value, g, key, rwlock_loc);
        ghost_release g;
      }
    }

    method is_reading(
        ghost t: int,
        glinear r: Rw.Token)
    returns (
      success: bool,
      glinear r': glOption<Rw.Token>,
      glinear handle: glOption<Rw.SharedObtainedToken>
    )
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val == RwLock.SharedHandle(RwLock.SharedPending2(t))
    requires 0 <= t < NUM_THREADS
    ensures !success ==> r' == glSome(r)
    ensures !success ==> handle == glNone
    ensures success ==>
        && r' == glNone
        && handle.glSome?
        && handle.value.is_handle(key)
        && handle.value.token.loc == rwlock_loc
        && handle.value.b.CacheEntryHandle?
        && handle.value.t == t
    {
      atomic_block var f := execute_atomic_load(atomic) {
        ghost_acquire old_g;
        glinear var new_g;
        var fl := old_g.rwlock.val.central.flag;
        if fl != RwLock.Reading && fl != RwLock.Reading_ExcLock {
          glinear var hand;
          glinear var G(rwlock, status0) := old_g;
          rwlock, hand := Rw.perform_SharedCheckReading(rwlock, r, t);
          handle := glSome(Rw.SharedObtainedToken(t, rwlock.val.central.stored_value, hand));
          r' := glNone;
          new_g := G(rwlock, status0);
        } else {
          r' := glSome(r);
          new_g := old_g;
          handle := glNone;
        }
        ghost_release new_g;
      }

      success := bit_and_uint8(f, flag_reading) == 0;
    }

    method take_exc_if_eq_clean()
    returns (
      success: bool,
      glinear m': glOption<Rw.Token>,
      ghost b: Handle,
      glinear status: glOption<CacheResources.CacheStatus>
    )
    requires this.inv()
    //requires m == RwLock.Internal(RwLock.SharedPending(t))
    ensures !success ==> m'.glNone? && status.glNone?
    ensures success ==>
        && m'.glSome?
        && m'.value.loc == rwlock_loc
        && m'.value.val == RwLock.ExcHandle(RwLock.ExcPending(-1, 0, true, b))
        && status == glSome(CacheResources.CacheStatus(
            key.cache_idx, Clean))
        && b.CacheEntryHandle?
        && b.is_handle(key)
    {
      atomic_block var did_set :=
          execute_atomic_compare_and_set_strong(atomic, flag_clean, flag_exc_clean_claim)
      {
        ghost_acquire old_g;
        glinear var new_g;
        if did_set {
          //m' := perform_SharedCheckExcFree(
          //    key, t, RwLock.Available, m, old_g.rwlock);
          //m' := perform_SharedCheckReading(
          //    key, t, RwLock.Available, m', old_g.rwlock);
          
          glinear var G(rwlock, status0) := old_g;
          glinear var m0;

          var fl := rwlock.val.central.flag;
          rwlock, m0 := Rw.perform_ThreadlessClaim(rwlock);
          rwlock, m0 := Rw.perform_ClaimToPending(rwlock, m0);

          //m', rwlock := perform_SharedToExc(
          //    key, t, RwLock.Available, m', rwlock);

          rwlock, m0 := Rw.perform_TakeExcLockFinishWriteback(
              rwlock, m0, true);

          m' := glSome(m0);
          b := rwlock.val.central.stored_value;

          new_g := G(rwlock, glNone);
          status := status0;
          assert state_inv(new_value, new_g, key, rwlock_loc);
        } else {
          new_g := old_g;
          m' := glNone;
          status := glNone;
          assert state_inv(new_value, new_g, key, rwlock_loc);
          b :| true;
        }
        ghost_release new_g;
      }

      success := did_set;
    }

    method set_to_free(
        glinear handle: Handle,
        glinear r: Rw.Token)
    requires this.inv()
    requires handle.is_handle(key)
    requires handle.CacheEmptyHandle?
    requires r.val == RwLock.ExcHandle(RwLock.ExcObtained(-1, true))
    requires r.loc == rwlock_loc
    {
      atomic_block var _ := execute_atomic_store(atomic, flag_unmapped)
      {
        ghost_acquire old_g;
        glinear var new_g;

        glinear var G(rwlock, empty_status) := old_g;

        var fl := rwlock.val.central.flag;
        rwlock := Rw.perform_Deposit_Unmap(rwlock, r, handle);

        dispose_anything(empty_status);
        new_g := G(rwlock, glNone);

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }

    method abandon_exc(glinear r: Rw.Token, glinear status: CacheResources.CacheStatus)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val.exc.ExcPending?
    requires r.val == RwLock.ExcHandle(RwLock.ExcPending(
        -1, r.val.exc.visited, true, r.val.exc.b))
    requires status == CacheResources.CacheStatus(key.cache_idx, Clean)
    {
      atomic_block var orig_value := execute_atomic_fetch_and_uint8(atomic, 0xff - flag_exc - flag_claim) {
        ghost_acquire old_g;
        glinear var new_g;
        glinear var G(rwlock, empty_status) := old_g;

        var fl := rwlock.val.central.flag;
        rwlock := Rw.perform_AbandonExcPending(rwlock, r);

        dispose_anything(empty_status);
        new_g := G(rwlock, glSome(status));

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }

    method abandon_reading_pending(
        glinear r: Rw.Token,
        glinear handle: Handle)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val == RwLock.ReadHandle(RwLock.ReadPending)
    requires handle.is_handle(key)
    requires handle.CacheEmptyHandle?
    {
      atomic_block var _ := execute_atomic_store(atomic, flag_unmapped) {
        ghost_acquire old_g;
        glinear var new_g;
        glinear var G(rwlock, empty_status) := old_g;

        var fl := rwlock.val.central.flag;
        rwlock := Rw.perform_Deposit_AbandonReadPending(rwlock, r, handle);

        dispose_anything(empty_status);
        new_g := G(rwlock, glNone);

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }

    method mark_dirty(
        glinear r: Rw.Token,
        glinear status: CacheResources.CacheStatus)
    returns (glinear r': Rw.Token, glinear status': CacheResources.CacheStatus)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val.exc.ExcObtained?
    requires r.val == RwLock.ExcHandle(r.val.exc)
    requires status.cache_idx == key.cache_idx
    requires status.status == Clean || status.status == Dirty
    ensures r'.loc == rwlock_loc
    ensures r'.val == RwLock.ExcHandle(r.val.exc.(clean := false))
    ensures status' == CacheResources.CacheStatus(key.cache_idx, Dirty)
    {
      atomic_block var _ := execute_atomic_fetch_and_uint8(atomic, 0xff - flag_clean) {
        ghost_acquire old_g;
        glinear var new_g;
        glinear var G(rwlock, empty_status) := old_g;

        rwlock, r' := Rw.perform_MarkDirty(rwlock, r);

        new_g := G(rwlock, empty_status);

        if (status.status == Clean) {
          status' := CacheResources.status_mark_dirty(status);
        } else {
          status' := status;
        }

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }

    method try_set_claim(glinear r: Rw.Token, ghost ss: RwLock.SharedState)
    returns (success: bool, glinear r': Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires ss.SharedObtained?
    requires r.val == RwLock.SharedHandle(ss)
    ensures !success ==> r' == r
    ensures success ==> r'.loc == r.loc
    ensures success ==> r'.val ==
        RwLock.ExcHandle(RwLock.ExcClaim(ss.t, ss.b))
    {
      // set claim bit
      // return 'true' iff it was not already set

      atomic_block var ret := execute_atomic_fetch_or_uint8(atomic, flag_claim) {
        ghost_acquire old_g;
        glinear var new_g;

        if bit_and_uint8(flag_claim, ret) == 0 {
          glinear var G(rwlock, status) := old_g;
          rwlock, r' := Rw.perform_SharedToClaim(rwlock, r, ss);
          new_g := G(rwlock, status);
          assert state_inv(new_value, new_g, key, rwlock_loc);
        } else {
          new_g := old_g;
          r' := r;
          assert state_inv(new_value, new_g, key, rwlock_loc);
        }

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }

      success := bit_and_uint8(flag_claim, ret) == 0;
    }

    method unset_claim(glinear r: Rw.Token)
    returns (glinear r': Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val.exc.ExcClaim?
    requires r.val == RwLock.ExcHandle(r.val.exc)
    requires r.val.exc.t != -1
    ensures r'.loc == r.loc
    ensures r'.val ==
        RwLock.SharedHandle(RwLock.SharedObtained(r.val.exc.t, r.val.exc.b))
    {
      atomic_block var _ := execute_atomic_fetch_and_uint8(atomic, 0xff - flag_claim) {
        ghost_acquire old_g;
        glinear var new_g;

        glinear var G(rwlock, status) := old_g;
        assert rwlock.val.M?;
        rwlock, r' := Rw.perform_ClaimToShared(rwlock, r);
        new_g := G(rwlock, status);

        ghost_release new_g;
      }
    }

    method set_exc(glinear r: Rw.Token)
    returns (glinear r': Rw.Token)
    requires this.inv()
    requires r.loc == rwlock_loc
    requires r.val.M?
    requires r.val.exc.ExcClaim?
    requires r.val == RwLock.ExcHandle(r.val.exc)
    ensures r'.loc == r.loc
    ensures r'.val == RwLock.ExcHandle(RwLock.ExcPendingAwaitWriteback(
        r.val.exc.t, r.val.exc.b));
    {
      atomic_block var _ := execute_atomic_fetch_or_uint8(atomic, flag_exc) {
        ghost_acquire old_g;
        glinear var new_g;

        glinear var G(rwlock, status) := old_g;
        assert rwlock.val.M?;
        rwlock, r' := Rw.perform_ClaimToPending(rwlock, r);
        new_g := G(rwlock, status);

        assert state_inv(new_value, new_g, key, rwlock_loc);
        ghost_release new_g;
      }
    }
  }
}
