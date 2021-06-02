include "../framework/Atomic.s.dfy"
include "rwlock/RWLock.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "CacheResources.i.dfy"
include "../../lib/Base/LinearOption.i.dfy"

module AtomicStatusImpl {
  import opened NativeTypes
  import opened Atomics
  import opened LinearOption

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
    glinear status: CacheResources.Token
  )

  type AtomicStatus = Atomic<uint8, G>

  predicate state_inv(v: uint8, g: G, key: Key)
  {
    && g.rwlock.get().central.CentralState?
    && g.rwlock.get() == RWLock.CentralHandle(g.rwlock.get().central)

    && var flag := g.rwlock.get().central.flag;

    && flags_field_inv(v, flag, key)
    /*&& (g.rwlock.q.flags == RWLock.Reading_ExcLock ==>
      g.status.lNone?
    )*/
    && (key.cache_idx !in g.status.get().statuses ==>
        && g.status.get() == CacheResources.unit()
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
    && (key.cache_idx in g.status.get().statuses ==>
      && g.status.get() == CacheResources.CacheStatus(
          key.cache_idx, 
          g.status.get().statuses[key.cache_idx])
      && status_inv(v, g.status.get().statuses[key.cache_idx], key)
    )
    //&& (flag == RWLock.ExcLock_Clean ==> g.status.lNone?)
    //&& (flag == RWLock.ExcLock_Dirty ==> g.status.lNone?)
    && (flag == RWLock.PendingExcLock ==>
        key.cache_idx in g.status.get().statuses)
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

  predicate atomic_status_inv(a: AtomicStatus, key: Key)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, key)
  }

  method try_acquire_writeback(a: AtomicStatus, ghost key: Key, with_access: bool)
  returns (success: bool,
      glinear m: lOption<RW.WritebackObtainedHandle>,
      glinear disk_write_ticket: lOption<CacheResources.DiskWriteTicket>)
  requires atomic_status_inv(a, key)
  ensures !success ==> m.lNone?
  ensures !success ==> disk_write_ticket.lNone?
  ensures success ==>
      && m.lSome?
      && m.value.is_handle(key)
      && disk_write_ticket.lSome?
      && disk_write_ticket.value.writes(
          m.value.b.idx.v as uint64,
          m.value.b.data.s)
  {
    atomic_block var cur_flag := execute_atomic_load(a) { }

    if !(cur_flag == flag_zero
        || (with_access && cur_flag == flag_accessed)) {
      m := lNone;
      disk_write_ticket := lNone;
      success := false;
    } else {
      atomic_block var did_set :=
          execute_atomic_compare_and_set_strong(a, flag_zero, flag_writeback)
      {
        ghost_acquire old_g;

        ghost var ghosty := true;
        if did_set && ghosty {
          linear var res, handle, ticket, stat;
          linear var G(rwlock, status) := old_g;

          rwlock, res, handle := RW.do_internal_step
              key, rwlock);

          stat, ticket := CacheResources.initiate_writeback(
              handle.cache_entry, unwrap_value(status));

          new_g := G(rwlock, lSome(stat));
          handle_out := lSome(handle);
          m := lSome(res);
          disk_write_ticket := lSome(ticket);
          assert state_inv(new_v, new_g, key);
        } else {
          m := lNone;
          new_g := old_g;
          handle_out := lNone;
          disk_write_ticket := lNone;
          assert state_inv(new_v, new_g, key);
        }
        assert state_inv(new_v, new_g, key);

        ghost_release new_g;
      }

      if did_set {
        success := true;
      } else if !with_access {
        success := false;
      } else {
        atomic_block var did_set :=
            execute_atomic_compare_and_set_strong(a, flag_accessed, flag_writeback_accessed)
        {
          dispose_lnone(handle_out);
          dispose_lnone(m);
          dispose_lnone(disk_write_ticket);

          if did_set {
            linear var res, handle, stat, ticket;
            linear var G(rwlock, status) := old_g;
            rwlock, res, handle := RWLockMethods.transform_TakeWriteback(
                key, rwlock);
            stat, ticket := CacheResources.initiate_writeback(
                handle.cache_entry, unwrap_value(status));
            new_g := G(rwlock, lSome(stat));
            handle_out := lSome(handle);
            m := lSome(res);
            disk_write_ticket := lSome(ticket);
          } else {
            m := lNone;
            new_g := old_g;
            handle_out := lNone;
            disk_write_ticket := lNone;
          }
          assert state_inv(new_v, new_g, key);
        }

        success := did_set;
      }
    }
  }

  /*

  method release_writeback(a: AtomicStatus, key: Key,
      linear r: RW.Token,
      /* readonly */ linear handle: RWLock.Handle,
      linear stub: DiskWriteStub)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.WritebackObtained(key))
  requires handle.is_handle(key)
  requires 0 <= handle.cache_entry.disk_idx
             < 0x1_0000_0000_0000_0000
  requires stub == DiskWriteStub(
      handle.cache_entry.disk_idx as uint64)
  {
    // Unset Writeback; set Clean
    var orig_value := fetch_xor(a, flag_writeback_clean);

    ///// Begin jank
    ///// Setup:
    var v := flag_writeback_clean;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_xor(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    linear var G(rwlock, status) := old_g;

    RWLockMethods.pre_ReleaseWriteback(key, fl, rwlock, r);

    linear var stat := CacheResources.finish_writeback(
        handle.cache_entry, unwrap_value(status), stub);

    rwlock := RWLockMethods.transform_ReleaseWriteback(key, fl, rwlock, r, handle);
    new_g := G(rwlock, lSome(stat));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  /*method try_set_write_lock(a: AtomicStatus, key: Key)
  returns (success: bool, linear m: lOption<RW.Token>)
  requires atomic_status_inv(a, key)
  ensures !success ==> m.lNone?
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.ExcLockPendingAwaitWriteback(key))
  {
    var orig_value := fetch_or(a, flag_exc);

    ///// Begin jank
    ///// Setup:
    var v := flag_exc;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_or(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    if fl == RWLock.Available {
      linear var r;
      new_g, r := RWLockMethods.transform_TakeExcLock(key, old_g);
      m := lSome(r);
    } else if fl == RWLock.Writeback {
      linear var r;
      new_g, r := RWLockMethods.transform_TakeExcLockAwaitWriteback(key, old_g);
      m := lSome(r);
    } else {
      new_g := old_g;
      m := lNone;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(orig_value, flag_exc) == 0;
  }*/

  method try_check_writeback_isnt_set(a: AtomicStatus, key: Key,
      t: int, linear m: RW.Token)
  returns (success: bool, clean: bool, linear m': RW.Token,
      linear status: lOption<CacheResources.R>)
  requires atomic_status_inv(a, key)
  requires m == RWLock.Internal(
      RWLock.ExcLockPendingAwaitWriteback(key, t))
  ensures !success ==> m' == m
  ensures !success ==> status.lNone?
  ensures success ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, t, 0, clean))
  ensures success ==>
    && status == lSome(CacheResources.CacheStatus(key.cache_idx,
        (if clean then CacheResources.Clean else CacheResources.Dirty)))
  {
    var f := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == old_v;
    assume f == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    if fl == RWLock.Writeback || fl == RWLock.Writeback_PendingExcLock
    {
      new_g := old_g;
      m' := m;
      status := lNone;
      assert state_inv(new_v, new_g, key);
    } else {
      linear var G(rwlock, status0) := old_g;
      rwlock, m' := RWLockMethods.transform_TakeExcLockFinishWriteback(
        key, t,fl, bit_and(f, flag_clean) != 0,
        rwlock, m);
      status := status0;
      new_g := G(rwlock, lNone);
      assert state_inv(new_v, new_g, key);
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(f, flag_writeback) == 0;
    clean := bit_and(f, flag_clean) != 0;
  }

  method try_alloc(a: AtomicStatus, key: Key)
  returns (success: bool,
      linear m: lOption<RW.Token>,
      linear handle_opt: lOption<RWLock.Handle>,
      linear status: lOption<CacheResources.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> m.lNone?
  ensures !success ==> handle_opt.lNone?
  ensures !success ==> status.lNone?
  ensures success ==>
      && m == lSome(RWLock.Internal(RWLock.ReadingPending(key)))
  ensures success ==> handle_opt.lSome?
      && handle_opt.value.is_handle(key)
  ensures success ==>
    && status == lSome(CacheResources.CacheStatus(
        key.cache_idx, CacheResources.Empty))
  {
    // check first to reduce contention
    var f := atomic_read(a);
    if f != flag_unmapped {
      success := false;
      m := lNone;
      handle_opt := lNone;
      status := lNone;
    } else {
      var did_set := compare_and_set(a, flag_unmapped, flag_exc_reading);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_unmapped;
      var v2 := flag_exc_reading;
      var old_v: uint8;
      var new_v: uint8;
      linear var old_g: G := unsafe_obtain();
      assume old_v == v1 ==> new_v == v2 && did_set;
      assume old_v != v1 ==> new_v == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      linear var new_g;
      ///// Transfer:
      if did_set {
        linear var res, handle;
        linear var G(rwlock, status0) := old_g;
        rwlock, res, handle := RWLockMethods.transform_Alloc(key, rwlock);
        status := status0;
        new_g := G(rwlock, lNone);
        m := lSome(res);
        handle_opt := lSome(handle);
        assert status.lSome?;
        assert status.value.status == CacheResources.Empty;
      } else {
        m := lNone;
        handle_opt := lNone;
        status := lNone;
        new_g := old_g;
      }
      assert state_inv(new_v, new_g, key);
      ///// Teardown:
      assert atomic_inv(a, new_v, new_g);
      unsafe_dispose(new_g);
      ///// End jank

      success := did_set;
    }
  }

  method clear_exc_bit_during_load_phase(a: AtomicStatus, key: Key, t:int,
      linear r: RW.Token)
  returns (linear q: RW.Token)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.ReadingPendingCounted(key, t))
  ensures q == RWLock.Internal(RWLock.ReadingObtained(key, t))
  {
    atomic_write(a, flag_accessed_reading_clean);

    ///// Begin jank
    ///// Setup:
    var v := flag_accessed_reading_clean;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    linear var G(rwlock, status) := old_g;
    rwlock, q := RWLockMethods.transform_ObtainReading(key, t, fl, rwlock, r);
    new_g := G(rwlock, status);
    assert status.lNone?;
    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method load_phase_finish(a: AtomicStatus, key: Key, t: int,
      linear r: RW.Token, linear handle: RWLock.Handle,
      linear status: CacheResources.R)
  returns (linear q: RW.Token, /*readonly*/ linear handle_out: RWLock.Handle)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.ReadingObtained(key, t))
  requires handle.is_handle(key)
  requires status == CacheResources.CacheStatus(key.cache_idx,
      CacheResources.Clean)
  ensures q == RWLock.Internal(RWLock.SharedLockObtained(key, t))
  ensures handle_out == handle
  {
    var orig_value := fetch_and(a, 0xff - flag_reading);

    ///// Begin jank
    ///// Setup:
    var v := 0xff - flag_reading;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_and(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    linear var G(rwlock, status_empty) := old_g;
    RWLockMethods.pre_ReadingToShared(key, t, fl, rwlock, r);
    dispose_lnone(status_empty);
    rwlock, q, handle_out :=
        RWLockMethods.transform_ReadingToShared(key, t, fl, rwlock, r, handle);
    new_g := G(rwlock, lSome(status));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method quicktest_is_exc_locked(a: AtomicStatus)
  returns (is_exc_locked: bool)
  {
    var v := atomic_read(a);
    return ((v as bv8) & (flag_exc as bv8)) as uint8 != 0;
  }

  method is_exc_locked_or_free(a: AtomicStatus,
      key: Key, t: int,
      linear r: RW.Token)
  returns (success: bool, is_accessed: bool, linear r': RW.Token)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.SharedLockPending(key, t))
  ensures !success ==> r == r'
  ensures success ==> r' == 
      RWLock.Internal(RWLock.SharedLockPending2(key, t))
  {
    var f := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == old_v;
    assume f == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    if fl == RWLock.Available || fl == RWLock.Writeback
        || fl == RWLock.Reading {
      r' := RWLockMethods.transform_SharedCheckExcFree(
          key, t, old_g.rwlock.q.flags,
          r, old_g.rwlock);
      new_g := old_g;
    } else {
      r' := r;
      new_g := old_g;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(f, bit_or(flag_exc, flag_unmapped)) == 0;
    is_accessed := bit_and(f, flag_accessed) != 0;
  }

  method mark_accessed(a: AtomicStatus,
      key: Key, t: int,
      shared r: RW.Token)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.SharedLockPending2(key, t))
  {
    var orig_value := fetch_or(a, flag_accessed);

    ///// Begin jank
    ///// Setup:
    var v := flag_accessed;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_or(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    RWLockMethods.possible_flags_SharedLockPending2(key, t, old_g.rwlock.q.flags,
        r, old_g.rwlock);
    new_g := old_g;
    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method clear_accessed(a: AtomicStatus, key: Key)
  requires atomic_status_inv(a, key)
  {
    var orig_value := fetch_and(a, 0xff - flag_accessed);

    ///// Begin jank
    ///// Setup:
    var v := 0xff - flag_accessed;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_and(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    new_g := old_g;
    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method is_reading(a: AtomicStatus,
      key: Key, t: int,
      linear r: RW.Token)
  returns (
    success: bool,
    linear r': RW.Token,
    /*readonly*/ linear handle: lOption<RWLock.Handle>
  )
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.SharedLockPending2(key, t))
  ensures !success ==> r == r'
  ensures !success ==> handle == lNone
  ensures success ==>
      && r' == RWLock.Internal(RWLock.SharedLockObtained(key, t))
      && handle.lSome?
      && handle.value.is_handle(key)
  {
    var f := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == old_v;
    assume f == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.rwlock.q.flags;
    if fl != RWLock.Reading && fl != RWLock.Reading_ExcLock {
      linear var hand;
      r', hand := RWLockMethods.transform_SharedCheckReading(
          key, t, old_g.rwlock.q.flags,
          r, old_g.rwlock);
      new_g := old_g;
      handle := lSome(hand);
    } else {
      r' := r;
      new_g := old_g;
      handle := lNone;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(f, flag_reading) == 0;
  }

  method take_exc_if_eq_clean(a: AtomicStatus,
      key: Key)
  returns (
    success: bool,
    linear m': lOption<RW.Token>,
    linear status: lOption<CacheResources.R>,
    /*readonly*/ linear handle: lOption<RWLock.Handle>
  )
  requires atomic_status_inv(a, key)
  //requires m == RWLock.Internal(RWLock.SharedLockPending(key, t))
  ensures !success ==> m'.lNone? && status.lNone? && handle.lNone?
  ensures success ==>
      && m' == lSome(RWLock.Internal(RWLock.ExcLockPending(key, -1, 0, true)))
      && status == lSome(CacheResources.CacheStatus(
          key.cache_idx, CacheResources.Clean))
      && handle.lSome?
      && handle.value.is_handle(key)
  {
    var did_set := compare_and_set(a, flag_clean, flag_exc_clean);

    ///// Begin jank
    ///// Setup:
    var v1 := flag_clean;
    var v2 := flag_exc_clean;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume old_v == v1 ==> new_v == v2 && did_set;
    assume old_v != v1 ==> new_v == old_v && !did_set;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    if did_set {
      //m' := transform_SharedCheckExcFree(
      //    key, t, RWLock.Available, m, old_g.rwlock);
      //m' := transform_SharedCheckReading(
      //    key, t, RWLock.Available, m', old_g.rwlock);
      
      linear var G(rwlock, status0) := old_g;
      linear var m0, handle';

      var fl := rwlock.q.flags;
      rwlock, m0, handle' := RWLockMethods.transform_ThreadlessExc(key, rwlock, fl);

      //m', rwlock := transform_SharedToExc(
      //    key, t, RWLock.Available, m', rwlock);

      rwlock, m0 := RWLockMethods.transform_TakeExcLockFinishWriteback(
          key, -1, RWLock.PendingExcLock, true, rwlock, m0);

      new_g := G(rwlock, lNone);
      status := status0;
      m' := lSome(m0);
      handle := lSome(handle');
      assert state_inv(new_v, new_g, key);
    } else {
      new_g := old_g;
      m' := lNone;
      status := lNone;
      handle := lNone;
      assert state_inv(new_v, new_g, key);
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := did_set;
  }

  method set_to_free(a: AtomicStatus, key: Key,
      linear handle: RWLock.Handle,
      linear status: CacheResources.R,
      linear r: RW.Token)
  requires atomic_status_inv(a, key)
  requires handle.is_handle(key)
  requires status == CacheResources.CacheStatus(
      key.cache_idx,
      CacheResources.Empty)
  requires r == RWLock.Internal(RWLock.ExcLockObtained(key, -1, true))
  {
    atomic_write(a, flag_unmapped);

    ///// Begin jank
    ///// Setup:
    var v := flag_unmapped;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:

    linear var G(rwlock, empty_status) := old_g;

    var fl := rwlock.q.flags;
    rwlock := RWLockMethods.transform_unmap(key, fl, true, rwlock, handle, r);

    dispose_lnone(empty_status);
    new_g := G(rwlock, lSome(status));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method abandon_exc(
      a: AtomicStatus,
      key: Key,
      linear status: CacheResources.R,
      linear r: RW.Token,
      /*readonly*/ linear handle: RWLock.Handle)
  requires atomic_status_inv(a, key)
  requires status == CacheResources.CacheStatus(
      key.cache_idx,
      CacheResources.Clean)
  requires r.Internal? && r.q.ExcLockPending?
  requires r == RWLock.Internal(RWLock.ExcLockPending(key, -1,
      r.q.visited, true))
  requires handle.is_handle(key)
  {
    var orig_value := fetch_and(a, 0xff - flag_exc);

    ///// Begin jank
    ///// Setup:
    var v := 0xff - flag_exc;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_and(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:

    linear var G(rwlock, empty_status) := old_g;

    var fl := rwlock.q.flags;
    var visited := r.q.visited;
    rwlock := RWLockMethods.abandon_ExcLockPending(key, fl, visited, true, r, rwlock, handle);

    dispose_lnone(empty_status);
    new_g := G(rwlock, lSome(status));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method abandon_reading_pending(
      a: AtomicStatus,
      key: Key,
      linear status: CacheResources.R,
      linear r: RW.Token,
      /*readonly*/ linear handle: RWLock.Handle)
  requires atomic_status_inv(a, key)
  requires status == CacheResources.CacheStatus(
      key.cache_idx,
      CacheResources.Empty)
  requires r == RWLock.Internal(RWLock.ReadingPending(key))
  requires handle.is_handle(key)
  {
    atomic_write(a, flag_unmapped);

    ///// Begin jank
    ///// Setup:
    var v := flag_unmapped;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: G := unsafe_obtain();
    assume new_v == v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;

    ///// Transfer:

    linear var G(rwlock, empty_status) := old_g;

    var fl := rwlock.q.flags;
    rwlock := RWLockMethods.abandon_ReadingPending(key, fl, r, rwlock, handle);

    dispose_lnone(empty_status);
    new_g := G(rwlock, lSome(status));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }
  */
}
