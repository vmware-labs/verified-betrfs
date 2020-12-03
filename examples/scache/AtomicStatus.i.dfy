include "Atomic.s.dfy"
include "RWLock.i.dfy"
include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"

module AtomicStatusImpl {
  import opened NativeTypes
  import opened Ptrs
  import opened AtomicSpec
  import opened LinearMaybe
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
  const flag_write_accessed : uint8 := 6;
  const flag_writeback_exc_accessed : uint8 := 7;
  const flag_accessed_reading : uint8 := 20;
  const flag_exc_reading : uint8 := 18;
  const flag_exc_accessed_reading : uint8 := 22;
  const flag_writeback_exc_clean : uint8 := 35;
  const flag_writeback_accessed_clean : uint8 := 37;
  const flag_write_accessed_clean : uint8 := 38;
  const flag_writeback_exc_accessed_clean : uint8 := 39;
  const flag_accessed_reading_clean : uint8 := 52;
  const flag_exc_reading_clean : uint8 := 50;
  const flag_exc_accessed_reading_clean : uint8 := 54;
  const flag_exc_accessed_clean : uint8 := 38;

  linear datatype G = G(
    linear rwlock: RWLock.R,
    linear status: maybe<CacheResources.R>
  )

  type AtomicStatus = Atomic<uint8, G>

  predicate state_inv(v: uint8, g: G, key: RWLock.Key)
  {
    && g.rwlock.Internal?
    && flags_field_inv(v, g.rwlock.q, key)
    /*&& (g.rwlock.q.flags == RWLock.Reading_ExcLock ==>
      !has(g.status)
    )*/
    && (!has(g.status) ==> (
        || v == flag_exc
        || v == flag_exc_reading
        || v == flag_accessed_reading_clean
    ))
    && (has(g.status) ==> (
      && status_inv(v, read(g.status), key)
    ))
  }

  predicate flags_field_inv(v: uint8, f: RWLock.Q, key: RWLock.Key)
  {
    && f.FlagsField?
    && f.key == key
    && (f.flags == RWLock.Available ==> (
      || v == flag_zero
      || v == flag_accessed
      || v == flag_clean
      || v == flag_accessed_clean
    ))
    && (f.flags == RWLock.WriteBack ==> (
      || v == flag_writeback
      || v == flag_writeback_accessed
    ))
    && (f.flags == RWLock.ExcLock ==> (
      || v == flag_exc
      || v == flag_write_accessed
      || v == flag_exc_clean
      || v == flag_write_accessed_clean
    ))
    && (f.flags == RWLock.WriteBack_PendingExcLock ==> (
      || v == flag_writeback_exc
      || v == flag_writeback_exc_accessed
      || v == flag_writeback_exc_clean
      || v == flag_writeback_exc_accessed_clean
    ))
    && (f.flags == RWLock.Unmapped ==> v == flag_unmapped)
    && (f.flags == RWLock.Reading ==>
      || v == flag_reading
      || v == flag_accessed_reading_clean
    )
    && (f.flags == RWLock.Reading_ExcLock ==> v == flag_exc_reading || v == flag_exc_accessed_reading)
  }
  
  predicate status_inv(v: uint8, f: CacheResources.R,
      key: RWLock.Key)
  {
    && f.CacheStatus?
    && f.cache_idx == key.cache_idx
    && (f.status == CacheResources.Empty ==> (
      v == flag_unmapped
    ))
    && (f.status == CacheResources.Reading ==> (
      false
    ))
    && (f.status == CacheResources.Clean ==> (
      || v == flag_clean
      || v == flag_exc_clean
      || v == flag_accessed_clean
      || v == flag_exc_accessed_clean
    ))
    && (f.status == CacheResources.Dirty ==> (
      || v == flag_zero
      || v == flag_accessed
    ))
    && (f.status == CacheResources.WriteBack ==> (
      || v == flag_writeback
      || v == flag_writeback_exc
      || v == flag_writeback_accessed
      || v == flag_writeback_exc_accessed
    ))
  }

  predicate atomic_status_inv(a: AtomicStatus, key: RWLock.Key)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, key)
  }

  method unsafe_obtain<Q>() returns (linear r: Q)
  method unsafe_dispose<Q>(linear r: Q)

  method try_acquire_writeback(a: AtomicStatus, key: RWLock.Key, with_access: bool)
  returns (success: bool,
      linear m: maybe<RWLock.R>,
      /* readonly */ linear handle_out: maybe<RWLock.Handle>,
      linear disk_write_ticket: maybe<CacheResources.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures !success ==> !has(handle_out)
  ensures !success ==> !has(disk_write_ticket)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.WriteBackObtained(key))
  ensures success ==>
      && has(handle_out)
      && has(disk_write_ticket)
      && read(handle_out).is_handle(key)
      && read(disk_write_ticket)
        == CacheResources.DiskWriteTicket(
            read(handle_out).cache_entry.disk_idx as uint64,
            read(handle_out).cache_entry.data)
  {
    var cur_flag := atomic_read(a);
    if !(cur_flag == flag_zero
        || (with_access && cur_flag == flag_accessed)) {
      m := empty();
      handle_out := empty();
      disk_write_ticket := empty();
      success := false;
    } else {
      var did_set := compare_and_set(a, flag_zero, flag_writeback);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_zero;
      var v2 := flag_writeback;
      var old_v: uint8;
      var new_v: uint8;
      linear var old_g: G := unsafe_obtain();
      assume old_v == v1 ==> new_v == v2 && did_set;
      assume old_v != v1 ==> new_v == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      linear var new_g;
      ///// Transfer:
      if did_set {
        linear var res, handle, ticket, stat;
        linear var G(rwlock, status) := old_g;

        rwlock, res, handle := RWLock.transform_TakeWriteBack(
            key, rwlock);

        stat, ticket := CacheResources.initiate_writeback(
            handle.cache_entry, unwrap(status));

        new_g := G(rwlock, give(stat));
        handle_out := give(handle);
        m := give(res);
        disk_write_ticket := give(ticket);
        assert state_inv(new_v, new_g, key);
      } else {
        m := empty();
        new_g := old_g;
        handle_out := empty();
        disk_write_ticket := empty();
        assert state_inv(new_v, new_g, key);
      }
      assert state_inv(new_v, new_g, key);
      ///// Teardown:
      assert atomic_inv(a, new_v, new_g);
      unsafe_dispose(new_g);
      ///// End jank

      if did_set {
        success := true;
      } else if !with_access {
        success := false;
      } else {
        var did_set := compare_and_set(a, flag_accessed, flag_writeback_accessed);

        ///// Begin jank
        ///// Setup:
        var v1 := flag_accessed;
        var v2 := flag_writeback_accessed;
        var old_v: uint8;
        var new_v: uint8;
        linear var old_g: G := unsafe_obtain();
        assume old_v == v1 ==> new_v == v2 && did_set;
        assume old_v != v1 ==> new_v == old_v && !did_set;
        assume atomic_inv(a, old_v, old_g);
        linear var new_g;
        ///// Transfer:
        var _ := discard(m);
        var _ := discard(handle_out);
        var _ := discard(disk_write_ticket);

        if did_set {
          linear var res, handle, stat, ticket;
          linear var G(rwlock, status) := old_g;
          rwlock, res, handle := RWLock.transform_TakeWriteBack(
              key, rwlock);
          stat, ticket := CacheResources.initiate_writeback(
              handle.cache_entry, unwrap(status));
          new_g := G(rwlock, give(stat));
          handle_out := give(handle);
          m := give(res);
          disk_write_ticket := give(ticket);
        } else {
          m := empty();
          new_g := old_g;
          handle_out := empty();
          disk_write_ticket := empty();
        }
        assert state_inv(new_v, new_g, key);
        ///// Teardown:
        assert atomic_inv(a, new_v, new_g);
        unsafe_dispose(new_g);
        ///// End jank

        success := did_set;
      }
    }
  }

  method release_writeback(a: AtomicStatus, key: RWLock.Key,
      linear r: RWLock.R,
      /* readonly */ linear handle: RWLock.Handle,
      linear stub: CacheResources.R)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.WriteBackObtained(key))
  requires handle.is_handle(key)
  requires 0 <= handle.cache_entry.disk_idx
             < 0x1_0000_0000_0000_0000
  requires stub == CacheResources.DiskWriteStub(
      handle.cache_entry.disk_idx as uint64)
  {
    // Unset WriteBack; set Clean
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

    RWLock.pre_ReleaseWriteBack(key, fl, rwlock, r);

    linear var stat := CacheResources.finish_writeback(
        handle.cache_entry, unwrap(status), stub);

    rwlock := RWLock.transform_ReleaseWriteBack(key, fl, rwlock, r, handle);
    new_g := G(rwlock, give(stat));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  /*method try_set_write_lock(a: AtomicStatus, key: RWLock.Key)
  returns (success: bool, linear m: maybe<RWLock.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(key))
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
      new_g, r := RWLock.transform_TakeExcLock(key, old_g);
      m := give(r);
    } else if fl == RWLock.WriteBack {
      linear var r;
      new_g, r := RWLock.transform_TakeExcLockAwaitWriteBack(key, old_g);
      m := give(r);
    } else {
      new_g := old_g;
      m := empty();
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(orig_value, flag_exc) == 0;
  }*/

  method try_check_writeback_isnt_set(a: AtomicStatus, key: RWLock.Key,
      linear m: RWLock.R)
  returns (success: bool, linear m': RWLock.R)
  requires atomic_status_inv(a, key)
  requires m == RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(key))
  ensures !success ==> m' == m
  ensures success ==> m' == RWLock.Internal(RWLock.ExcLockPending(key, 0))
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
    if fl == RWLock.Available
        || fl == RWLock.ExcLock
        || fl == RWLock.Reading
        || fl == RWLock.Reading_ExcLock
        || fl == RWLock.Unmapped
    {
      linear var G(rwlock, status) := old_g;
      rwlock, m' := RWLock.transform_TakeExcLockFinishWriteBack(key, fl, rwlock, m);
      new_g := G(rwlock, status);
    } else {
      new_g := old_g;
      m' := m;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(f, flag_writeback) == 0;
  }

  method try_alloc(a: AtomicStatus, key: RWLock.Key)
  returns (success: bool,
      linear m: maybe<RWLock.R>,
      linear handle_maybe: maybe<RWLock.Handle>,
      linear status: maybe<CacheResources.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures !success ==> !has(handle_maybe)
  ensures !success ==> !has(status)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.ReadingPending(key))
  ensures success ==> has(handle_maybe)
      && read(handle_maybe).is_handle(key)
      && read(handle_maybe).idx.v == -1
  ensures success ==> has(status)
    && read(status) == CacheResources.CacheStatus(
        key.cache_idx, CacheResources.Empty)
  {
    // check first to reduce contention
    var f := atomic_read(a);
    if f != flag_unmapped {
      success := false;
      m := empty();
      handle_maybe := empty();
      status := empty();
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
        rwlock, res, handle := RWLock.transform_Alloc(key, rwlock);
        status := status0;
        new_g := G(rwlock, empty());
        m := give(res);
        handle_maybe := give(handle);
        assume has(status);
        assume read(status).status == CacheResources.Empty; // TODO
      } else {
        m := empty();
        handle_maybe := empty();
        status := empty();
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

  method clear_exc_bit_during_load_phase(a: AtomicStatus, key: RWLock.Key, t:int,
      linear r: RWLock.R)
  returns (linear q: RWLock.R)
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
    rwlock, q := RWLock.transform_ObtainReading(key, t, fl, rwlock, r);
    new_g := G(rwlock, status);
    assert !has(status);
    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method load_phase_finish(a: AtomicStatus, key: RWLock.Key, t: int,
      linear r: RWLock.R, linear handle: RWLock.Handle,
      linear status: CacheResources.R)
  returns (linear q: RWLock.R, /*readonly*/ linear handle_out: RWLock.Handle)
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
    RWLock.pre_ReadingToShared(key, t, fl, rwlock, r);
    var _ := discard(status_empty);
    rwlock, q, handle_out :=
        RWLock.transform_ReadingToShared(key, t, fl, rwlock, r, handle);
    new_g := G(rwlock, give(status));

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }
}
