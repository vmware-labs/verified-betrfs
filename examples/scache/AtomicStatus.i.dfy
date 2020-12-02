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

  const flag_zero : uint8 := 0;

  const flag_writeback : uint8 := 1;
  const flag_exc : uint8 := 2;
  const flag_accessed : uint8 := 4;
  const flag_unmapped : uint8 := 8;
  const flag_reading : uint8 := 16;

  const flag_writeback_exc : uint8 := 3;
  const flag_writeback_accessed : uint8 := 5;
  const flag_write_accessed : uint8 := 6;
  const flag_writeback_exc_accessed : uint8 := 7;
  const flag_accessed_reading : uint8 := 20;
  const flag_exc_reading : uint8 := 18;
  const flag_exc_accessed_reading : uint8 := 22;

  type AtomicStatus = Atomic<uint8, RWLock.R>

  predicate state_inv(v: uint8, g: RWLock.R, key: RWLock.Key)
  {
    && g.Internal?
    && g.q.FlagsField?
    && g.q.key == key
    && (g.q.flags == RWLock.Available ==> v == flag_zero || v == flag_accessed)
    && (g.q.flags == RWLock.WriteBack ==> v == flag_writeback || v == flag_writeback_accessed)
    && (g.q.flags == RWLock.ExcLock ==> v == flag_exc || v == flag_write_accessed)
    && (g.q.flags == RWLock.WriteBack_PendingExcLock ==>
        v == flag_writeback_exc || v == flag_writeback_exc_accessed)
    && (g.q.flags == RWLock.Unmapped ==> v == flag_unmapped)
    && (g.q.flags == RWLock.Reading ==> v == flag_reading || v == flag_accessed_reading)
    && (g.q.flags == RWLock.Reading_ExcLock ==> v == flag_exc_reading || v == flag_exc_accessed_reading)
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
      /* readonly */ linear handle_out: maybe<RWLock.Handle>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.WriteBackObtained(key))
  ensures !success ==> !has(handle_out)
  ensures success ==> has(handle_out)
      && read(handle_out).is_handle(key)
  {
    var cur_flag := atomic_read(a);
    if !(cur_flag == flag_zero || (with_access && cur_flag == flag_accessed)) {
      m := empty();
      handle_out := empty();
      success := false;
    } else {
      var did_set := compare_and_set(a, flag_zero, flag_writeback);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_zero;
      var v2 := flag_writeback;
      var old_v: uint8;
      var new_v: uint8;
      linear var old_g: RWLock.R := unsafe_obtain();
      assume old_v == v1 ==> new_v == v2 && did_set;
      assume old_v != v1 ==> new_v == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      linear var new_g;
      ///// Transfer:
      if did_set {
        linear var res, handle;
        new_g, res, handle := RWLock.transform_TakeWriteBack(key, old_g);
        handle_out := give(handle);
        m := give(res);
      } else {
        m := empty();
        new_g := old_g;
        handle_out := empty();
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
        linear var old_g: RWLock.R := unsafe_obtain();
        assume old_v == v1 ==> new_v == v2 && did_set;
        assume old_v != v1 ==> new_v == old_v && !did_set;
        assume atomic_inv(a, old_v, old_g);
        linear var new_g;
        ///// Transfer:
        var _ := discard(m);
        var _ := discard(handle_out);

        if did_set {
          linear var res, handle;
          new_g, res, handle := RWLock.transform_TakeWriteBack(key, old_g);
          handle_out := give(handle);
          m := give(res);
        } else {
          m := empty();
          new_g := old_g;
          handle_out := empty();
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
      /* readonly */ linear handle: RWLock.Handle)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.WriteBackObtained(key))
  requires handle.is_handle(key)
  {
    var orig_value := fetch_and(a, 0xff - flag_writeback);

    ///// Begin jank
    ///// Setup:
    var v := 0xff - flag_writeback;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_and(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    new_g := RWLock.transform_ReleaseWriteBack(key, fl, old_g, r, handle);

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
    linear var old_g: RWLock.R := unsafe_obtain();
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
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == old_v;
    assume f == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    if fl == RWLock.Available
        || fl == RWLock.ExcLock
        || fl == RWLock.Reading
        || fl == RWLock.Reading_ExcLock
        || fl == RWLock.Unmapped
    {
      new_g, m' := RWLock.transform_TakeExcLockFinishWriteBack(key, fl, old_g, m);
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
      linear handle_maybe: maybe<RWLock.Handle>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.ReadingPending(key))
  ensures !success ==> !has(handle_maybe)
  ensures success ==> has(handle_maybe)
      && read(handle_maybe).is_handle(key)
  {
    // check first to reduce contention
    var f := atomic_read(a);
    if f != flag_unmapped {
      success := false;
      m := empty();
      handle_maybe := empty();
    } else {
      var did_set := compare_and_set(a, flag_unmapped, flag_exc_reading);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_unmapped;
      var v2 := flag_exc_reading;
      var old_v: uint8;
      var new_v: uint8;
      linear var old_g: RWLock.R := unsafe_obtain();
      assume old_v == v1 ==> new_v == v2 && did_set;
      assume old_v != v1 ==> new_v == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      linear var new_g;
      ///// Transfer:
      if did_set {
        linear var res, handle;
        new_g, res, handle := RWLock.transform_Alloc(key, old_g);
        m := give(res);
        handle_maybe := give(handle);
      } else {
        m := empty();
        handle_maybe := empty();
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
    atomic_write(a, flag_accessed_reading); // TODO 'clean' bit

    ///// Begin jank
    ///// Setup:
    var v := flag_accessed_reading;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume new_v == v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    new_g, q := RWLock.transform_ObtainReading(key, t, fl, old_g, r);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }

  method load_phase_finish(a: AtomicStatus, key: RWLock.Key, t: int,
      linear r: RWLock.R, linear handle: RWLock.Handle)
  returns (linear q: RWLock.R, /*readonly*/ linear handle_out: RWLock.Handle)
  requires atomic_status_inv(a, key)
  requires r == RWLock.Internal(RWLock.ReadingObtained(key, t))
  requires handle.is_handle(key)
  ensures q == RWLock.Internal(RWLock.SharedLockObtained(key, t))
  ensures handle_out == handle
  {
    var orig_value := fetch_and(a, 0xff - flag_reading);

    ///// Begin jank
    ///// Setup:
    var v := 0xff - flag_reading;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_and(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    new_g, q, handle_out :=
        RWLock.transform_ReadingToShared(key, t, fl, old_g, r, handle);

    assert state_inv(new_v, new_g, key);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank
  }
}
