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
  import ReadWriteLockResources

  const flag_free : uint8 := 0;
  const flag_back : uint8 := 1;
  const flag_write : uint8 := 2;
  const flag_back_write : uint8 := 3;

  type AtomicStatus = Atomic<uint8, ReadWriteLockResources.Q>

  predicate state_inv(v: uint8, g: ReadWriteLockResources.Q, ptr: Ptr)
  {
    && g.FlagsField?
    && g.ptr == ptr
    && (g.flags == ReadWriteLockResources.Free ==> v == flag_free)
    && (g.flags == ReadWriteLockResources.Back ==> v == flag_back)
    && (g.flags == ReadWriteLockResources.Write ==> v == flag_write)
    && (g.flags == ReadWriteLockResources.Back_PendingWrite ==>
        v == flag_back_write)
  }

  predicate atomic_status_inv(a: AtomicStatus, ptr: Ptr)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, ptr)
  }

  method unsafe_obtain<Q>() returns (linear r: Q)
  method unsafe_dispose<Q>(linear r: Q)

  method try_acquire_writeback(a: AtomicStatus, ptr: Ptr)
  returns (success: bool, linear m: maybe<ReadWriteLockResources.Q>)
  requires atomic_status_inv(a, ptr)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == ReadWriteLockResources.BackObtained(ptr)
  {
    var did_set := compare_and_set(a, flag_free, flag_back);

    ///// Begin jank
    ///// Setup:
    var v1 := flag_free;
    var v2 := flag_back;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: ReadWriteLockResources.Q := unsafe_obtain();
    assume old_v == v1 ==> new_v == v2 && did_set;
    assume old_v != v1 ==> new_v == old_v && !did_set;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    if did_set {
      linear var res;
      new_g, res := ReadWriteLockResources.transform_TakeBack(ptr, old_g);
      m := give(res);
    } else {
      m := empty();
      new_g := old_g;
    }
    assert state_inv(new_v, new_g, ptr);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := did_set;
  }

  method try_set_write_lock(a: AtomicStatus, ptr: Ptr)
  returns (success: bool, linear m: maybe<ReadWriteLockResources.Q>)
  requires atomic_status_inv(a, ptr)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == ReadWriteLockResources.WritePendingAwaitBack(ptr)
  {
    var orig_value := fetch_or(a, flag_write);

    ///// Begin jank
    ///// Setup:
    var v := flag_write;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: ReadWriteLockResources.Q := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_or(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.flags;
    if fl == ReadWriteLockResources.Free {
      linear var r;
      new_g, r := ReadWriteLockResources.transform_TakeWrite(ptr, old_g);
      m := give(r);
    } else if fl == ReadWriteLockResources.Back {
      linear var r;
      new_g, r := ReadWriteLockResources.transform_TakeWriteAwaitBack(ptr, old_g);
      m := give(r);
    } else {
      new_g := old_g;
      m := empty();
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(orig_value, flag_write) == 0;
  }

  method try_check_writeback_isnt_set(a: AtomicStatus, ptr: Ptr,
      linear m: ReadWriteLockResources.Q)
  returns (success: bool, linear m': ReadWriteLockResources.Q)
  requires atomic_status_inv(a, ptr)
  requires m == ReadWriteLockResources.WritePendingAwaitBack(ptr)
  ensures !success ==> m' == m
  ensures success ==> m' == ReadWriteLockResources.WritePending(ptr, 0)
  {
    var f := atomic_read(a);

    ///// Begin jank
    ///// Setup:
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: ReadWriteLockResources.Q := unsafe_obtain();
    assume new_v == old_v;
    assume f == old_v;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.flags;
    if fl == ReadWriteLockResources.Free
        || fl == ReadWriteLockResources.Write
    {
      new_g, m' := ReadWriteLockResources.transform_TakeWriteFinishBack(ptr, fl, old_g, m);
    } else {
      new_g := old_g;
      m' := m;
    }
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := bit_and(f, flag_back) == 0;
  }
}
