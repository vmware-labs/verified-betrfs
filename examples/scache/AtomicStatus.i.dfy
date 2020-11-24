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

  const flag_free : uint8 := 0;
  const flag_back : uint8 := 1;
  const flag_write : uint8 := 2;
  const flag_back_write : uint8 := 3;

  type AtomicStatus = Atomic<uint8, RWLock.R>

  predicate state_inv(v: uint8, g: RWLock.R, key: RWLock.Key)
  {
    && g.Internal?
    && g.q.FlagsField?
    && g.q.key == key
    && (g.q.flags == RWLock.Free ==> v == flag_free)
    && (g.q.flags == RWLock.Back ==> v == flag_back)
    && (g.q.flags == RWLock.Write ==> v == flag_write)
    && (g.q.flags == RWLock.Back_PendingWrite ==>
        v == flag_back_write)
  }

  predicate atomic_status_inv(a: AtomicStatus, key: RWLock.Key)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, key)
  }

  method unsafe_obtain<Q>() returns (linear r: Q)
  method unsafe_dispose<Q>(linear r: Q)

  method try_acquire_writeback(a: AtomicStatus, key: RWLock.Key)
  returns (success: bool, linear m: maybe<RWLock.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.BackObtained(key))
  {
    // TODO check if the acquire flag is set

    var cur_flag := atomic_read(a);
    if cur_flag != flag_free {
      m := empty();
      success := false;
    } else {
      var did_set := compare_and_set(a, flag_free, flag_back);

      ///// Begin jank
      ///// Setup:
      var v1 := flag_free;
      var v2 := flag_back;
      var old_v: uint8;
      var new_v: uint8;
      linear var old_g: RWLock.R := unsafe_obtain();
      assume old_v == v1 ==> new_v == v2 && did_set;
      assume old_v != v1 ==> new_v == old_v && !did_set;
      assume atomic_inv(a, old_v, old_g);
      linear var new_g;
      ///// Transfer:
      if did_set {
        linear var res;
        new_g, res := RWLock.transform_TakeBack(key, old_g);
        m := give(res);
      } else {
        m := empty();
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

  method try_set_write_lock(a: AtomicStatus, key: RWLock.Key)
  returns (success: bool, linear m: maybe<RWLock.R>)
  requires atomic_status_inv(a, key)
  ensures !success ==> !has(m)
  ensures success ==> has(m)
      && read(m) == RWLock.Internal(RWLock.WritePendingAwaitBack(key))
  {
    var orig_value := fetch_or(a, flag_write);

    ///// Begin jank
    ///// Setup:
    var v := flag_write;
    var old_v: uint8;
    var new_v: uint8;
    linear var old_g: RWLock.R := unsafe_obtain();
    assume orig_value == old_v;
    assume new_v == bit_or(old_v, v);
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    var fl := old_g.q.flags;
    if fl == RWLock.Free {
      linear var r;
      new_g, r := RWLock.transform_TakeWrite(key, old_g);
      m := give(r);
    } else if fl == RWLock.Back {
      linear var r;
      new_g, r := RWLock.transform_TakeWriteAwaitBack(key, old_g);
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

  method try_check_writeback_isnt_set(a: AtomicStatus, key: RWLock.Key,
      linear m: RWLock.R)
  returns (success: bool, linear m': RWLock.R)
  requires atomic_status_inv(a, key)
  requires m == RWLock.Internal(RWLock.WritePendingAwaitBack(key))
  ensures !success ==> m' == m
  ensures success ==> m' == RWLock.Internal(RWLock.WritePending(key, 0))
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
    if fl == RWLock.Free
        || fl == RWLock.Write
    {
      new_g, m' := RWLock.transform_TakeWriteFinishBack(key, fl, old_g, m);
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
