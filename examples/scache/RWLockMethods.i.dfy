include "RWLock.i.dfy"

module RWLockMethods {
  import Ptrs
  import CacheResources
  import opened NativeTypes
  import opened Constants
  import opened Options
  import opened RWLock

  method transform_2_4(
      linear a1: R, linear a2: R,
      ghost c1: R, ghost c2: R, ghost c3: R, ghost c4: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R,
    linear b4: R)
  requires transform_step(multiset{a1, a2}, multiset{c1, c2, c3, c4},
      BasicStep(multiset{a2}, multiset{c2, c3, c4},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3 && b4 == c4

  method transform_4_2(
      linear a1: R, linear a2: R, linear a3: R, linear a4: R,
      ghost c1: R, ghost c2: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R)
  requires transform_step(multiset{a1, a2, a3, a4}, multiset{c1, c2},
      BasicStep(multiset{a2, a3, a4}, multiset{c2},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2

  method GetInv2(shared r: R, shared t: R)
  requires r != t
  ensures Inv2(r, t)
  ensures Inv2(t, r)

  method GetGlobalInvs(shared r: R)
  requires r.Internal? && r.q.Global?
  ensures exists m :: InvGlobal(r.q.g, m)

  method unsafe_obtain_g() returns (linear r: R) ensures r.Internal? && r.q.Global?
  method unsafe_dispose_g(linear r: R) requires r.Internal? && r.q.Global?

  method transform_TakeWriteBack(key: Key, linear flags: R)
  returns (linear flags': R, linear r': R, /*readonly*/ linear handle': Handle)
  requires flags == Internal(FlagsField(key, Available))
  ensures flags' == Internal(FlagsField(key, WriteBack))
  ensures r' == Internal(WriteBackObtained(key))
  ensures handle'.is_handle(key)
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);

    var state := g.q.g[key];
    var newState := state.(backHeld := true);

    ghost var step := TakeWriteBackStep(flags, 
        Internal(FlagsField(key, WriteBack)),
        Internal(WriteBackObtained(key)),
        Const(state.handle.value));

    linear var exc_handle';
    g', flags', r', exc_handle' := transform_2_4(g, flags,
      Internal(Global(g.q.g[key := newState])),
      step.flags', step.r', step.handle',
      g.q.g, key, state, newState, step);

    linear var Const(handle'_) := exc_handle';
    handle' := handle'_;
    unsafe_dispose_g(g');
  }

  method pre_ReleaseWriteBack(key: Key, fl: Flag,
    shared t: R, shared u: R)
  requires t == Internal(FlagsField(key, fl))
  requires u == Internal(WriteBackObtained(key))
  ensures fl == WriteBack || fl == WriteBack_PendingExcLock
  {
    linear var g := unsafe_obtain_g();
    GetGlobalInvs(g);
    GetInv2(t, u);
    GetInv2(t, g);
    GetInv2(u, g);
    unsafe_dispose_g(g);
  }

  method transform_ReleaseWriteBack(key: Key, fl: Flag,
    linear flags: R, linear r: R, /*readonly*/ linear handle: Handle)
  returns (linear r': R)
  requires flags == Internal(FlagsField(key, fl))
  requires r == Internal(WriteBackObtained(key))
  requires handle.is_handle(key)
  ensures fl == WriteBack || fl == WriteBack_PendingExcLock
  ensures fl == WriteBack ==> r' == Internal(FlagsField(key, Available))
  ensures fl == WriteBack_PendingExcLock ==> r' == Internal(FlagsField(key, PendingExcLock))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    /*assert fl != Unmapped;
    assert fl != Reading;
    assert fl != Reading_ExcLock;
    assert fl != Available;
    assert fl != PendingExcLock;
    assert fl != ExcLock_Clean;
    assert fl != ExcLock_Dirty;*/

    var state := g.q.g[key];
    var newState := state.(backHeld := false);

    ghost var step := ReleaseWriteBackStep(flags, r, Const(handle),
        Internal(FlagsField(key, if fl == WriteBack then Available else PendingExcLock)),
        fl);

    //assert ReleaseWriteBack(key, state, newState,
    //    multiset{flags, r, Const(handle)},
    //    multiset{step.flags'},
    //    flags, r, Const(handle), step.flags', fl);

    g', r' := transform_4_2(g, flags, r, Const(handle),
      Internal(Global(g.q.g[key := newState])),
      step.flags',
      g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_TakeExcLock(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, Available))
  ensures t == Internal(FlagsField(key, PendingExcLock))
  ensures u == Internal(ExcLockPendingAwaitWriteBack(key, -1))

  method transform_TakeExcLockAwaitWriteBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, WriteBack))
  ensures t == Internal(FlagsField(key, WriteBack_PendingExcLock))
  ensures u == Internal(ExcLockPendingAwaitWriteBack(key, -1))

  method transform_TakeExcLockFinishWriteBack(key: Key, t: int, fl: Flag, clean: bool, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires fl != WriteBack && fl != WriteBack_PendingExcLock
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(ExcLockPendingAwaitWriteBack(key, t))
  ensures fl == PendingExcLock
  ensures clean ==> t1 == Internal(FlagsField(key, ExcLock_Clean))
  ensures !clean ==> t1 == Internal(FlagsField(key, ExcLock_Dirty))
  ensures t2 == Internal(ExcLockPending(key, t, 0, clean))

  method transform_TakeExcLockCheckSharedLockZero(key: Key, t: int, idx: int, clean: bool, shared s1: R, linear s2: R)
  returns (linear t2: R)
  requires s1 == Internal(SharedLockRefCount(key, idx,
      if t == idx then 1 else 0))
  requires s2 == Internal(ExcLockPending(key, t, idx, clean))
  ensures t2 == Internal(ExcLockPending(key, t, idx + 1, clean))

  method transform_TakeExcLockFinish(key: Key, t: int, clean: bool, linear s1: R)
  returns (linear t1: R, linear t2: Handle)
  requires s1 == Internal(ExcLockPending(key, t, NUM_THREADS, clean))
  ensures t1 == Internal(ExcLockObtained(key, t, clean))
  ensures t2.is_handle(key)

  method transform_Alloc(key: Key, linear s1: R)
  returns (linear t1: R, linear t2: R, linear handle: Handle)
  requires s1 == Internal(FlagsField(key, Unmapped))
  ensures t1 == Internal(FlagsField(key, Reading_ExcLock))
  ensures t2 == Internal(ReadingPending(key))
  ensures handle.is_handle(key)
  ensures handle.idx.v == -1

  method transform_ReadingIncCount(key: Key, t: int, refcount: uint8,
      linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == Internal(SharedLockRefCount(key, t, refcount))
  requires s2 == Internal(ReadingPending(key))
  ensures refcount < 0xff
  ensures t1 == Internal(SharedLockRefCount(key, t, refcount + 1))
  ensures t2 == Internal(ReadingPendingCounted(key, t))

  method transform_ObtainReading(key: Key, t: int, fl: Flag,
      linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(ReadingPendingCounted(key, t))
  ensures fl == Reading_ExcLock
  ensures t1 == Internal(FlagsField(key, Reading))
  ensures t2 == Internal(ReadingObtained(key, t))

  method pre_ReadingToShared(key: Key, t: int, fl: Flag,
      shared s1: R, shared s2: R)
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(ReadingObtained(key, t))
  ensures fl == Reading

  method transform_ReadingToShared(key: Key, t: int, fl: Flag,
      linear s1: R, linear s2: R, linear handle: Handle)
  returns (linear t1: R, linear t2: R, /*readonly*/ linear handle_out: Handle)
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(ReadingObtained(key, t))
  requires handle.is_handle(key)
  ensures fl == Reading
  ensures t1 == Internal(FlagsField(key, Available))
  ensures t2 == Internal(SharedLockObtained(key, t))
  ensures handle_out == handle

  method transform_SharedIncCount(
      key: Key, t: int, refcount: uint8,
      linear s1: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == Internal(SharedLockRefCount(key, t, refcount))
  ensures refcount < 0xff
  ensures t1 == Internal(SharedLockRefCount(key, t, refcount + 1))
  ensures t2 == Internal(SharedLockPending(key, t))

  method transform_SharedDecCountPending(
      key: Key, t: int, refcount: uint8,
      linear s1: R, linear s2: R)
  returns (linear t1: R)
  requires s1 == Internal(SharedLockRefCount(key, t, refcount))
  requires s2 == Internal(SharedLockPending(key, t))
  ensures refcount > 0
  ensures t1 == Internal(SharedLockRefCount(key, t, refcount - 1))

  method transform_SharedDecCountObtained(
      key: Key, t: int, refcount: uint8,
      linear s1: R, linear s2: R, linear s3: Handle)
  returns (linear t1: R)
  requires s1 == Internal(SharedLockRefCount(key, t, refcount))
  requires s2 == Internal(SharedLockObtained(key, t))
  requires s3.is_handle(key)
  ensures refcount > 0
  ensures t1 == Internal(SharedLockRefCount(key, t, refcount - 1))

  method transform_SharedCheckExcFree(
      key: Key, t: int, fl: Flag,
      linear s1: R, shared s2: R)
  returns (linear t1: R)
  requires fl == Available || fl == WriteBack || fl == Reading
  requires s1 == Internal(SharedLockPending(key, t))
  requires s2 == Internal(FlagsField(key, fl))
  ensures t1 == Internal(SharedLockPending2(key, t))

  method transform_SharedCheckReading(
      key: Key, t: int, fl: Flag,
      linear s1: R, shared s2: R
  )
  returns (
      linear t1: R,
      /*readonly*/ linear handle: Handle
  )
  requires fl != Reading && fl != Reading_ExcLock
  requires s1 == Internal(SharedLockPending2(key, t))
  requires s2 == Internal(FlagsField(key, fl))
  ensures t1 == Internal(SharedLockObtained(key, t))
  ensures handle.is_handle(key)

  method possible_flags_SharedLockPending2(key: Key, t: int, fl: Flag,
      shared r: R, shared f: R)
  requires r == Internal(SharedLockPending2(key, t))
  requires f == Internal(FlagsField(key, fl))
  ensures fl != Unmapped

  method transform_unmap(key: Key, fl: Flag, clean: bool,
      linear flags: R,
      linear handle: Handle,
      linear r: R
  )
  returns (
      linear flags': R
  )
  requires flags == Internal(FlagsField(key, fl))
  requires handle.is_handle(key)
  requires r == Internal(ExcLockObtained(key, -1, clean))
  ensures flags' == Internal(FlagsField(key, Unmapped))
  ensures clean ==> fl == ExcLock_Clean
  ensures !clean ==> fl == ExcLock_Dirty

  method abandon_ExcLockPending(key: Key, fl: Flag, visited: int, clean: bool,
      linear r: R, linear f: R)
  returns (linear f': R)
  requires r == Internal(ExcLockPending(key, -1, visited, clean))
  requires f == Internal(FlagsField(key, fl))
  ensures clean ==> fl == ExcLock_Clean
  ensures !clean ==> fl == ExcLock_Dirty
  ensures f' == Internal(FlagsField(key, Available))
}
