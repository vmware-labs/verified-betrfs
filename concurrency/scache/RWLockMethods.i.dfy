include "RWLock.i.dfy"

module RWLockMethods {
  import Ptrs
  import CacheResources
  import opened NativeTypes
  import opened Constants
  import opened Options
  import opened RWLock

  method transform_1_2_2(
      shared s1: R,
      linear a1: R, linear a2: R,
      ghost c1: R, ghost c2: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R)
  requires transform_step(multiset{s1, a1, a2}, multiset{s1, c1, c2},
      BasicStep(multiset{s1, a2}, multiset{s1, c2},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2

  method transform_1_2_3(
      shared s1: R,
      linear a1: R, linear a2: R,
      ghost c1: R, ghost c2: R, ghost c3: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R)
  requires transform_step(multiset{s1, a1, a2}, multiset{s1, c1, c2, c3},
      BasicStep(multiset{s1, a2}, multiset{s1, c2, c3},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3

  method transform_2_3(
      linear a1: R, linear a2: R,
      ghost c1: R, ghost c2: R, ghost c3: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R)
  requires transform_step(multiset{a1, a2}, multiset{c1, c2, c3},
      BasicStep(multiset{a2}, multiset{c2, c3},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3

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

  method transform_3_3(
      linear a1: R, linear a2: R, linear a3: R,
      ghost c1: R, ghost c2: R, ghost c3: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R)
  requires transform_step(multiset{a1, a2, a3}, multiset{c1, c2, c3},
      BasicStep(multiset{a2, a3}, multiset{c2, c3},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3

  method transform_4_2(
      linear a1: R, linear a2: R, linear a3: R, linear a4: R,
      ghost c1: R, ghost c2: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R)
  requires transform_step(multiset{a1, a2, a3, a4}, multiset{c1, c2},
      BasicStep(multiset{a2, a3, a4}, multiset{c2},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2

  method transform_4_3(
      linear a1: R, linear a2: R, linear a3: R, linear a4: R,
      ghost c1: R, ghost c2: R, ghost c3: R,
      ghost g: map<Key, RWLockState>,
      key: Key, state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R)
  requires transform_step(multiset{a1, a2, a3, a4}, multiset{c1, c2, c3},
      BasicStep(multiset{a2, a3, a4}, multiset{c2, c3},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3

  method transform_4_4(
      linear a1: R, linear a2: R, linear a3: R, linear a4: R,
      ghost c1: R, ghost c2: R, ghost c3: R, ghost c4: R,
      ghost g: map<Key, RWLockState>,
      key: Key, ghost state: RWLockState, ghost state': RWLockState,
      ghost basicStep: BasicStep)
  returns (
    linear b1: R,
    linear b2: R,
    linear b3: R,
    linear b4: R)
  requires transform_step(multiset{a1, a2, a3, a4}, multiset{c1, c2, c3, c4},
      BasicStep(multiset{a2, a3, a4}, multiset{c2, c3, c4},
        g, key, state, state', basicStep))
  ensures b1 == c1 && b2 == c2 && b3 == c3 && b4 == c4

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

  method transform_ThreadlessExc(key: Key, linear flags: R, fl: Flag)
  returns (linear flags': R, linear r': R, /*readonly*/ linear handle': Handle)
  requires fl == Available || fl == WriteBack
  requires flags == Internal(FlagsField(key, fl))
  ensures flags' == Internal(FlagsField(key,
      if fl == Available then PendingExcLock else WriteBack_PendingExcLock))
  ensures r' == Internal(ExcLockPendingAwaitWriteBack(key, -1))
  ensures handle'.is_handle(key)
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);

    var state := g.q.g[key];
    var newState := state.(excState := WLSPendingAwaitWriteBack(-1));

    ghost var step := ThreadlessExcStep(flags,
        Internal(FlagsField(key,
            if fl == Available then PendingExcLock else WriteBack_PendingExcLock)),
        Internal(ExcLockPendingAwaitWriteBack(key, -1)),
        Const(state.handle.value),
        fl);

    linear var handle_const;
    g', flags', r', handle_const := transform_2_4(g, flags,
        Internal(Global(g.q.g[key := newState])),
        step.flags', step.r', step.handle',
        g.q.g, key, state, newState, step);

    linear var Const(handle_out) := handle_const;
    handle' := handle_out;

    unsafe_dispose_g(g');
  }

  method transform_TakeExcLockFinishWriteBack(key: Key, t: int, fl: Flag, clean: bool, linear flags: R, linear r: R)
  returns (linear flags': R, linear r': R)
  requires fl != WriteBack && fl != WriteBack_PendingExcLock
  requires flags == Internal(FlagsField(key, fl))
  requires r == Internal(ExcLockPendingAwaitWriteBack(key, t))
  ensures fl == PendingExcLock
  ensures clean ==> flags' == Internal(FlagsField(key, ExcLock_Clean))
  ensures !clean ==> flags' == Internal(FlagsField(key, ExcLock_Dirty))
  ensures r' == Internal(ExcLockPending(key, t, 0, clean))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    var newState := state.(excState := WLSPending(t, 0, clean));

    ghost var step := TakeExcLockFinishWriteBackStep(flags, r,
        Internal(FlagsField(key,
          if clean then ExcLock_Clean else ExcLock_Dirty)),
        Internal(ExcLockPending(key, t, 0, clean)), t, fl, clean);

    g', flags', r' := transform_3_3(g, flags, r,
        Internal(Global(g.q.g[key := newState])),
        step.flags', step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_TakeExcLockSharedLockZero(key: Key, t: int, idx: int, clean: bool, shared refcount: R, linear r: R)
  returns (linear r': R)
  requires refcount == Internal(SharedLockRefCount(key, idx, if t == idx then 1 else 0))
  requires r == Internal(ExcLockPending(key, t, idx, clean))
  ensures r' == Internal(ExcLockPending(key, t, idx + 1, clean))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, refcount);
    GetInv2(g, r);

    var state := g.q.g[key];
    var newState := state.(excState := WLSPending(t, idx + 1, clean));

    ghost var step := TakeExcLockSharedLockZeroStep(refcount, r,
        Internal(ExcLockPending(key, t, idx + 1, clean)),t, idx, clean);

    g', r' := transform_1_2_2(refcount, g, r,
        Internal(Global(g.q.g[key := newState])),
        step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_TakeExcLockFinish(key: Key, t: int, clean: bool,
      linear r: R, /*readonly*/ linear handle: Handle)
  returns (linear r': R, linear handle': Handle)
  requires r == Internal(ExcLockPending(key, t, NUM_THREADS, clean))
  requires handle.is_handle(key)
  ensures r' == Internal(ExcLockObtained(key, t, clean))
  ensures handle' == handle
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, r);

    var state := g.q.g[key];
    var newState := state
        .(excState := WLSObtained(t, clean))
        .(handle := None);

    ghost var step := TakeExcLockFinishStep(r, Const(handle),
        Internal(ExcLockObtained(key, t, clean)),
        Exc(handle),
        t, clean);

    linear var handle_exc;
    g', r', handle_exc := transform_3_3(g, r, Const(handle),
        Internal(Global(g.q.g[key := newState])),
        step.r', step.handle',
        g.q.g, key, state, newState, step);

    linear var Exc(handle_out) := handle_exc;
    handle' := handle_out;

    unsafe_dispose_g(g');
  }

  method transform_Alloc(key: Key, linear flags: R)
  returns (linear flags': R, linear r': R, linear handle': Handle)
  requires flags == Internal(FlagsField(key, Unmapped))
  ensures flags' == Internal(FlagsField(key, Reading_ExcLock))
  ensures r' == Internal(ReadingPending(key))
  ensures handle'.is_handle(key)
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);

    var state := g.q.g[key];
    var newState := state
        .(unmapped := false)
        .(handle := None)
        .(readState := RSPending);

    ghost var step := AllocStep(flags,
        Internal(FlagsField(key, Reading_ExcLock)),
        Internal(ReadingPending(key)),
        Exc(state.handle.value));

    linear var handle_exc;
    g', flags', r', handle_exc := transform_2_4(g, flags,
        Internal(Global(g.q.g[key := newState])),
        step.flags', step.r', step.handle',
        g.q.g, key, state, newState, step);

    linear var Exc(handle_out) := handle_exc;
    handle' := handle_out;

    unsafe_dispose_g(g');
  }

  method transform_ReadingIncCount(key: Key, t: int, refcount: uint8,
      linear client: R, linear rc: R, linear r: R)
  returns (linear rc': R, linear r': R)
  requires client == Internal(Client(t))
  requires rc == Internal(SharedLockRefCount(key, t, refcount))
  requires r == Internal(ReadingPending(key))
  ensures rc' == Internal(SharedLockRefCount(key, t,
      if refcount == 255 then 0 else refcount + 1))
  ensures r' == Internal(ReadingPendingCounted(key, t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, rc);
    GetInv2(g, r);
    GetInv2(g, client);

    var state := g.q.g[key];
    var newState := state
        .(readCounts := state.readCounts[t := state.readCounts[t] + 1])
        .(readState := RSPendingCounted(t));

    ghost var step := ReadingIncCountStep(client, rc, r,
        Internal(SharedLockRefCount(key, t, if refcount == 255 then 0 else refcount + 1)),
        Internal(ReadingPendingCounted(key, t)), t, refcount);

    g', rc', r' := transform_4_3(g, client, rc, r,
        Internal(Global(g.q.g[key := newState])),
        step.rc', step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_ObtainReading(key: Key, t: int, fl: Flag,
      linear flags: R, linear r: R)
  returns (linear flags': R, linear r': R)
  requires flags == Internal(FlagsField(key, fl))
  requires r == Internal(ReadingPendingCounted(key, t))
  ensures fl == Reading_ExcLock
  ensures flags' == Internal(FlagsField(key, Reading))
  ensures r' == Internal(ReadingObtained(key, t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, r);
    GetInv2(g, flags);

    var state := g.q.g[key];
    var newState := state.(readState := RSObtained(t));

    ghost var step := ObtainReadingStep(flags, r,
      Internal(FlagsField(key, Reading)),
      Internal(ReadingObtained(key, t)), t, fl);

    g', flags', r' := transform_3_3(g, flags, r,
        Internal(Global(g.q.g[key := newState])),
        step.flags', step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method pre_ReadingToShared(key: Key, t: int, fl: Flag,
      shared flags: R, shared r: R)
  requires flags == Internal(FlagsField(key, fl))
  requires r == Internal(ReadingObtained(key, t))
  ensures fl == Reading
  {
    linear var g := unsafe_obtain_g();
    GetGlobalInvs(g);
    GetInv2(flags, r);
    GetInv2(g, flags);
    GetInv2(g, r);
    unsafe_dispose_g(g);
  }

  method transform_ReadingToShared(key: Key, t: int, fl: Flag,
      linear flags: R, linear r: R, linear handle: Handle)
  returns (linear flags': R, linear r': R, /*readonly*/ linear handle': Handle)
  requires flags == Internal(FlagsField(key, fl))
  requires r == Internal(ReadingObtained(key, t))
  requires handle.is_handle(key)
  ensures fl == Reading
  ensures flags' == Internal(FlagsField(key, Available))
  ensures r' == Internal(SharedLockObtained(key, t))
  ensures handle' == handle
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, r);
    GetInv2(g, flags);

    var state := g.q.g[key];
    ghost var newState := state
      .(readState := RSNone)
      .(handle := Some(handle));

    ghost var step := ReadingToSharedStep(flags, r, Exc(handle),
      Internal(FlagsField(key, Available)),
      Internal(SharedLockObtained(key, t)),
      Const(handle),
      t, fl);

    assert ReadingToShared(key, state, newState,
      multiset{step.flags, step.r, step.handle},
      multiset{step.flags', step.r', step.handle'},
      step.flags, step.r, step.handle,
      step.flags', step.r', step.handle',
      t, fl);

    linear var handle_const;
    g', flags', r', handle_const := transform_4_4(g, flags, r, Exc(handle),
        Internal(Global(g.q.g[key := newState])),
        step.flags', step.r', step.handle',
        g.q.g, key, state, newState, step);


    linear var Const(handle_out) := handle_const;
    handle' := handle_out;

    unsafe_dispose_g(g');
  }

  method transform_SharedIncCount(
      key: Key, t: int, refcount: uint8,
      linear client: R, linear rc: R)
  returns (linear rc': R, linear r': R)
  requires client == Internal(Client(t))
  requires rc == Internal(SharedLockRefCount(key, t, refcount))
  ensures rc' == Internal(SharedLockRefCount(key, t,
      if refcount == 255 then 0 else refcount + 1))
  ensures r' == Internal(SharedLockPending(key, t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, rc);
    GetInv2(g, client);

    var state := g.q.g[key];
    ghost var newState := state
        .(readCounts := state.readCounts[t := state.readCounts[t] + 1]);

    ghost var step := SharedIncCountStep(client, rc,
      Internal(SharedLockRefCount(key, t,
          if refcount == 255 then 0 else refcount + 1)),
      Internal(SharedLockPending(key, t)),
      t, refcount);

    g', rc', r' := transform_3_3(g, client, rc,
        Internal(Global(g.q.g[key := newState])),
        step.rc', step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_SharedDecCountPending(
      key: Key, t: int, refcount: uint8,
      linear rc: R, linear r: R)
  returns (linear rc': R, linear client': R)
  requires rc == Internal(SharedLockRefCount(key, t, refcount))
  requires r == Internal(SharedLockPending(key, t))
  ensures rc' == Internal(SharedLockRefCount(key, t,
      if refcount == 0 then 255 else refcount - 1))
  ensures client' == Internal(Client(t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, rc);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state
          .(readCounts := state.readCounts[t := state.readCounts[t] - 1]);

    ghost var step := SharedDecCountPendingStep(rc, r,
      Internal(SharedLockRefCount(key, t,
        if refcount == 0 then 255 else refcount - 1)),
      Internal(Client(t)),
      t, refcount);

    g', rc', client' := transform_3_3(g, rc, r,
        Internal(Global(g.q.g[key := newState])),
        step.rc', step.client',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_SharedDecCountObtained(
      key: Key, t: int, refcount: uint8,
      linear rc: R, linear r: R, linear handle: Handle)
  returns (linear rc': R, linear client': R)
  requires rc == Internal(SharedLockRefCount(key, t, refcount))
  requires r == Internal(SharedLockObtained(key, t))
  requires handle.is_handle(key)
  ensures rc' == Internal(SharedLockRefCount(key, t,
    if refcount == 0 then 255 else refcount - 1))
  ensures client' == Internal(Client(t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, rc);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state
          .(readCounts := state.readCounts[t := state.readCounts[t] - 1]);

    ghost var step := SharedDecCountObtainedStep(rc, r, Const(handle),
      Internal(SharedLockRefCount(key, t,
        if refcount == 0 then 255 else refcount - 1)),
      Internal(Client(t)),
      t, refcount);

    g', rc', client' := transform_4_3(g, rc, r, Const(handle),
        Internal(Global(g.q.g[key := newState])),
        step.rc', step.client',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_SharedCheckExcFree(
      key: Key, t: int, fl: Flag,
      linear r: R, shared flags: R)
  returns (linear r': R)
  requires fl == Available || fl == WriteBack || fl == Reading
  requires r == Internal(SharedLockPending(key, t))
  requires flags == Internal(FlagsField(key, fl))
  ensures r' == Internal(SharedLockPending2(key, t))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state;

    ghost var step := SharedCheckExcFreeStep(r, flags,
      Internal(SharedLockPending2(key, t)),
      t, fl);

    g', r' := transform_1_2_2(flags, g, r,
        Internal(Global(g.q.g[key := newState])),
        step.r',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method transform_SharedCheckReading(
      key: Key, t: int, fl: Flag,
      linear r: R, shared flags: R
  )
  returns (
      linear r': R,
      /*readonly*/ linear handle': Handle
  )
  requires fl != Reading && fl != Reading_ExcLock
  requires r == Internal(SharedLockPending2(key, t))
  requires flags == Internal(FlagsField(key, fl))
  ensures r' == Internal(SharedLockObtained(key, t))
  ensures handle'.is_handle(key)
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state;

    ghost var step := SharedCheckReadingStep(r, flags,
      Internal(SharedLockObtained(key, t)),
      Const(state.handle.value),
      t, fl);

    linear var handle_const;
    g', r', handle_const := transform_1_2_3(flags, g, r,
        Internal(Global(g.q.g[key := newState])),
        step.r', step.handle',
        g.q.g, key, state, newState, step);

    linear var Const(handle_out) := handle_const;
    handle' := handle_out;

    unsafe_dispose_g(g');
  }

  method possible_flags_SharedLockPending2(key: Key, t: int, fl: Flag,
      shared r: R, shared f: R)
  requires r == Internal(SharedLockPending2(key, t))
  requires f == Internal(FlagsField(key, fl))
  ensures fl != Unmapped
  {
    linear var g := unsafe_obtain_g();
    GetGlobalInvs(g);
    GetInv2(r, f);
    GetInv2(r, g);
    GetInv2(f, g);
    unsafe_dispose_g(g);
  }

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
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state
      .(unmapped := true)
      .(excState := WLSNone)
      .(handle := Some(handle));

    ghost var step := UnmapStep(flags, r, Exc(handle),
      Internal(FlagsField(key, Unmapped)),
      fl, clean);

    g', flags' := transform_4_2(g, flags, Exc(handle), r,
        Internal(Global(g.q.g[key := newState])),
        step.flags',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method abandon_ExcLockPending(key: Key, fl: Flag, visited: int, clean: bool,
      linear r: R, linear flags: R, /*readonly*/ linear handle: Handle)
  returns (linear flags': R)
  requires r == Internal(ExcLockPending(key, -1, visited, clean))
  requires flags == Internal(FlagsField(key, fl))
  requires handle.is_handle(key)
  ensures clean ==> fl == ExcLock_Clean
  ensures !clean ==> fl == ExcLock_Dirty
  ensures flags' == Internal(FlagsField(key, Available))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state.(excState := WLSNone);

    ghost var step := AbandonExcLockPendingStep(flags, r, Const(handle),
      Internal(FlagsField(key, Available)),
      fl, visited, clean);

    g', flags' := transform_4_2(g, flags, Const(handle), r,
        Internal(Global(g.q.g[key := newState])),
        step.flags',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }

  method abandon_ReadingPending(key: Key, fl: Flag,
      linear r: R, linear flags: R, /*readonly*/ linear handle: Handle)
  returns (linear flags': R)
  requires r == Internal(ReadingPending(key))
  requires flags == Internal(FlagsField(key, fl))
  requires handle.is_handle(key)
  ensures fl == Reading_ExcLock
  ensures flags' == Internal(FlagsField(key, Unmapped))
  {
    linear var g := unsafe_obtain_g();
    linear var g';

    GetGlobalInvs(g);
    GetInv2(g, flags);
    GetInv2(g, r);

    var state := g.q.g[key];
    ghost var newState := state.(readState := RSNone);

    ghost var step := AbandonReadingPendingStep(flags, r, Const(handle),
      Internal(FlagsField(key, Unmapped)),
      fl);

    g', flags' := transform_4_2(g, flags, Const(handle), r,
        Internal(Global(g.q.g[key := newState])),
        step.flags',
        g.q.g, key, state, newState, step);

    unsafe_dispose_g(g');
  }
}
