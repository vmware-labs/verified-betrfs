// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Constants.i.dfy"
include "ResourceBuilderSpec.s.dfy"
include "CacheResources.i.dfy"
include "Multisets.i.dfy"

module RWLock refines ResourceBuilderSpec {
  import Ptrs
  import CacheResources
  import opened NativeTypes
  import opened Constants
  import opened Options
  import opened MultisetUtil

  datatype Key = Key(data_ptr: Ptrs.Ptr, idx_ptr: Ptrs.Ptr, cache_idx: int)

  linear datatype Handle = CacheEntryHandle(
      key: Key,
      linear cache_entry: CacheResources.R,
      linear data: Ptrs.ArrayDeref<byte>,
      linear idx: Ptrs.Deref<int>
  )
  {
    predicate is_handle(key: Key)
    {
      && this.key == key
      && this.cache_entry.CacheEntry?
      && this.cache_entry.cache_idx == key.cache_idx
      && this.data.ptr == key.data_ptr
      && this.idx.ptr == key.idx_ptr
      && |this.data.s| == 4096
      && this.cache_entry.data == this.data.s
      && this.cache_entry.disk_idx == this.idx.v
      && 0 <= this.idx.v < NUM_DISK_PAGES
    }
  }

  type V = Handle

  /*
   * We consider two bits of the status field, ExcLock and WriteBack.
   *
   * ExcLock and WriteBack. Of course, 'ExcLock'
   * and 'WriteBack' should be exclusive operations;
   * When both flags are set,
   * it should be interpreted as the 'ExcLock' being
   * pending, with the 'WriteBack' being active.
   *
   * Those 2 bits gives 2x2 = 4 states. We then have 2 more:
   * Unmapped and Reading.
   *
   * NOTE: in retrospect, it might have made sense to have this
   * just be a struct of 5-6 booleans.
   */
  datatype Flag =
    | Unmapped
    | Reading
    | Reading_ExcLock
    | Available
    | WriteBack
    | WriteBack_PendingExcLock
    | PendingExcLock
    | ExcLock_Clean
    | ExcLock_Dirty

  datatype ExcState = 
    | WLSNone
    | WLSPendingAwaitWriteBack(t: int)
    | WLSPending(t: int, visited: int, clean: bool)
    | WLSObtained(t: int, clean: bool)

  datatype ReadState =
    | RSNone
    | RSPending
    | RSPendingCounted(t: int)
    | RSObtained(t: int)

  datatype RWLockState = RWLockState(
    excState: ExcState,
    readState: ReadState,
    unmapped: bool,
    backHeld: bool,
    readCounts: seq<int>,
    handle: Option<Handle>)

  datatype Q =
    | Global(g: map<Key, RWLockState>)
    | FlagsField(key: Key, flags: Flag)
    | SharedLockRefCount(key: Key, t: int, refcount: uint8)

    | Client(t: int)

    // Standard flow for obtaining a 'shared' lock

    | SharedLockPending(key: Key, t: int)     // inc refcount
    | SharedLockPending2(key: Key, t: int)    // !free & !writelocked
    | SharedLockObtained(key: Key, t: int)    // !reading

    // Standard flow for obtaining an 'exclusive' lock

    | ExcLockPendingAwaitWriteBack(key: Key, t: int)
        // set ExcLock bit
    | ExcLockPending(key: Key, t: int, visited: int, clean: bool)
        // check WriteBack bit unset
        //   and `visited` of the refcounts
    | ExcLockObtained(key: Key, t: int, clean: bool)

    // Flow for the phase of reading in a page from disk.
    // This is a special-case flow, because it needs to be performed
    // on the way to obtaining a 'shared' lock, but it requires
    // exclusive access to the underlying memory and resources.
    // End-game for this flow is to become an ordinary 'shared' lock

    | ReadingPending(key: Key)                // set status bit to 
                                              //   ExcLock | Reading
    | ReadingPendingCounted(key: Key, t: int) // inc refcount
    | ReadingObtained(key: Key, t: int)       // clear ExcLock bit

    // Flow for the phase of doing a write-back.
    // Special case in part because it can be initiated by any thread
    // and completed by any thread (not necessarily the same one).
    
    | WriteBackObtained(key: Key)             // set WriteBack status bit

  datatype BasicStep =
    | TakeWriteBackStep(flags: R, flags': R, r': R, handle': R)
    | ReleaseWriteBackStep(flags: R, r: R, handle: R, flags': R, fl: Flag)
    | ThreadlessExcStep(flags: R, flags': R, r': R, handle': R, fl: Flag)
    | SharedToExcStep(flags: R, r: R, flags': R, r': R, t: int, fl: Flag)
    | TakeExcLockFinishWriteBackStep(flags: R, r: R, flags': R, r': R,
          t: int, fl: Flag, clean: bool)
    | TakeExcLockSharedLockZeroStep(rc_rc': R, r: R, r': R,
          t: int, idx: int, clean: bool)
    | TakeExcLockFinishStep(r: R, handle: R, r': R, handle': R, t: int, clean: bool) 
    | DowngradeExcLockStep(r: R, handle: R, flags: R, r': R, handle': R, flags': R, fl: Flag, t: int, clean: bool) 
    | AllocStep(flags: R, flags': R, r': R, handle': R)
    | ReadingIncCountStep(client: R, rc: R, r: R, rc': R, r': R, t: int, refcount: uint8)
    | ObtainReadingStep(flags: R, r: R, flags': R, r': R, t: int, fl: Flag)
    | ReadingToSharedStep(flags: R, r: R, handle: R, flags': R, r': R, handle': R, t: int, fl: Flag)
    | SharedIncCountStep(client: R, rc: R, rc': R, r': R, t: int, refcount: uint8)
    | SharedDecCountPendingStep(rc: R, r: R, rc': R, client': R, t: int, refcount: uint8)
    | SharedDecCountObtainedStep(rc: R, r: R, handle: R, rc': R, client': R, t: int, refcount: uint8)
    | SharedCheckExcFreeStep(r: R, flags_flags': R, r': R, t: int, fl: Flag)
    | SharedCheckReadingStep(r: R, flags_flags': R, r': R, handle': R, t: int, fl: Flag)
    | UnmapStep(flags: R, r: R, handle: R, flags': R, fl: Flag, clean: bool)
    | AbandonExcLockPendingStep(flags: R, r: R, handle: R, flags': R, fl: Flag, visited: int, clean: bool)
    | AbandonReadingPendingStep(flags: R, r: R, handle: R, flags': R, fl: Flag)

  predicate TakeWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R,
    flags': R, r': R, handle': R)
  {
    && a == multiset{flags}
    && a' == multiset{flags', r', handle'}
    && state' == state.(backHeld := true)
    && flags == Internal(FlagsField(key, Available))
    && flags' == Internal(FlagsField(key, WriteBack))
    && r' == Internal(WriteBackObtained(key))
    && (state.handle.Some? ==>
      handle' == Const(state.handle.value))
  }

  predicate ReleaseWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, handle: R,
    flags': R,
    fl: Flag)
  {
    && a == multiset{flags, r, handle}
    && a' == multiset{flags'}
    && state' == state.(backHeld := false)
    && flags == Internal(FlagsField(key, fl))
    && r == Internal(WriteBackObtained(key))
    && (fl == WriteBack ==>
        flags' == Internal(FlagsField(key, Available)))
    && (fl == WriteBack_PendingExcLock ==>
        flags' == Internal(FlagsField(key, PendingExcLock)))
    && handle.Const? && handle.v.is_handle(key)
  }

  predicate ThreadlessExc(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R,
    flags': R, r': R, handle': R,
    fl: Flag)
  {
    && a == multiset{flags}
    && a' == multiset{flags', r', handle'}
    && (fl == Available || fl == WriteBack)
    && flags == Internal(FlagsField(key, fl))
    && flags' == Internal(FlagsField(key,
        if fl == Available then PendingExcLock else WriteBack_PendingExcLock))
    && r' == Internal(ExcLockPendingAwaitWriteBack(key, -1))
    && state' == state.(excState := WLSPendingAwaitWriteBack(-1))
    && (state.handle.Some? ==> handle' == Const(state.handle.value))
  }

  predicate SharedToExc(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R,
    flags': R, r': R,
    t: int, fl: Flag)
  {
    && a == multiset{flags, r}
    && a' == multiset{flags', r'}
    && (fl == Available || fl == WriteBack)
    && flags == Internal(FlagsField(key, fl))
    && flags' == Internal(FlagsField(key,
        if fl == Available then PendingExcLock else WriteBack_PendingExcLock))
    && r == Internal(SharedLockObtained(key, t))
    && r' == Internal(ExcLockPendingAwaitWriteBack(key, t))
    && state' == state.(excState := WLSPendingAwaitWriteBack(t))
  }

  predicate TakeExcLockFinishWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R,
    flags': R, r': R,
    t: int, fl: Flag, clean: bool)
  {
    && a == multiset{flags, r}
    && a' == multiset{flags', r'}
    && fl != WriteBack && fl != WriteBack_PendingExcLock
    && state' == state.(excState := WLSPending(t, 0, clean))
    && flags == Internal(FlagsField(key, fl))
    && r == Internal(ExcLockPendingAwaitWriteBack(key, t))
    && flags' == Internal(FlagsField(key,
          if clean then ExcLock_Clean else ExcLock_Dirty))
    && r' == Internal(ExcLockPending(key, t, 0, clean))
  }

  predicate TakeExcLockSharedLockZero(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    rc_rc': R,
    r: R, r': R,
    t: int, idx: int, clean: bool)
  {
    && a == multiset{r, rc_rc'}
    && a' == multiset{r', rc_rc'}
    && state' == state.(excState := WLSPending(t, idx + 1, clean))
    && rc_rc' == Internal(SharedLockRefCount(key, idx,
        if t == idx then 1 else 0))
    && r == Internal(ExcLockPending(key, t, idx, clean))
    && r' == Internal(ExcLockPending(key, t, idx + 1, clean))
  }

  predicate TakeExcLockFinish(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    r: R, handle: R,
    r': R, handle': R,
    t: int, clean: bool)
  {
    && a == multiset{r, handle}
    && a' == multiset{r',handle'}
    && state' == state
        .(excState := WLSObtained(t, clean))
        .(handle := None)
    && r == Internal(ExcLockPending(key, t, NUM_THREADS, clean))
    && r' == Internal(ExcLockObtained(key, t, clean))
    && handle.Const?
    && handle.v.is_handle(key)
    && handle' == Exc(handle.v)
  }

  predicate DowngradeExcLock(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    r: R, handle: R, flags: R,
    r': R, handle': R, flags': R,
    fl: Flag, t: int, clean: bool)
  {
    && a == multiset{r, handle, flags}
    && a' == multiset{r', handle', flags'}
    && handle.Exc? && handle.v.is_handle(key)
    && state' == state
        .(excState := WLSNone)
        .(handle := Some(handle.v))
    && r == Internal(ExcLockObtained(key, t, clean))
    && 0 <= t < NUM_THREADS
    && flags == Internal(FlagsField(key, fl))
    && flags' == Internal(FlagsField(key, Available))
    && r' == Internal(SharedLockObtained(key, t))
    && handle' == Const(handle.v)
  }

  predicate Alloc(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R,
    flags': R, r': R, handle': R)
  {
    && a == multiset{flags}
    && a' == multiset{flags', r', handle'}
    && state' == state
        .(unmapped := false)
        .(handle := None)
        .(readState := RSPending)
    && flags == Internal(FlagsField(key, Unmapped))
    && flags' == Internal(FlagsField(key, Reading_ExcLock))
    && r' == Internal(ReadingPending(key))
    && (state.handle.Some? ==>
      handle' == Exc(state.handle.value))
  }

  predicate ReadingIncCount(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    client: R, rc: R, r: R, rc': R, r': R, t: int, refcount: uint8)
  {
    && a == multiset{rc, r, client}
    && a' == multiset{rc', r'}
    && (0 <= t < |state.readCounts| ==>
        state' == state
          .(readCounts := state.readCounts[t := state.readCounts[t] + 1])
          .(readState := RSPendingCounted(t))
    )
    && rc == Internal(SharedLockRefCount(key, t, refcount))
    && r == Internal(ReadingPending(key))
    && client == Internal(Client(t))
    && rc' == Internal(SharedLockRefCount(key, t,
        // uint8 addition
        // (we'll need to prove invariant that this doesn't overflow)
        if refcount == 255 then 0 else refcount + 1))
    && r' == Internal(ReadingPendingCounted(key, t))
  }

  predicate ObtainReading(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, flags': R, r': R, t: int, fl: Flag)
  {
    && a == multiset{flags, r}
    && a' == multiset{flags', r'}
    && state' == state.(readState := RSObtained(t))
    && flags == Internal(FlagsField(key, fl))
    && r == Internal(ReadingPendingCounted(key, t))
    && flags' == Internal(FlagsField(key, Reading))
    && r' == Internal(ReadingObtained(key, t))
  }

  predicate ReadingToShared(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, handle: R, flags': R, r': R, handle': R, t: int, fl: Flag)
  {
    && a == multiset{flags, r, handle}
    && a' == multiset{flags', r', handle'}
    && flags == Internal(FlagsField(key, fl))
    && r == Internal(ReadingObtained(key, t))
    && handle.Exc?  && handle.v.is_handle(key)
    && flags' == Internal(FlagsField(key, Available))
    && r' == Internal(SharedLockObtained(key, t))
    && handle'.Const? && handle'.v == handle.v

    && state' == state
      .(readState := RSNone)
      .(handle := Some(handle.v))
  }

  predicate SharedIncCount(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    client: R, rc: R, rc': R, r': R, t: int, refcount: uint8)
  {
    && a == multiset{client, rc}
    && a' == multiset{rc', r'}
    && rc == Internal(SharedLockRefCount(key, t, refcount))
    && client == Internal(Client(t))
    && rc' == Internal(SharedLockRefCount(key, t,
        if refcount == 255 then 0 else refcount + 1))
    && r' == Internal(SharedLockPending(key, t))

    && (0 <= t < |state.readCounts| ==>
        state' == state
          .(readCounts := state.readCounts[t := state.readCounts[t] + 1])
    )
  }

  predicate SharedDecCountPending(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    rc: R, r: R, rc': R, client': R, t: int, refcount: uint8)
  {
    && a == multiset{rc, r}
    && a' == multiset{rc', client'}
    && rc == Internal(SharedLockRefCount(key, t, refcount))
    && r == Internal(SharedLockPending(key, t))
    && rc' == Internal(SharedLockRefCount(key, t,
        if refcount == 0 then 255 else refcount - 1))

    && (0 <= t < |state.readCounts| ==>
        state' == state
          .(readCounts := state.readCounts[t := state.readCounts[t] - 1])
    )
    && client' == Internal(Client(t))
  }

  predicate SharedDecCountObtained(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    rc: R, r: R, handle: R, rc': R, client': R, t: int, refcount: uint8)
  {
    && a == multiset{rc, r, handle}
    && a' == multiset{rc', client'}
    && rc == Internal(SharedLockRefCount(key, t, refcount))
    && r == Internal(SharedLockObtained(key, t))
    && handle.Const? && handle.v.is_handle(key)
    && rc' == Internal(SharedLockRefCount(key, t,
        if refcount == 0 then 255 else refcount - 1))

    && (0 <= t < |state.readCounts| ==>
        state' == state
          .(readCounts := state.readCounts[t := state.readCounts[t] - 1])
    )
    && client' == Internal(Client(t))
  }

  predicate SharedCheckExcFree(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    r: R, flags_flags': R, r': R, t: int, fl: Flag)
  {
    && a == multiset{r, flags_flags'}
    && a' == multiset{r', flags_flags'}
    && r == Internal(SharedLockPending(key, t))
    && flags_flags' == Internal(FlagsField(key, fl))
    && r' == Internal(SharedLockPending2(key, t))
    && state' == state
    && (fl == Available || fl == WriteBack || fl == Reading)
  }

  predicate SharedCheckReading(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    r: R, flags_flags': R, r': R, handle': R, t: int, fl: Flag)
  {
    && a == multiset{r, flags_flags'}
    && a' == multiset{r', flags_flags', handle'}
    && r == Internal(SharedLockPending2(key, t))
    && flags_flags' == Internal(FlagsField(key, fl))
    && r' == Internal(SharedLockObtained(key, t))
    && (state.handle.Some? ==>
        handle' == Const(state.handle.value))
    && state' == state
    && fl != Reading && fl != Reading_ExcLock
  }

  predicate Unmap(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, handle: R, flags': R, fl: Flag, clean: bool)
  {
    && a == multiset{flags, r, handle}
    && a' == multiset{flags'}
    && flags == Internal(FlagsField(key, fl))
    && handle.Exc? && handle.v.is_handle(key)
    && r == Internal(ExcLockObtained(key, -1, clean))
    && flags' == Internal(FlagsField(key, Unmapped))
    && state' == state
      .(unmapped := true)
      .(excState := WLSNone)
      .(handle := Some(handle.v))
  }

  predicate AbandonExcLockPending(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, handle: R, flags': R, fl: Flag, visited: int, clean: bool)
  {
    && a == multiset{flags, handle, r}
    && a' == multiset{flags'}
    && r == Internal(ExcLockPending(key, -1, visited, clean))
    && flags == Internal(FlagsField(key, fl))
    && flags' == Internal(FlagsField(key, Available))
    && handle.Const? && handle.v.is_handle(key)

    && state' == state.(excState := WLSNone)
  }

  predicate AbandonReadingPending(
    key: Key, state: RWLockState, state': RWLockState,
    a: multiset<R>, a': multiset<R>,
    flags: R, r: R, handle: R, flags': R, fl: Flag)
  {
    && a == multiset{flags, handle, r}
    && a' == multiset{flags'}
    && r == Internal(ReadingPending(key))
    && flags == Internal(FlagsField(key, fl))
    && flags' == Internal(FlagsField(key, Unmapped))
    && handle.Const? && handle.v.is_handle(key)

    && state' == state.(readState := RSNone)
  }

  datatype QStep =
    | BasicStep(
        a: multiset<R>, a': multiset<R>,
        g: map<Key, RWLockState>,
        key: Key, state: RWLockState, state': RWLockState,
        basicStep: BasicStep)

  predicate step_common(a: multiset<R>, a': multiset<R>, step: QStep)
  {
    && a == multiset{Internal(Global(step.g))} + step.a
    && a' == multiset{
        Internal(Global(step.g[step.key := step.state']))} + step.a'
    && step.key in step.g
    && step.g[step.key] == step.state
  }

  predicate transform_step(a: multiset<R>, a': multiset<R>, step: QStep)
  {
    && step_common(a, a', step)
    && match step.basicStep {
      case TakeWriteBackStep(flags, flags', r', handle') =>
        && TakeWriteBack(step.key, step.state, step.state',
            step.a, step.a',
            flags, flags', r', handle')
      case ReleaseWriteBackStep(flags, r, handle, flags', fl) =>
        && ReleaseWriteBack(step.key, step.state, step.state',
            step.a, step.a',
            flags, r, handle, flags', fl)
      case ThreadlessExcStep(flags, flags', r', handle', fl) =>
        && ThreadlessExc(step.key, step.state, step.state',
            step.a, step.a',
            flags, flags', r', handle', fl)
      case SharedToExcStep(flags, r, flags', r', t, fl) =>
        && SharedToExc(step.key, step.state, step.state',
            step.a, step.a',
            flags, r, flags', r', t, fl)
      case TakeExcLockFinishWriteBackStep(flags, r, flags', r', t, fl, clean) =>
        && TakeExcLockFinishWriteBack(step.key, step.state, step.state',
            step.a, step.a',
            flags, r, flags', r', t, fl, clean)
      case TakeExcLockSharedLockZeroStep(rc_rc', r, r', t, idx, clean) =>
        && TakeExcLockSharedLockZero(step.key, step.state, step.state', 
            step.a, step.a',
            rc_rc', r, r', t, idx, clean)
      case TakeExcLockFinishStep(r, handle, r', handle', t, clean) =>
        && TakeExcLockFinish(step.key, step.state, step.state',
            step.a, step.a',
            r, handle, r', handle', t, clean)
      case DowngradeExcLockStep(r, handle, flags, r', handle', flags', fl, t, clean) =>
        && DowngradeExcLock(step.key, step.state, step.state',
            step.a, step.a',
            r, handle, flags, r', handle', flags', fl, t, clean)
      case AllocStep(flags, flags', r', handle') =>
        && Alloc(step.key, step.state, step.state', step.a, step.a',
            flags, flags', r', handle')
      case ReadingIncCountStep(client, rc, r, rc', r', t, refcount) =>
        && ReadingIncCount(step.key, step.state, step.state', step.a, step.a',
            client, rc, r, rc', r', t, refcount)
      case ObtainReadingStep(flags, r, flags', r', t, fl) =>
        && ObtainReading(step.key, step.state, step.state', step.a, step.a',
            flags, r, flags', r', t, fl)
      case ReadingToSharedStep(flags, r, handle, flags', r', handle', t, fl) =>
        && ReadingToShared(step.key, step.state, step.state', step.a, step.a',
            flags, r, handle, flags', r', handle', t, fl)
      case SharedIncCountStep(client, rc, rc', r', t, refcount) =>
        && SharedIncCount(step.key, step.state, step.state', step.a, step.a',
            client, rc, rc', r', t, refcount)
      case SharedDecCountPendingStep(rc, r, rc', client', t, refcount) =>
        && SharedDecCountPending(step.key, step.state, step.state', step.a, step.a',
            rc, r, rc', client', t, refcount)
      case SharedDecCountObtainedStep(rc, r, handle, rc', client', t, refcount) =>
        && SharedDecCountObtained(step.key, step.state, step.state', step.a, step.a',
            rc, r, handle, rc', client', t, refcount)
      case SharedCheckExcFreeStep(r, flags_flags', r', t, fl) =>
        && SharedCheckExcFree(step.key, step.state, step.state', step.a, step.a',
            r, flags_flags', r', t, fl)
      case SharedCheckReadingStep(r, flags_flags', r', handle', t, fl) =>
        && SharedCheckReading(step.key, step.state, step.state', step.a, step.a',
            r, flags_flags', r', handle', t, fl)
      case UnmapStep(flags, r, handle, flags', fl, clean) =>
        && Unmap(step.key, step.state, step.state', step.a, step.a',
            flags, r, handle, flags', fl, clean)
      case AbandonExcLockPendingStep(flags, r, handle, flags', fl, visited, clean) =>
        && AbandonExcLockPending(step.key, step.state, step.state', step.a, step.a',
            flags, r, handle, flags', fl, visited, clean)
      case AbandonReadingPendingStep(flags, r, handle, flags', fl) =>
        && AbandonReadingPending(step.key, step.state, step.state', step.a, step.a',
            flags, r, handle, flags', fl)
    }
  }

  predicate InvRWLockState(key: Key, state: RWLockState, m: multiset<R>)
  {
    && |state.readCounts| == NUM_THREADS
    && (state.excState.WLSPendingAwaitWriteBack? ==>
        && state.readState == RSNone
        && !state.unmapped
        && -1 <= state.excState.t < NUM_THREADS
      )
    && (state.excState.WLSPending? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      && 0 <= state.excState.visited <= NUM_THREADS
      //&& (forall i | 0 <= i < state.excState.visited
      //    && i != state.excState.t :: state.readCounts[i] == 0)
      //&& (0 <= state.excState.t < state.excState.visited ==>
      //      state.readCounts[state.excState.t] == 1)
      && -1 <= state.excState.t < NUM_THREADS
    )
    && (state.excState.WLSObtained? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      //&& (forall i | 0 <= i < |state.readCounts|
      //    && i != state.excState.t :: state.readCounts[i] == 0)
      //&& (0 <= state.excState.t < |state.readCounts| ==>
      //      state.readCounts[state.excState.t] == 1)
      && -1 <= state.excState.t < NUM_THREADS
    )
    && (state.backHeld ==>
      && state.readState == RSNone
    )
    && (state.readState.RSPending? ==>
      && !state.unmapped
      && !state.backHeld
      //&& (forall i | 0 <= i < |state.readCounts|
      //    :: state.readCounts[i] == 0)
    )
    && (state.readState.RSPendingCounted? ==>
      && !state.unmapped
      && !state.backHeld
      && 0 <= state.readState.t < NUM_THREADS
      //&& (forall i | 0 <= i < |state.readCounts| && i != state.readState.t
      //    :: state.readCounts[i] == 0)
      //&& state.readCounts[state.readState.t] == 1
    )
    && (state.readState.RSObtained? ==>
      0 <= state.readState.t < NUM_THREADS
    )
    && (state.unmapped ==>
      && !state.backHeld
      && state.readState == RSNone
      //&& (forall i | 0 <= i < |state.readCounts|
      //    :: state.readCounts[i] == 0)
    )
    && (state.excState.WLSObtained? ==> state.handle.None?)
    && (!state.readState.RSNone? ==> state.handle.None?)
    && (!state.excState.WLSObtained? && state.readState.RSNone?
        ==> state.handle.Some?)
    && (state.handle.Some? ==>
      state.handle.value.is_handle(key)
    )
    && (forall i | 0 <= i < |state.readCounts|
      :: state.readCounts[i] == CountCountedRefs(m, key, i))
  }

  predicate is_counted_ref_type(r: R)
  {
    && r.Internal?
    && (r.q.SharedLockPending? || r.q.SharedLockPending2?
        || r.q.SharedLockObtained?
        || r.q.ExcLockPendingAwaitWriteBack?
        || r.q.ExcLockPending?
        || r.q.ExcLockObtained?
        || r.q.ReadingPendingCounted?
        || r.q.ReadingObtained?)
  }

  predicate is_counted_ref(r: R, key: Key, t: int)
  {
    && is_counted_ref_type(r)
    && r.q.key == key
    && r.q.t == t
  }

  function CountCountedRefs(m: multiset<R>, key: Key, i: int) : nat
  {
    MultisetUtil.Count((r) => is_counted_ref(r, key, i), m)
  }

  predicate is_const_ref(r: R, key: Key)
  {
    && r.Internal?
    && (r.q.SharedLockObtained? || r.q.WriteBackObtained?
      || r.q.ExcLockPendingAwaitWriteBack? || r.q.ExcLockPending?)
    && r.q.key == key
  }

  function CountConstRefs(m: multiset<R>, key: Key) : nat
  {
    MultisetUtil.Count((r) => is_const_ref(r, key), m)
  }

  predicate is_const(r: R, key: Key)
  {
    && r.Const?
    && r.v.key == key
  }

  function CountConsts(m: multiset<R>, key: Key) : nat
  {
    MultisetUtil.Count((r) => is_const(r, key), m)
  }

  predicate is_thread_owned(r: R, t: int)
  {
    && r.Internal?
    && (r.q.Client? || r.q.SharedLockPending? || r.q.SharedLockPending2? ||
        r.q.SharedLockObtained? || r.q.ExcLockPendingAwaitWriteBack? ||
        r.q.ExcLockPending? || r.q.ExcLockObtained? ||
        r.q.ReadingPendingCounted? || r.q.ReadingObtained?)
    && r.q.t == t
  }

  function CountThreadOwned(m: multiset<R>, t: int) : nat
  {
    MultisetUtil.Count((r) => is_thread_owned(r, t), m)
  }

  predicate InvGlobal(g: map<Key, RWLockState>, m: multiset<R>)
  {
    && (forall key | key in g :: InvRWLockState(key, g[key], m))
  }

  predicate InvObjectState(key: Key, q: Q, state: RWLockState)
  {
    && |state.readCounts| == NUM_THREADS
    && (q.FlagsField? ==>
      && (q.flags == Unmapped ==>
        && state.unmapped
      )
      && (q.flags == Reading ==>
        && state.readState.RSObtained?
      )
      && (q.flags == Reading_ExcLock ==>
        && (state.readState.RSPending?
          || state.readState.RSPendingCounted?)
      )
      && (q.flags == Available ==>
        && state.excState == WLSNone
        && state.readState == RSNone
        && !state.backHeld
        && !state.unmapped
      )
      && (q.flags == WriteBack ==>
        && state.excState == WLSNone
        && state.readState == RSNone
        && state.backHeld
        && !state.unmapped
      )
      && (q.flags == ExcLock_Clean ==>
        && (state.excState.WLSPending? || state.excState.WLSObtained?)
        && state.excState.clean
      )
      && (q.flags == ExcLock_Dirty ==>
        && (state.excState.WLSPending? || state.excState.WLSObtained?)
        && !state.excState.clean
      )
      && (q.flags == WriteBack_PendingExcLock ==>
        && state.excState.WLSPendingAwaitWriteBack?
        && state.backHeld
      )
      && (q.flags == PendingExcLock ==>
        && state.excState.WLSPendingAwaitWriteBack?
        && !state.backHeld
      )
    )
    && (q.SharedLockRefCount? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readCounts[q.t] == q.refcount as int
    )

    && (q.SharedLockPending? ==>
      && 0 <= q.t < NUM_THREADS
    )
    && (q.SharedLockPending2? ==>
      && 0 <= q.t < NUM_THREADS
      && (state.excState == WLSNone || state.excState.WLSPendingAwaitWriteBack?
          || (state.excState.WLSPending? && state.excState.visited <= q.t))
      && (state.readState == RSNone || state.readState.RSObtained?)
      && !state.unmapped
    )
    && (q.SharedLockObtained? ==>
      && 0 <= q.t < NUM_THREADS
      && (state.excState == WLSNone || state.excState.WLSPendingAwaitWriteBack?
          || (state.excState.WLSPending? && state.excState.visited <= q.t))
      && state.readState == RSNone
      && !state.unmapped
    )

    && (q.ExcLockPendingAwaitWriteBack? ==>
      && -1 <= q.t < NUM_THREADS
      && state.excState == WLSPendingAwaitWriteBack(q.t)
    )
    && (q.ExcLockPending? ==>
      && -1 <= q.t < NUM_THREADS
      && state.excState == WLSPending(q.t, q.visited, q.clean)
    )
    && (q.ExcLockObtained? ==>
      && -1 <= q.t < NUM_THREADS
      && state.excState == WLSObtained(q.t, q.clean)
    )

    && (q.ReadingPending? ==>
      && state.readState.RSPending?
    )
    && (q.ReadingPendingCounted? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readState == RSPendingCounted(q.t)
    )
    && (q.ReadingObtained? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readState == RSObtained(q.t)
    )

    && (q.WriteBackObtained? ==>
      && state.backHeld
    )
  }

  predicate InvObject(r: R, g: map<Key, RWLockState>)
  {
    && (r.Internal? ==> (
      && !r.q.Global?
      && (!r.q.Client? ==>
        && r.q.key in g
        && InvObjectState(r.q.key, r.q, g[r.q.key])
      )
    ))
    && (r.Const? ==> (
      && r.v.key in g
      && g[r.v.key].handle == Some(r.v)
    ))
  }

  predicate Inv2(q: R, r: R)
  {
    && (q.Internal? ==> (
      && (r.Internal? ==> (
        && !(q.q.Global? && r.q.Global?)
        && (q.q.FlagsField? && r.q.FlagsField? ==> q.q.key != r.q.key)
        && (q.q.SharedLockRefCount? && r.q.SharedLockRefCount? ==> !(q.q.key == r.q.key && q.q.t == r.q.t))
        && (q.q.WriteBackObtained? && r.q.WriteBackObtained? ==> q.q.key != r.q.key)
        && (q.q.ExcLockPendingAwaitWriteBack? && r.q.ExcLockPendingAwaitWriteBack? ==> q.q.key != r.q.key)
        && (q.q.ExcLockPending? && r.q.ExcLockPending? ==> q.q.key != r.q.key)
        && (q.q.ExcLockObtained? && r.q.ExcLockObtained? ==> q.q.key != r.q.key)
        && (q.q.ReadingPending? && r.q.ReadingPending? ==> q.q.key != r.q.key)
        && (q.q.ReadingPendingCounted? && r.q.ReadingPendingCounted? ==> q.q.key != r.q.key)
        && (q.q.ReadingObtained? && r.q.ReadingObtained? ==> q.q.key != r.q.key)
      ))
      && (q.q.Global? ==> (
        && InvObject(r, q.q.g)
      ))
    ))
  }
  
  const NUM_CLIENTS := 255;

  predicate Inv(s: Variables)
  {
    && (forall g | g in s.m :: g.Internal? && g.q.Global? ==> InvGlobal(g.q.g, s.m))
    && (forall a, b | multiset{a,b} <= s.m :: Inv2(a, b))
    && (forall key :: CountConsts(s.m, key) == CountConstRefs(s.m, key))
    && (forall t | 0 <= t < NUM_THREADS :: CountThreadOwned(s.m, t) == NUM_CLIENTS)
  }

  lemma forall_CountReduce<A>()
  ensures forall fn: A->bool, a, b {:trigger Count<A>(fn, a + b) }
    :: Count<A>(fn, a + b) == Count<A>(fn, a) + Count<A>(fn, b)
  ensures forall fn: A->bool, a {:trigger Count<A>(fn, multiset{a}) }
    :: Count<A>(fn, multiset{a}) == (if fn(a) then 1 else 0)
  ensures forall fn: A->bool, a, b {:trigger Count<A>(fn, multiset{a,b}) }
    :: Count<A>(fn, multiset{a,b}) ==
        (if fn(a) then 1 else 0) + (if fn(b) then 1 else 0)
  ensures forall fn: A->bool, a, b, c {:trigger Count<A>(fn, multiset{a,b, c}) }
    :: Count<A>(fn, multiset{a,b,c}) ==
        (if fn(a) then 1 else 0) + (if fn(b) then 1 else 0) + (if fn(c) then 1 else 0)

  // Relevant assertions to trigger all relevant Inv2(x, y) expressions
  lemma UsefulTriggers(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  ensures forall x, y //{:trigger a[x], rest[y]}
        | x in a && y in rest :: Inv2(x, y) && Inv2(y, x);
  ensures forall x, y //{:trigger a[x], a[y]}
        | x in a && y in a && x != y ::
        Inv2(x, y) && Inv2(y, x);
  ensures forall x | x in step.a :: x in a;
  ensures Internal(Global(step.g)) in a;
  {
  }

  lemma TakeWriteBackStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  //requires step_common(a, a', step)
  requires step.basicStep.TakeWriteBackStep?
  /*requires TakeWriteBack(step.key, step.state, step.state',
        step.a, step.a',
        step.basicStep.flags, step.basicStep.flags',
        step.basicStep.r', step.basicStep.handle')*/
  requires transform_step(a, a', step)
  requires Inv(s)
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    //assert step.state.handle.Some?;

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma ReleaseWriteBackStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.ReleaseWriteBackStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall g | g in s'.m && g.Internal? && g.q.Global?
    ensures InvGlobal(g.q.g, s'.m)
    {
    }

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma ThreadlessExcStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.ThreadlessExcStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma SharedToExcStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedToExcStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }


  lemma TakeExcLockFinishWriteBackStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.TakeExcLockFinishWriteBackStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma TakeExcLockSharedLockZeroStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.TakeExcLockSharedLockZeroStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        if p.Internal? && (p.q.SharedLockPending2? || p.q.SharedLockObtained?) &&
            p.q.key == step.key && p.q.t == step.basicStep.idx {
          if step.basicStep.t == step.basicStep.idx {
            Count_ge_2((r) => is_counted_ref(r, p.q.key, p.q.t), s.m, p, step.basicStep.r);
            assert CountCountedRefs(s.m, p.q.key, p.q.t) >= 2;
            assert false;
          } else {
            Count_ge_1((r) => is_counted_ref(r, p.q.key, p.q.t), s.m, p);
            assert CountCountedRefs(s.m, p.q.key, p.q.t) >= 1;
            assert step.state.readCounts[p.q.t] >= 1;
            assert false;
          }
        }

        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma TakeExcLockFinishStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.TakeExcLockFinishStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        if p.Const? && p.v.key == step.key {
          // If a Const exists (one other than the one being turned into an Exc
          // by this step), then there is either
          // a SharedObtained or a WriteBackObtained object (etc.)
          // to certify it, and that would lead to a contradiction.
          Count_ge_1((r) => is_const(r, step.key), rest, p);
          assert CountConsts(s.m, step.key) >= 2;
          assert CountConsts(s.m, step.key)
              == CountConstRefs(s.m, step.key);
          //var o := get_true_elem((r) => is_const_ref(r, step.key), s.m);
          var o, o2 := get_2_true_elems((r) => is_const_ref(r, step.key), s.m);
          assert false;
        }

        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma DowngradeExcLockStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.DowngradeExcLockStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma AllocStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.AllocStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);

    assert step.state.handle.Some?;

    forall i | 0 <= i < |step.state'.readCounts|
    ensures step.state'.readCounts[i] == CountCountedRefs(s'.m, step.key, i)
    {
      assert step.state.readCounts[i] == CountCountedRefs(s.m, step.key, i);
      assert CountCountedRefs(s'.m, step.key, i)
          == CountCountedRefs(s.m, step.key, i);
      assert step.state'.readCounts[i]
          == step.state.readCounts[i];
    }

    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {

        if p.Const? && p.v.key == step.key {
          // If a Const exists, then there is either
          // a SharedLockObtained or a WriteBackObtained object
          // to certify it, and that would lead to a contradiction.
          Count_ge_1((r) => is_const(r, step.key), s.m, p);
          assert CountConsts(s.m, step.key)
              == CountConstRefs(s.m, step.key);
          var o := get_true_elem((r) => is_const_ref(r, step.key), s.m);
          assert false;
        }

        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma ReadingIncCountStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.ReadingIncCountStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
    calc {
      step.state'.readCounts[step.basicStep.t];
      CountCountedRefs(s'.m, step.key, step.basicStep.t);
      <= {
        CountSubset(
            (r) => is_counted_ref(r, step.key, step.basicStep.t),
            (r) => is_thread_owned(r, step.basicStep.t),
            s'.m);
      }
      CountThreadOwned(s'.m, step.basicStep.t);
    }
    assert step.state'.readCounts[step.basicStep.t] <= 255;

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }
  }

  lemma ObtainReadingStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.ObtainReadingStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma ReadingToSharedStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.ReadingToSharedStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma SharedIncCountStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedIncCountStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
    calc {
      step.state'.readCounts[step.basicStep.t];
      CountCountedRefs(s'.m, step.key, step.basicStep.t);
      <= {
        CountSubset(
            (r) => is_counted_ref(r, step.key, step.basicStep.t),
            (r) => is_thread_owned(r, step.basicStep.t),
            s'.m);
      }
      CountThreadOwned(s'.m, step.basicStep.t);
    }
    assert step.state'.readCounts[step.basicStep.t] <= 255;

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }
  }

  lemma SharedDecCountPendingStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedDecCountPendingStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma SharedDecCountObtainedStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedDecCountObtainedStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma SharedCheckExcFreeStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedCheckExcFreeStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma SharedCheckReadingStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.SharedCheckReadingStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma UnmapStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.UnmapStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma AbandonExcLockPendingStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.AbandonExcLockPendingStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma AbandonReadingPendingStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.AbandonReadingPendingStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);
    forall_CountReduce<R>();

    assert InvRWLockState(step.key, step.state, s.m);
    assert InvRWLockState(step.key, step.state', s'.m);

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }

    forall k
    ensures CountConsts(s'.m, k) == CountConstRefs(s'.m, k)
    {
      assert CountConsts(s.m, k) == CountConstRefs(s.m, k); // trigger
    }

    assert forall t | 0 <= t < NUM_THREADS :: 
        CountThreadOwned(s.m, t) == CountThreadOwned(s'.m, t);
  }

  lemma BasicStepPreservesInv(
      s: Variables, s': Variables, step: QStep,
      a: multiset<R>, a': multiset<R>, rest: multiset<R>)
  requires s'.saved == s.saved
  requires s.m == a + rest
  requires s'.m == a' + rest
  requires transform_step(a, a', step)
  requires Inv(s)
  ensures Inv(s')
  {
    match step.basicStep {
      case TakeWriteBackStep(_,_,_,_) => {
        TakeWriteBackStepPreservesInv(s, s', step, a, a', rest);
      }
      case ReleaseWriteBackStep(_,_,_,_,_) => {
        ReleaseWriteBackStepPreservesInv(s, s', step, a, a', rest);
      }
      case TakeExcLockFinishWriteBackStep(_,_,_,_,_,_,_) => {
         TakeExcLockFinishWriteBackStepPreservesInv(
            s, s', step, a, a', rest);
      }
      case TakeExcLockSharedLockZeroStep(_,_,_,_,_,_) => {
         TakeExcLockSharedLockZeroStepPreservesInv(
            s, s', step, a, a', rest);
      }
      case TakeExcLockFinishStep(_,_,_,_,_,_) => {
         TakeExcLockFinishStepPreservesInv(s, s', step, a, a', rest);
      }
      case AllocStep(_,_,_,_) => {
         AllocStepPreservesInv(s, s', step, a, a', rest);
      }
      case AbandonExcLockPendingStep(_,_,_,_,_,_,_) => {
        AbandonExcLockPendingStepPreservesInv(s, s', step, a, a', rest);
      }
      case AbandonReadingPendingStep(_,_,_,_,_) => {
        AbandonReadingPendingStepPreservesInv(s, s', step, a, a', rest);
      }
      case UnmapStep(_,_,_,_,_,_) => {
        UnmapStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedCheckReadingStep(_,_,_,_,_,_) => {
        SharedCheckReadingStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedCheckExcFreeStep(_,_,_,_,_) => {
        SharedCheckExcFreeStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedDecCountObtainedStep(_,_,_,_,_,_,_) => {
        SharedDecCountObtainedStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedDecCountPendingStep(_,_,_,_,_,_) => {
        SharedDecCountPendingStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedIncCountStep(_,_,_,_,_,_) => {
        SharedIncCountStepPreservesInv(s, s', step, a, a', rest);
      }
      case ReadingToSharedStep(_,_,_,_,_,_,_,_) => {
        ReadingToSharedStepPreservesInv(s, s', step, a, a', rest);
      }
      case ObtainReadingStep(_,_,_,_,_,_) => {
        ObtainReadingStepPreservesInv(s, s', step, a, a', rest);
      }
      case ReadingIncCountStep(_,_,_,_,_,_,_) => {
        ReadingIncCountStepPreservesInv(s, s', step, a, a', rest);
      }
      case SharedToExcStep(_,_,_,_,_,_) => {
        SharedToExcStepPreservesInv(s, s', step, a, a', rest);
      }
      case ThreadlessExcStep(_,_,_,_,_) => {
        ThreadlessExcStepPreservesInv(s, s', step, a, a', rest);
      }
      case DowngradeExcLockStep(_,_,_,_,_,_,_,_,_) => {
        DowngradeExcLockStepPreservesInv(s, s', step, a, a', rest);
      }
    }
  }
}
