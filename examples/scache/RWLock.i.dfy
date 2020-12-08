include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Constants.i.dfy"
include "ResourceBuilderSpec.s.dfy"
include "CacheResources.i.dfy"

module RWLock refines ResourceBuilderSpec {
  import Ptrs
  import CacheResources
  import opened NativeTypes
  import opened Constants
  import opened Options

  datatype Key = Key(data_ptr: Ptrs.Ptr, idx_ptr: Ptrs.Ptr, cache_idx: int)

  linear datatype Handle = CacheEntryHandle(
      linear cache_entry: CacheResources.R,
      linear data: Ptrs.ArrayDeref<byte>,
      linear idx: Ptrs.Deref<int>
  )
  {
    predicate is_handle(key: Key)
    {
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

  datatype ExcLockLockState = 
    | WLSNone
    | WLSPendingAwaitWriteBack
    | WLSPending(t: int, visited: int, clean: bool)
    | WLSObtained(t: int, clean: bool)

  datatype ReadState =
    | RSNone
    | RSPending
    | RSPendingCounted(t: int)
    | RSObtained(t: int)

  datatype RWLockState = RWLockState(
    writeLock: ExcLockLockState,
    readState: ReadState,
    unmapped: bool,
    backHeld: bool,
    readCounts: seq<int>)

  datatype Q =
    | Global(g: map<Key, RWLockState>)
    | FlagsField(key: Key, flags: Flag)
    | SharedLockRefCount(key: Key, t: int, refcount: uint8)

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
    | TakeWriteBackStep(flags: R, flags': R, r': R)
    | ReleaseWriteBackStep(flags: R, r: R, flags': R, fl: Flag)

  predicate TakeWriteBack(
    key: Key,
    state: RWLockState,
    state': RWLockState,
    flags: R,
    flags': R,
    r': R)
  {
    && state' == state.(backHeld := true)
    && flags == Internal(FlagsField(key, Available))
    && flags' == Internal(FlagsField(key, WriteBack))
    && r' == Internal(WriteBackObtained(key))
  }

  predicate ReleaseWriteBack(
    key: Key,
    state: RWLockState,
    state': RWLockState,
    flags: R,
    r: R,
    flags': R,
    fl: Flag)
  {
    && state' == state.(backHeld := false)
    && flags == Internal(FlagsField(key, fl))
    && r == Internal(WriteBackObtained(key))
    && (fl == WriteBack ==>
        flags' == Internal(FlagsField(key, Available)))
    && (fl == WriteBack_PendingExcLock ==>
        flags' == Internal(FlagsField(key, PendingExcLock)))
  }

  datatype QStep =
    | BasicStep(
        a: multiset<R>, a': multiset<R>,
        g: map<Key, RWLockState>,
        key: Key, state: RWLockState, state': RWLockState,
        basicStep: BasicStep)


  predicate transform_step(a: multiset<R>, a': multiset<R>, step: QStep)
  {
    && a == multiset{Internal(Global(step.g))} + step.a
    && a' == multiset{
        Internal(Global(step.g[step.key := step.state']))} + step.a'
    && step.key in step.g
    && step.g[step.key] == step.state
    && match step.basicStep {
      case TakeWriteBackStep(flags, flags', r') =>
        && step.a == multiset{flags}
        && step.a' == multiset{flags', r'}
        && TakeWriteBack(step.key, step.state, step.state',
            flags, flags', r')
      case ReleaseWriteBackStep(flags, r, flags', fl) =>
        && step.a == multiset{flags, r}
        && step.a' == multiset{flags'}
        && ReleaseWriteBack(step.key, step.state, step.state',
            flags, r, flags', fl)
    }
  }

  /*predicate TakeWriteBack(a: multiset<R>, b: multiset<R>, key: Key,
      g: map<Key, RWLockState>, g': map<Key, RWLockState>)
  {
    && key in g
    && key in g'
    && g' == g[key := g'[key]]
    && g'[key] == g[key].(backHeld := true)
    && a == multiset{
      Internal(Global(g)),
      Internal(FlagsField(key, Available))
    }
    && b == multiset{
      Internal(Global(g')),
      Internal(FlagsField(key, WriteBack)),
      Internal(WriteBackObtained(key))
    }
  }*/

  /*predicate TakeExcLock(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{ FlagsField(key, Available) }
    && b == multiset{
      FlagsField(key, ExcLock),
      ExcLockPendingAwaitWriteBack(key)
    }
  }

  predicate TakeExcLockAwaitWriteBack(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{ FlagsField(key, WriteBack) }
    && b == multiset{
      FlagsField(key, WriteBack_PendingExcLock),
      ExcLockPendingAwaitWriteBack(key)
    }
  }

  predicate TakeExcLockFinishWriteBack(a: multiset<Q>, b: multiset<Q>, key: Key, fl: Flag)
  {
    // The 'free' case cannot actually occur, but it's convenient to allow it.
    && (fl == ExcLock || fl == Available)
    && a == multiset{
      FlagsField(key, fl),
      ExcLockPendingAwaitWriteBack(key)
    }
    && b == multiset{
      FlagsField(key, fl),
      ExcLockPending(key, 0)
    }
  }

  predicate TakeExcLockCheckSharedLockZero(a: multiset<Q>, b: multiset<Q>, key: Key, idx: int)
  {
    && a == multiset{
      ExcLockPending(key, idx),
      SharedLockRefCount(key, idx, 0) 
    }
    && b == multiset{
      ExcLockPending(key, idx + 1),
      SharedLockRefCount(key, idx, 0) 
    }
  }

  predicate TakeExcLockFinish(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{
      ExcLockPending(key, NUM_THREADS)
    }
    && b == multiset{
      ExcLockObtained(key)
    }
  }*/

  /*
  predicate TakeSharedLock(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      SharedLockRefCount(key, t, r)
    }
    && a == multiset{
      SharedLockRefCount(key, t, if r == 255 then 0 else r+1),
      SharedLockPending(key, t)
    }
  }

  predicate TakeSharedLockFinish(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8, fl: Flag)
  {
    && (fl == Available || fl == WriteBack)
    && a == multiset{
      SharedLockPending(key, t),
      FlagsField(key, fl)
    }
    && a == multiset{
      SharedLockObtained(key, t)
    }
  }

  predicate TakeSharedLockBail(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      SharedLockRefCount(key, t, r),
      SharedLockPending(key, t)
    }
    && b == multiset{
      SharedLockRefCount(key, t, if r == 0 then 255 else r-1)
    }
  }*/

  predicate InvRWLockState(state: RWLockState)
  {
    && |state.readCounts| == NUM_THREADS
    && (state.writeLock.WLSPendingAwaitWriteBack? ==>
        && state.readState == RSNone
        && !state.unmapped
      )
    && (state.writeLock.WLSPending? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      && 0 <= state.writeLock.visited < NUM_THREADS
      && (forall i | 0 <= i < state.writeLock.visited
          :: state.readCounts[i] == 0)
      && 0 <= state.writeLock.t < NUM_THREADS
    )
    && (state.writeLock.WLSObtained? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      && (forall i | 0 <= i < |state.readCounts|
          :: state.readCounts[i] == 0)
      && 0 <= state.writeLock.t < NUM_THREADS
    )
    && (state.backHeld ==>
      && state.readState == RSNone
    )
    && (
      (
        || state.readState == RSPending
        || state.readState.RSPendingCounted?
      ) ==> (
        && !state.unmapped
        && !state.backHeld
        && (forall i | 0 <= i < |state.readCounts|
            :: state.readCounts[i] == 0)
      )
    )
    && (state.readState.RSPendingCounted? ==>
      0 <= state.readState.t < NUM_THREADS
    )
    && (state.readState.RSObtained? ==>
      0 <= state.readState.t < NUM_THREADS
    )
    && (state.unmapped ==>
      && !state.backHeld
      && (forall i | 0 <= i < |state.readCounts|
          :: state.readCounts[i] == 0)
    )
  }

  predicate InvGlobal(g: map<Key, RWLockState>)
  {
    forall key | key in g :: InvRWLockState(g[key])
  }

  predicate InvObjectState(q: Q, state: RWLockState)
  {
    && InvRWLockState(state)
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
        && state.writeLock == WLSNone
        && state.readState == RSNone
        && !state.backHeld
        && !state.unmapped
      )
      && (q.flags == WriteBack ==>
        && state.writeLock == WLSNone
        && state.readState == RSNone
        && state.backHeld
        && !state.unmapped
      )
      && (q.flags == ExcLock_Clean ==>
        && (state.writeLock.WLSPending? || state.writeLock.WLSObtained?)
        && state.writeLock.clean
      )
      && (q.flags == ExcLock_Dirty ==>
        && (state.writeLock.WLSPending? || state.writeLock.WLSObtained?)
        && !state.writeLock.clean
      )
      && (q.flags == WriteBack_PendingExcLock ==>
        && state.writeLock == WLSPendingAwaitWriteBack
        && state.backHeld
      )
      && (q.flags == PendingExcLock ==>
        && state.writeLock == WLSPendingAwaitWriteBack
        && !state.backHeld
      )
    )
    && (q.SharedLockRefCount? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readCounts[q.t] == q.refcount as int
    )

    && (q.SharedLockPending2? ==>
      && state.writeLock == WLSNone
      && (state.readState == RSNone || state.readState.RSObtained?)
    )
    && (q.SharedLockObtained? ==>
      && state.writeLock == WLSNone
      && state.readState == RSNone
    )

    && (q.ExcLockPendingAwaitWriteBack? ==>
      && state.writeLock == WLSPendingAwaitWriteBack
    )
    && (q.ExcLockPending? ==>
      && state.writeLock == WLSPending(q.t, q.visited, q.clean)
    )
    && (q.ExcLockObtained? ==>
      && state.writeLock == WLSObtained(q.t, q.clean)
    )

    && (q.ReadingPending? ==>
      && state.readState.RSPending?
    )
    && (q.ReadingPendingCounted? ==>
      && state.readState == RSPendingCounted(q.t)
    )
    && (q.ReadingObtained? ==>
      && state.readState == RSObtained(q.t)
    )

    && (q.WriteBackObtained? ==>
      && state.backHeld
    )
  }

  predicate InvObject(q: R, g: map<Key, RWLockState>)
  {
    && q.Internal?
    && !q.q.Global?
    && q.q.key in g
    && InvObjectState(q.q, g[q.q.key])
  }

  predicate Inv2(q: R, r: R)
  {
    && q.Internal?
    && r.Internal?
    && !(q.q.Global? && r.q.Global?)
    && (q.q.FlagsField? && r.q.FlagsField? ==> q.q.key != r.q.key)
    && (q.q.SharedLockRefCount? && r.q.SharedLockRefCount? ==> !(q.q.key == r.q.key && q.q.t == r.q.t))
    && (q.q.WriteBackObtained? && r.q.WriteBackObtained? ==> q.q.key != r.q.key)
    && (q.q.ExcLockPendingAwaitWriteBack? && r.q.ExcLockPendingAwaitWriteBack? ==> q.q.key != r.q.key)
    && (q.q.ExcLockPending? && r.q.ExcLockPending? ==> q.q.key != r.q.key)
    && (q.q.ExcLockObtained? && r.q.ExcLockObtained? ==> q.q.key != r.q.key)
    && (q.q.Global? ==>
      && InvObject(r, q.q.g)
    )
  }

  predicate Inv(s: Variables)
  {
    && (forall g | g in s.m :: g.Internal? && g.q.Global? ==> InvGlobal(g.q.g))
    && (forall a, b | multiset{a,b} <= s.m :: Inv2(a, b))
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
    forall t | t in a && !(t.Internal? && t.q.Global?)
    ensures Inv2(Internal(Global(step.g)), t)
    {
    }
    forall t | t in rest && !(t.Internal? && t.q.Global?)
    ensures Inv2(Internal(Global(step.g)), t)
    {
    }

    assert InvRWLockState(step.state);

    assert InvRWLockState(step.state') by {
      forall t | t in a && !(t.Internal? && t.q.Global?)
      ensures Inv2(Internal(Global(step.g)), t)
      {
      }
    }

    forall q, p | multiset{q, p} <= s'.m
    ensures Inv2(q, p)
    {
      if multiset{q, p} <= rest {
        assert Inv2(q, p);
      } else if q in a' && p in rest {
        forall t | t in a
        ensures Inv2(t, p)
        ensures Inv2(p, t)
        {
        }
        match step.basicStep {
          case TakeWriteBackStep(flags, flags', r') => {
            assert Inv2(q, p);
          }
          case ReleaseWriteBackStep(flags, r, flags', fl) => {
            /*assert step.state.backHeld;
            assert fl != Unmapped;
            assert fl != Reading;
            assert fl != Reading_ExcLock;
            assert fl != Available;
            assert fl != ExcLock_Clean;
            assert fl != ExcLock_Dirty;
            assert fl != PendingExcLock;
            assert fl == WriteBack || fl == WriteBack_PendingExcLock;
            assert Internal(WriteBackObtained(step.key)) in step.a;
            assert Internal(WriteBackObtained(step.key)) in a;
            assert Inv2(Internal(WriteBackObtained(step.key)), p);
            assert !(p.Internal? && p.q.WriteBackObtained? &&
                p.q.key == step.key);*/
            assert Inv2(q, p);
          }
        }
        assert Inv2(q, p);
      } else if q in rest && p in a' {
        forall t | t in a
        ensures Inv2(t, q)
        ensures Inv2(q, t)
        {
        }
        assert Inv2(q, p);
      } else if multiset{q, p} <= a' {
        assert Inv2(q, p);
      }
    }
  }

  method transform_TakeWriteBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R, /*readonly*/ linear v: Handle)
  requires s == Internal(FlagsField(key, Available))
  ensures t == Internal(FlagsField(key, WriteBack))
  ensures u == Internal(WriteBackObtained(key))
  ensures v.is_handle(key)

  method pre_ReleaseWriteBack(key: Key, fl: Flag,
    shared t: R, shared u: R)
  requires t == Internal(FlagsField(key, fl))
  requires u == Internal(WriteBackObtained(key))
  ensures fl == WriteBack || fl == WriteBack_PendingExcLock

  method transform_ReleaseWriteBack(key: Key, fl: Flag,
    linear t: R, linear u: R, /*readonly*/ linear v: Handle)
  returns (linear s: R)
  requires t == Internal(FlagsField(key, fl))
  requires u == Internal(WriteBackObtained(key))
  requires v.is_handle(key)
  ensures fl == WriteBack || fl == WriteBack_PendingExcLock
  ensures fl == WriteBack ==> s == Internal(FlagsField(key, Available))
  ensures fl == WriteBack_PendingExcLock ==> s == Internal(FlagsField(key, PendingExcLock))

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
