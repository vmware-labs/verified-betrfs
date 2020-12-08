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
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.TakeWriteBackStep?
  ensures Inv(s')
  {
    UsefulTriggers(s, s', step, a, a', rest);

    assert InvRWLockState(step.state);
    assert InvRWLockState(step.state');

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

    assert InvRWLockState(step.state);
    assert InvRWLockState(step.state');

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
      case TakeWriteBackStep(_,_,_) => {
        TakeWriteBackStepPreservesInv(s, s', step, a, a', rest);
      }
      case ReleaseWriteBackStep(_,_,_,_) => {
        ReleaseWriteBackStepPreservesInv(s, s', step, a, a', rest);
      }
    }
  }
}
