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
    | ExcLock
    | WriteBack_PendingExcLock

  datatype ExcLockLockState = 
    | WLSNone
    | WLSPendingAwaitWriteBack
    | WLSPending(visited: int)
    | WLSObtained

  datatype RWLockState = RWLockState(
    writeLock: ExcLockLockState,
    backHeld: bool,
    readCounts: seq<int>)

  datatype Q =
    | Global(g: map<Key, RWLockState>)
    | FlagsField(key: Key, flags: Flag)
    | SharedLockRefCount(key: Key, t: int, refcount: uint8)

    // Standard flow for obtaining a 'shared' lock

    | SharedLockPending(key: Key, t: int)     // inc refcount
    | SharedLockObtained(key: Key, t: int)    // check status bit

    // Standard flow for obtaining an 'exclusive' lock

    | ExcLockPendingAwaitWriteBack(key: Key)  // set ExcLock bit
    | ExcLockPending(key: Key, visited: int)  // check WriteBack bit unset
                                              //   and `visited` of the
                                              //   refcounts
    | ExcLockObtained(key: Key)

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


  /*datatype QStep =
    | TakeWriteBackStep(key: Key)
    | TakeExcLock(key: Key)
    | TakeExcLockAwaitWriteBack(key: Key)*/

  predicate TakeWriteBack(a: multiset<R>, b: multiset<R>, key: Key,
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
  }

  predicate TakeExcLock(a: multiset<Q>, b: multiset<Q>, key: Key)
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
  }

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
  }

  predicate InvRWLockState(state: RWLockState)
  {
    && |state.readCounts| == NUM_THREADS
    && (state.writeLock != WLSNone ==>
      && !state.backHeld
      && (forall i | 0 <= i < |state.readCounts| :: state.readCounts[i] == 0)
    )
    && (state.writeLock.WLSPending? ==>
        0 <= state.writeLock.visited < NUM_THREADS)
  }

  predicate InvGlobal(g: map<Key, RWLockState>)
  {
    forall key | key in g :: InvRWLockState(g[key])
  }

  predicate InvObjectState(q: Q, state: RWLockState)
  {
    && InvRWLockState(state)
    && (q.FlagsField? ==>
      && (q.flags == Available ==> state.writeLock == WLSNone && !state.backHeld)
      && (q.flags == WriteBack ==> state.writeLock == WLSNone && state.backHeld)
      && (q.flags == ExcLock ==> state.writeLock != WLSNone && !state.backHeld)
      && (q.flags == WriteBack_PendingExcLock ==>
          state.writeLock == WLSPendingAwaitWriteBack && state.backHeld)
    )
    && (q.SharedLockRefCount? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readCounts[q.t] == q.refcount as int
    )
    && (q.WriteBackObtained? ==>
      state.backHeld
    )
    && (q.ExcLockPendingAwaitWriteBack? ==>
      state.writeLock == WLSPendingAwaitWriteBack
    )
    && (q.ExcLockPending? ==>
      state.writeLock == WLSPending(q.visited)
    )
    && (q.ExcLockObtained? ==>
      state.writeLock == WLSObtained
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

  lemma TakeWriteBackPreservesInv(
    s: Variables, s': Variables,
    a: multiset<R>, b: multiset<R>, c: multiset<R>,
    key: Key, g: map<Key, RWLockState>, g': map<Key, RWLockState>)
  requires TakeWriteBack(a, b, key, g, g')
  requires Inv(s)
  requires s.m == a + c
  requires s'.m == b + c
  requires s'.saved == s.saved
  ensures Inv(s')
  {
    var y := b + c;
    forall q, r | multiset{q, r} <= y
    ensures Inv2(q, r)
    {
      if multiset{q, r} <= c {
        assert Inv2(q, r);
      } else if q in b && r in c {
        assert Inv2(Internal(Global(g)), r);
        assert Inv2(Internal(FlagsField(key, Available)), r);
        assert Inv2(q, r);
      } else if q in c && r in b {
        assert Inv2(q, Internal(Global(g)));
        assert Inv2(q, Internal(FlagsField(key, Available)));
        assert Inv2(q, r);
      } else if multiset{q, r} <= b {
        assert Inv2(q, r);
      }
    }
    assert Inv(s');
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
  ensures fl == WriteBack_PendingExcLock ==> s == Internal(FlagsField(key, ExcLock))

  method transform_TakeExcLock(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, Available))
  ensures t == Internal(FlagsField(key, ExcLock))
  ensures u == Internal(ExcLockPendingAwaitWriteBack(key))

  method transform_TakeExcLockAwaitWriteBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, WriteBack))
  ensures t == Internal(FlagsField(key, WriteBack_PendingExcLock))
  ensures u == Internal(ExcLockPendingAwaitWriteBack(key))

  method transform_TakeExcLockFinishWriteBack(key: Key, fl: Flag, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires fl == ExcLock || fl == Available
      // vacuous cases:
      || fl == Reading || fl == Reading_ExcLock || fl == Unmapped
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(ExcLockPendingAwaitWriteBack(key))
  ensures t1 == Internal(FlagsField(key, fl))
  ensures t2 == Internal(ExcLockPending(key, 0))

  method transform_TakeExcLockCheckSharedLockZero(key: Key, idx: int, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == Internal(SharedLockRefCount(key, idx, 0))
  requires s2 == Internal(ExcLockPending(key, idx))
  ensures t1 == Internal(SharedLockRefCount(key, idx, 0))
  ensures t2 == Internal(ExcLockPending(key, idx + 1))

  method transform_TakeExcLockFinish(key: Key, linear s1: R)
  returns (linear t1: R, linear t2: Handle)
  requires s1 == Internal(ExcLockPending(key, NUM_THREADS))
  ensures t1 == Internal(ExcLockObtained(key))
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

}
