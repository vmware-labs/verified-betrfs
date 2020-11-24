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
      && this.cache_entry.disk_idx_opt ==
          (if this.idx.v == -1 then None else Some(this.idx.v))
    }
  }

  type V = Handle

  /*
   * We consider two bits of the status field, WriteLock and WriteBack.
   * To avoid confusion, I simply call them 'Write' and 'Back'.
   *
   * Write and Back. Of course, 'Write'
   * and 'Back' should be exclusive operations;
   * When both flags are set,
   * it should be interpreted as the 'Write' being
   * pending, with the 'Back' being in progress.
   */
  datatype Flag =
    | Free
    | Back
    | Write
    | Back_PendingWrite

  datatype WriteLockState = 
    | WLSNone
    | WLSPendingAwaitBack
    | WLSPending(visited: int)
    | WLSObtained

  datatype RWLockState = RWLockState(
    writeLock: WriteLockState,
    backHeld: bool,
    readCounts: seq<int>)

  datatype Q =
    | Global(g: map<Key, RWLockState>)
    | FlagsField(key: Key, flags: Flag)
    | ReadRefCount(key: Key, t: int, refcount: uint8)

    | ReadPending(key: Key, t: int)
    | ReadObtained(key: Key, t: int)
    
    | BackObtained(key: Key)

    | WritePendingAwaitBack(key: Key)
    | WritePending(key: Key, visited: int)
    | WriteObtained(key: Key)

  /*datatype QStep =
    | TakeBackStep(key: Key)
    | TakeWrite(key: Key)
    | TakeWriteAwaitBack(key: Key)*/

  predicate TakeBack(a: multiset<R>, b: multiset<R>, key: Key,
      g: map<Key, RWLockState>, g': map<Key, RWLockState>)
  {
    && key in g
    && key in g'
    && g' == g[key := g'[key]]
    && g'[key] == g[key].(backHeld := true)
    && a == multiset{
      Internal(Global(g)),
      Internal(FlagsField(key, Free))
    }
    && b == multiset{
      Internal(Global(g')),
      Internal(FlagsField(key, Back)),
      Internal(BackObtained(key))
    }
  }

  predicate TakeWrite(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{ FlagsField(key, Free) }
    && b == multiset{
      FlagsField(key, Write),
      WritePendingAwaitBack(key)
    }
  }

  predicate TakeWriteAwaitBack(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{ FlagsField(key, Back) }
    && b == multiset{
      FlagsField(key, Back_PendingWrite),
      WritePendingAwaitBack(key)
    }
  }

  predicate TakeWriteFinishBack(a: multiset<Q>, b: multiset<Q>, key: Key, fl: Flag)
  {
    // The 'free' case cannot actually occur, but it's convenient to allow it.
    && (fl == Write || fl == Free)
    && a == multiset{
      FlagsField(key, fl),
      WritePendingAwaitBack(key)
    }
    && b == multiset{
      FlagsField(key, fl),
      WritePending(key, 0)
    }
  }

  predicate TakeWriteCheckReadZero(a: multiset<Q>, b: multiset<Q>, key: Key, idx: int)
  {
    && a == multiset{
      WritePending(key, idx),
      ReadRefCount(key, idx, 0) 
    }
    && b == multiset{
      WritePending(key, idx + 1),
      ReadRefCount(key, idx, 0) 
    }
  }

  predicate TakeWriteFinish(a: multiset<Q>, b: multiset<Q>, key: Key)
  {
    && a == multiset{
      WritePending(key, NUM_THREADS)
    }
    && b == multiset{
      WriteObtained(key)
    }
  }

  predicate TakeRead(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(key, t, r)
    }
    && a == multiset{
      ReadRefCount(key, t, if r == 255 then 0 else r+1),
      ReadPending(key, t)
    }
  }

  predicate TakeReadFinish(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8, fl: Flag)
  {
    && (fl == Free || fl == Back)
    && a == multiset{
      ReadPending(key, t),
      FlagsField(key, fl)
    }
    && a == multiset{
      ReadObtained(key, t)
    }
  }

  predicate TakeReadBail(a: multiset<Q>, b: multiset<Q>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(key, t, r),
      ReadPending(key, t)
    }
    && b == multiset{
      ReadRefCount(key, t, if r == 0 then 255 else r-1)
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
      && (q.flags == Free ==> state.writeLock == WLSNone && !state.backHeld)
      && (q.flags == Back ==> state.writeLock == WLSNone && state.backHeld)
      && (q.flags == Write ==> state.writeLock != WLSNone && !state.backHeld)
      && (q.flags == Back_PendingWrite ==>
          state.writeLock == WLSPendingAwaitBack && state.backHeld)
    )
    && (q.ReadRefCount? ==>
      && 0 <= q.t < NUM_THREADS
      && state.readCounts[q.t] == q.refcount as int
    )
    && (q.BackObtained? ==>
      state.backHeld
    )
    && (q.WritePendingAwaitBack? ==>
      state.writeLock == WLSPendingAwaitBack
    )
    && (q.WritePending? ==>
      state.writeLock == WLSPending(q.visited)
    )
    && (q.WriteObtained? ==>
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
    && (q.q.ReadRefCount? && r.q.ReadRefCount? ==> !(q.q.key == r.q.key && q.q.t == r.q.t))
    && (q.q.BackObtained? && r.q.BackObtained? ==> q.q.key != r.q.key)
    && (q.q.WritePendingAwaitBack? && r.q.WritePendingAwaitBack? ==> q.q.key != r.q.key)
    && (q.q.WritePending? && r.q.WritePending? ==> q.q.key != r.q.key)
    && (q.q.WriteObtained? && r.q.WriteObtained? ==> q.q.key != r.q.key)
    && (q.q.Global? ==>
      && InvObject(r, q.q.g)
    )
  }

  predicate Inv(s: Variables)
  {
    && (forall g | g in s.m :: g.Internal? && g.q.Global? ==> InvGlobal(g.q.g))
    && (forall a, b | multiset{a,b} <= s.m :: Inv2(a, b))
  }

  lemma TakeBackPreservesInv(
    s: Variables, s': Variables,
    a: multiset<R>, b: multiset<R>, c: multiset<R>,
    key: Key, g: map<Key, RWLockState>, g': map<Key, RWLockState>)
  requires TakeBack(a, b, key, g, g')
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
        assert Inv2(Internal(FlagsField(key, Free)), r);
        assert Inv2(q, r);
      } else if q in c && r in b {
        assert Inv2(q, Internal(Global(g)));
        assert Inv2(q, Internal(FlagsField(key, Free)));
        assert Inv2(q, r);
      } else if multiset{q, r} <= b {
        assert Inv2(q, r);
      }
    }
    assert Inv(s');
  }

  method transform_TakeBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, Free))
  ensures t == Internal(FlagsField(key, Back))
  ensures u == Internal(BackObtained(key))

  method transform_TakeWrite(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, Free))
  ensures t == Internal(FlagsField(key, Write))
  ensures u == Internal(WritePendingAwaitBack(key))

  method transform_TakeWriteAwaitBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == Internal(FlagsField(key, Back))
  ensures t == Internal(FlagsField(key, Back_PendingWrite))
  ensures u == Internal(WritePendingAwaitBack(key))

  method transform_TakeWriteFinishBack(key: Key, fl: Flag, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires fl == Write || fl == Free
  requires s1 == Internal(FlagsField(key, fl))
  requires s2 == Internal(WritePendingAwaitBack(key))
  ensures t1 == Internal(FlagsField(key, fl))
  ensures t2 == Internal(WritePending(key, 0))

  method transform_TakeWriteCheckReadZero(key: Key, idx: int, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == Internal(ReadRefCount(key, idx, 0))
  requires s2 == Internal(WritePending(key, idx))
  ensures t1 == Internal(ReadRefCount(key, idx, 0))
  ensures t2 == Internal(WritePending(key, idx + 1))
}
