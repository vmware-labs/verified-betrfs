include "ArrayPtr.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Constants.i.dfy"
include "ResourceSpec.s.dfy"
include "CacheResources.i.dfy"

module RWLock refines ResourceSpec {
  import Ptrs
  import CacheResources
  import opened NativeTypes
  import opened Constants
  import opened Options

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

  datatype Key = Key(data_ptr: Ptrs.Ptr, idx_ptr: Ptrs.Ptr, cache_idx: int)

  datatype WriteLockState = 
    | WLSNone
    | WLSPendingAwaitBack
    | WLSPending(visited: int)
    | WLSObtained

  datatype ProtectedData = ProtectedData(
      cache_entry: CacheResources.R,
      data: Ptrs.ArrayDeref<byte>,
      idx: Ptrs.Deref<int>)

  datatype RWLockState = RWLockState(
    writeLock: WriteLockState,
    backHeld: bool,
    readCounts: seq<int>,
    protectedData: Option<ProtectedData>)

  datatype R =
    | Global(g: map<Key, RWLockState>)
    | FlagsField(key: Key, flags: Flag)
    | ReadRefCount(key: Key, t: int, refcount: uint8)

    | ReadPending(key: Key, t: int)
    | ReadObtained(key: Key, t: int)
    
    | BackObtained(key: Key)

    | WritePendingAwaitBack(key: Key)
    | WritePending(key: Key, visited: int)
    | WriteObtained(key: Key)

    | ConstHandle(key: Key, data: ProtectedData)

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
      Global(g),
      FlagsField(key, Free)
    }
    && b == multiset{
      Global(g'),
      FlagsField(key, Back),
      BackObtained(key)
    }
  }

  predicate TakeWrite(a: multiset<R>, b: multiset<R>, key: Key)
  {
    && a == multiset{ FlagsField(key, Free) }
    && b == multiset{
      FlagsField(key, Write),
      WritePendingAwaitBack(key)
    }
  }

  predicate TakeWriteAwaitBack(a: multiset<R>, b: multiset<R>, key: Key)
  {
    && a == multiset{ FlagsField(key, Back) }
    && b == multiset{
      FlagsField(key, Back_PendingWrite),
      WritePendingAwaitBack(key)
    }
  }

  predicate TakeWriteFinishBack(a: multiset<R>, b: multiset<R>, key: Key, fl: Flag)
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

  predicate TakeWriteCheckReadZero(a: multiset<R>, b: multiset<R>, key: Key, idx: int)
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

  predicate TakeWriteFinish(a: multiset<R>, b: multiset<R>, key: Key)
  {
    && a == multiset{
      WritePending(key, NUM_THREADS)
    }
    && b == multiset{
      WriteObtained(key)
    }
  }

  predicate TakeRead(a: multiset<R>, b: multiset<R>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(key, t, r)
    }
    && a == multiset{
      ReadRefCount(key, t, if r == 255 then 0 else r+1),
      ReadPending(key, t)
    }
  }

  predicate TakeReadFinish(a: multiset<R>, b: multiset<R>, key: Key, t: int, r: uint8, fl: Flag)
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

  predicate TakeReadBail(a: multiset<R>, b: multiset<R>, key: Key, t: int, r: uint8)
  {
    && a == multiset{
      ReadRefCount(key, t, r),
      ReadPending(key, t)
    }
    && b == multiset{
      ReadRefCount(key, t, if r == 0 then 255 else r-1)
    }
  }

  /*method transform_TakeBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == FlagsField(key, Free)
  ensures t == FlagsField(key, Back)
  ensures u == BackObtained(key)

  method transform_TakeWrite(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == FlagsField(key, Free)
  ensures t == FlagsField(key, Write)
  ensures u == WritePendingAwaitBack(key)

  method transform_TakeWriteAwaitBack(key: Key, linear s: R)
  returns (linear t: R, linear u: R)
  requires s == FlagsField(key, Back)
  ensures t == FlagsField(key, Back_PendingWrite)
  ensures u == WritePendingAwaitBack(key)

  method transform_TakeWriteFinishBack(key: Key, fl: Flag, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires fl == Write || fl == Free
  requires s1 == FlagsField(key, fl)
  requires s2 == WritePendingAwaitBack(key)
  ensures t1 == FlagsField(key, fl)
  ensures t2 == WritePending(key, 0)

  method transform_TakeWriteCheckReadZero(key: Key, idx: int, linear s1: R, linear s2: R)
  returns (linear t1: R, linear t2: R)
  requires s1 == ReadRefCount(key, idx, 0)
  requires s2 == WritePending(key, idx)
  ensures t1 == ReadRefCount(key, idx, 0)
  ensures t2 == WritePending(key, idx + 1)*/

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

  predicate InvObjectState(q: R, state: RWLockState)
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
    && !q.Global?
    && q.key in g
    && InvObjectState(q, g[q.key])
  }

  predicate Inv2(q: R, r: R)
  {
    && !(q.Global? && r.Global?)
    && (q.FlagsField? && r.FlagsField? ==> q.key != r.key)
    && (q.ReadRefCount? && r.ReadRefCount? ==> !(q.key == r.key && q.t == r.t))
    && (q.BackObtained? && r.BackObtained? ==> q.key != r.key)
    && (q.WritePendingAwaitBack? && r.WritePendingAwaitBack? ==> q.key != r.key)
    && (q.WritePending? && r.WritePending? ==> q.key != r.key)
    && (q.WriteObtained? && r.WriteObtained? ==> q.key != r.key)
    && (q.Global? ==>
      && InvObject(r, q.g)
    )
  }

  predicate Inv(s: multiset<R>)
  {
    && (forall g | g in s :: g.Global? ==> InvGlobal(g.g))
    && (forall a, b | multiset{a,b} <= s :: Inv2(a, b))
  }

  lemma TakeBackPreservesInv(a: multiset<R>, b: multiset<R>, c: multiset<R>,
    key: Key, g: map<Key, RWLockState>, g': map<Key, RWLockState>)
  requires TakeBack(a, b, key, g, g')
  requires Inv(a + c)
  ensures Inv(b + c)
  {
    var y := b + c;
    forall q, r | multiset{q, r} <= y
    ensures Inv2(q, r)
    {
      if multiset{q, r} <= c {
        assert Inv2(q, r);
      } else if q in b && r in c {
        assert Inv2(Global(g), r);
        assert Inv2(FlagsField(key, Free), r);
        assert Inv2(q, r);
      } else if q in c && r in b {
        assert Inv2(q, Global(g));
        assert Inv2(q, FlagsField(key, Free));
        assert Inv2(q, r);
      } else if multiset{q, r} <= b {
        assert Inv2(q, r);
      }
    }
    assert Inv(y);
  }
}
