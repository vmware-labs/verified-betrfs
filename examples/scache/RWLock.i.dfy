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
    | TakeExcLockFinishWriteBackStep(flags: R, r: R, flags': R, r': R,
          t: int, fl: Flag, clean: bool)
    | TakeExcLockSharedLockZeroStep(rc_rc': R, r: R, r': R,
          t: int, idx: int, clean: bool)
    | TakeExcLockFinishStep(r: R, r': R, handle': R, t: int, clean: bool) 

  predicate TakeWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    flags: R,
    flags': R, r': R, handle': R)
  {
    && state' == state.(backHeld := true)
    && flags == Internal(FlagsField(key, Available))
    && flags' == Internal(FlagsField(key, WriteBack))
    && r' == Internal(WriteBackObtained(key))
    && (state.handle.Some? ==>
      handle' == Const(state.handle.value))
  }

  predicate ReleaseWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    flags: R, r: R, handle: R,
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
    && handle.Const? && handle.v.is_handle(key)
  }

  predicate TakeExcLockFinishWriteBack(
    key: Key, state: RWLockState, state': RWLockState,
    flags: R, r: R,
    flags': R, r': R,
    t: int, fl: Flag, clean: bool)
  {
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
    rc_rc': R,
    r: R, r': R,
    t: int, idx: int, clean: bool)
  {
    && state' == state.(excState := WLSPending(t, idx + 1, clean))
    && rc_rc' == Internal(SharedLockRefCount(key, idx,
        if t == idx then 1 else 0))
    && r == Internal(ExcLockPending(key, t, idx, clean))
    && r' == Internal(ExcLockPending(key, t, idx + 1, clean))
  }

  predicate TakeExcLockFinish(
    key: Key, state: RWLockState, state': RWLockState,
    r: R,
    r': R, handle': R,
    t: int, clean: bool)
  {
    && state' == state
        .(excState := WLSObtained(t, clean))
        .(handle := None)
    && r == Internal(ExcLockPending(key, t, NUM_THREADS, clean))
    && r' == Internal(ExcLockObtained(key, t, clean))
    && (state.handle.Some? ==> handle' == Exc(state.handle.value))
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
      case TakeWriteBackStep(flags, flags', r', handle') =>
        && step.a == multiset{flags}
        && step.a' == multiset{flags', r', handle'}
        && TakeWriteBack(step.key, step.state, step.state',
            flags, flags', r', handle')
      case ReleaseWriteBackStep(flags, r, handle, flags', fl) =>
        && step.a == multiset{flags, r, handle}
        && step.a' == multiset{flags'}
        && ReleaseWriteBack(step.key, step.state, step.state',
            flags, r, handle, flags', fl)
      case TakeExcLockFinishWriteBackStep(flags, r, flags', r', t, fl, clean) =>
        && step.a == multiset{flags, r}
        && step.a' == multiset{flags', r'}
        && TakeExcLockFinishWriteBack(step.key, step.state, step.state',
            flags, r, flags', r', t, fl, clean)
      case TakeExcLockSharedLockZeroStep(rc_rc', r, r', t, idx, clean) =>
        && step.a == multiset{r, rc_rc'}
        && step.a' == multiset{r', rc_rc'}
        && TakeExcLockSharedLockZero(step.key, step.state, step.state', rc_rc', r, r', t, idx, clean)
      case TakeExcLockFinishStep(r, r', handle', t, clean) =>
        && step.a == multiset{r}
        && step.a' == multiset{r',handle'}
        && TakeExcLockFinish(step.key, step.state, step.state', r, r', handle', t, clean)
    }
  }

  predicate InvRWLockState(key: Key, state: RWLockState, m: multiset<R>)
  {
    && |state.readCounts| == NUM_THREADS
    && (state.excState.WLSPendingAwaitWriteBack? ==>
        && state.readState == RSNone
        && !state.unmapped
        && 0 <= state.excState.t < NUM_THREADS
      )
    && (state.excState.WLSPending? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      && 0 <= state.excState.visited <= NUM_THREADS
      && (forall i | 0 <= i < state.excState.visited
          && i != state.excState.t :: state.readCounts[i] == 0)
      && (0 <= state.excState.t < state.excState.visited ==>
            state.readCounts[state.excState.t] == 1)
      && 0 <= state.excState.t < NUM_THREADS
    )
    && (state.excState.WLSObtained? ==>
      && state.readState == RSNone
      && !state.unmapped
      && !state.backHeld
      && (forall i | 0 <= i < |state.readCounts|
          && i != state.excState.t :: state.readCounts[i] == 0)
      && (0 <= state.excState.t < |state.readCounts| ==>
            state.readCounts[state.excState.t] == 1)
      && 0 <= state.excState.t < NUM_THREADS
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
    && (state.excState.WLSObtained? ==> state.handle.None?)
    && (!state.excState.WLSObtained? ==> state.handle.Some?)
    && (state.handle.Some? ==>
      state.handle.value.is_handle(key)
    )
    && (forall i | 0 <= i < |state.readCounts|
      :: state.readCounts[i] == CountCountedRefs(m, key, i))
  }

  predicate is_counted_ref(r: R, key: Key, t: int)
  {
    && r.Internal?
    && (r.q.SharedLockPending? || r.q.SharedLockPending2?
        || r.q.SharedLockObtained?
        || r.q.ExcLockPendingAwaitWriteBack?
        || r.q.ExcLockPending?
        || r.q.ExcLockObtained?
        || r.q.ReadingPendingCounted?
        || r.q.ReadingObtained?)
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
    && (r.q.SharedLockObtained? || r.q.WriteBackObtained?)
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

    && (q.SharedLockPending2? ==>
      && state.excState == WLSNone
      && (state.readState == RSNone || state.readState.RSObtained?)
    )
    && (q.SharedLockObtained? ==>
      && state.excState == WLSNone
      && state.readState == RSNone
    )

    && (q.ExcLockPendingAwaitWriteBack? ==>
      && state.excState == WLSPendingAwaitWriteBack(q.t)
    )
    && (q.ExcLockPending? ==>
      && state.excState == WLSPending(q.t, q.visited, q.clean)
    )
    && (q.ExcLockObtained? ==>
      && state.excState == WLSObtained(q.t, q.clean)
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

  predicate InvObject(r: R, g: map<Key, RWLockState>)
  {
    && (r.Internal? ==> (
      && !r.q.Global?
      && r.q.key in g
      && InvObjectState(r.q.key, r.q, g[r.q.key])
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
      ))
      && (q.q.Global? ==> (
        && InvObject(r, q.q.g)
      ))
    ))
  }

  predicate Inv(s: Variables)
  {
    && (forall g | g in s.m :: g.Internal? && g.q.Global? ==> InvGlobal(g.q.g, s.m))
    && (forall a, b | multiset{a,b} <= s.m :: Inv2(a, b))
    && (forall key :: CountConsts(s.m, key) == CountConstRefs(s.m, key))
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
  requires transform_step(a, a', step)
  requires Inv(s)
  requires step.basicStep.TakeWriteBackStep?
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
          // If a Const exists, then there is either
          // a SharedObtained or a WriteBackObtained object
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
      case TakeExcLockFinishStep(_,_,_,_,_) => {
         TakeExcLockFinishStepPreservesInv(s, s', step, a, a', rest);
      }
    }
  }
}
