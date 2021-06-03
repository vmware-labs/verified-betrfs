include "Ext.i.dfy"
include "SimpleExtToken.i.dfy"
include "../Constants.i.dfy"
include "FullMap.i.dfy"
include "../../../lib/Base/Option.s.dfy"

module RWLock refines SimpleExt {
  import opened Constants
  import opened Options
  import opened FullMaps

  /*
   * We consider two bits of the status field, ExcLock and Writeback.
   *
   * ExcLock and Writeback. Of course, 'ExcLock'
   * and 'Writeback' should be exclusive operations;
   * When both flags are set,
   * it should be interpreted as the 'ExcLock' being
   * pending, with the 'Writeback' being active.
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
    | Writeback
    | Writeback_PendingExcLock
    | PendingExcLock
    | ExcLock_Clean
    | ExcLock_Dirty

  type ThreadId = nat

  // Standard flow for obtaining a 'shared' lock

  datatype SharedState =
    | SharedPending(t: ThreadId)              // inc refcount
    | SharedPending2(t: ThreadId)             // !free & !writelocked
    | SharedObtained(t: ThreadId, b: Base.M)  // !reading

  // Standard flow for obtaining an 'exclusive' lock

  datatype ExcState = 
    | ExcNone
      // set ExcLock bit:
    | ExcPendingAwaitWriteback(t: int, b: Base.M)
      // check Writeback bit unset
      //   and `visited` of the refcounts
    | ExcPending(t: int, visited: int, clean: bool, b: Base.M)
    | ExcObtained(t: int, clean: bool)

  datatype WritebackState =
    | WritebackNone
      // set Writeback status bit
    | WritebackObtained(b: Base.M)

  // Flow for the phase of reading in a page from disk.
  // This is a special-case flow, because it needs to be performed
  // on the way to obtaining a 'shared' lock, but it requires
  // exclusive access to the underlying memory and resources.
  // End-game for this flow is to become an ordinary 'shared' lock

  datatype ReadState =
    | ReadNone
    | ReadPending                        // set status bit to ExcLock | Reading
    | ReadPendingCounted(t: ThreadId)    // inc refcount
    | ReadObtained(t: ThreadId)          // clear ExcLock bit

  datatype CentralState =
    | CentralNone
    | CentralState(flag: Flag, stored_value: Base.M)

  datatype M = M(
    central: CentralState,
    refCounts: map<ThreadId, nat>,

    sharedState: FullMap<SharedState>,
    exc: ExcState,
    read: ReadState,

    // Flow for the phase of doing a write-back.
    // Special case in part because it can be initiated by any thread
    // and completed by any thread (not necessarily the same one).
    
    writeback: WritebackState
  )

  type F = M

  function unit() : F
  {
    M(CentralNone, map[], zero_map(), ExcNone, ReadNone, WritebackNone)
  }

  predicate dot_defined(a: F, b: F)
  {
    && !(a.central.CentralState? && b.central.CentralState?)
    && a.refCounts.Keys !! b.refCounts.Keys
    && (a.exc.ExcNone? || b.exc.ExcNone?)
    && (a.read.ReadNone? || b.read.ReadNone?)
    && (a.writeback.WritebackNone? || b.writeback.WritebackNone?)
  }

  function dot(a: F, b: F) : F
    //requires dot_defined(a, b)
  {
    M(
      if a.central.CentralState? then a.central else b.central,
      (map k | k in a.refCounts.Keys + b.refCounts.Keys ::
          if k in a.refCounts.Keys then a.refCounts[k] else b.refCounts[k]),
      add_fns(a.sharedState, b.sharedState),
      if !a.exc.ExcNone? then a.exc else b.exc,
      if !a.read.ReadNone? then a.read else b.read,
      if !a.writeback.WritebackNone? then a.writeback else b.writeback
    ) 
  }

  lemma dot_unit(x: F)
  ensures dot_defined(x, unit())
  ensures dot(x, unit()) == x
  {
  }

  lemma commutative(x: F, y: F)
  //requires dot_defined(x, y)
  ensures dot_defined(y, x)
  ensures dot(x, y) == dot(y, x)
  {
  }

  lemma associative(x: F, y: F, z: F)
  //requires dot_defined(y, z)
  //requires dot_defined(x, dot(y, z))
  ensures dot_defined(x, y)
  ensures dot_defined(dot(x, y), z)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    assume false;
  }

  function IsSharedRefFor(t: int) : (SharedState) -> bool
  {
    (ss: SharedState) => ss.t == t
  }

  function CountSharedRefs(m: FullMap<SharedState>, t: int) : nat
  {
    SumFilter(IsSharedRefFor(t), m)
  }

  function CountAllRefs(state: F, t: int) : nat
  {
    CountSharedRefs(state.sharedState, t)

      + (if (state.exc.ExcPendingAwaitWriteback?
            || state.exc.ExcPending?
            || state.exc.ExcObtained?) && state.exc.t == t
         then 1 else 0)

      + (if (state.read.ReadPendingCounted?
            || state.read.ReadObtained?) && state.read.t == t
         then 1 else 0)
  }

  predicate Inv(state: F)
  {
    && state != unit() ==> (
      && state.central.CentralState?
      && (state.exc.ExcPendingAwaitWriteback? ==>
        && state.read.ReadNone?
        && -1 <= state.exc.t < NUM_THREADS
        && state.exc.b == state.central.stored_value
      )
      && (state.exc.ExcPending? ==>
        && state.read == ReadNone
        && state.writeback.WritebackNone?
        && 0 <= state.exc.visited <= NUM_THREADS
        && -1 <= state.exc.t < NUM_THREADS
        && state.exc.b == state.central.stored_value
      )
      && (state.exc.ExcObtained? ==>
        && state.read == ReadNone
        && state.writeback.WritebackNone?
        && -1 <= state.exc.t < NUM_THREADS
      )
      && (state.writeback.WritebackObtained? ==>
        && state.read == ReadNone
        && state.writeback.b == state.central.stored_value
      )
      && (state.read.ReadPending? ==>
        && state.writeback.WritebackNone?
      )
      && (state.read.ReadPendingCounted? ==>
        && state.writeback.WritebackNone?
        && 0 <= state.read.t < NUM_THREADS
      )
      && (state.read.ReadObtained? ==>
        && 0 <= state.read.t < NUM_THREADS
      )
      //&& (state.stored_value.Some? ==>
      //  state.stored_value.value.is_handle(key)
      //)
      && (forall t | 0 <= t < NUM_THREADS
        :: t in state.refCounts && state.refCounts[t] == CountAllRefs(state, t))

      && (state.central.flag == Unmapped ==>
        && state.writeback.WritebackNone?
        && state.read.ReadNone?
        && state.exc.ExcNone?
      )
      && (state.central.flag == Reading ==>
        && state.read.ReadObtained?
        && state.writeback.WritebackNone?
        && state.writeback.WritebackNone?
      )
      && (state.central.flag == Reading_ExcLock ==>
        && (state.read.ReadPending?
          || state.read.ReadPendingCounted?)
        && state.writeback.WritebackNone?
      )
      && (state.central.flag == Available ==>
        && state.exc.ExcNone?
        && state.read.ReadNone?
        && state.writeback.WritebackNone?
      )
      && (state.central.flag == Writeback ==>
        && state.exc.ExcNone?
        && state.read.ReadNone?
        && state.writeback.WritebackObtained?
      )
      && (state.central.flag == ExcLock_Clean ==>
        && (state.exc.ExcPending? || state.exc.ExcObtained?)
        && state.exc.clean
        && state.writeback.WritebackNone?
      )
      && (state.central.flag == ExcLock_Dirty ==>
        && (state.exc.ExcPending? || state.exc.ExcObtained?)
        && !state.exc.clean
        && state.writeback.WritebackNone?
      )
      && (state.central.flag == Writeback_PendingExcLock ==>
        && state.exc.ExcPendingAwaitWriteback?
        && state.writeback.WritebackObtained?
      )
      && (state.central.flag == PendingExcLock ==>
        && state.exc.ExcPendingAwaitWriteback?
        && state.writeback.WritebackNone?
      )
      && (forall ss: SharedState :: state.sharedState[ss] > 0 ==>
        && 0 <= ss.t < NUM_THREADS
        && (ss.SharedPending2? ==>
          && !state.exc.ExcObtained?
          && !state.read.ReadPending?
          && !state.read.ReadPendingCounted?
          && (state.exc.ExcPending? ==> state.exc.visited <= ss.t)
          && state.central.flag != Unmapped
        )
        && (ss.SharedObtained? ==>
          && ss.b == state.central.stored_value
          && !state.exc.ExcObtained?
          && state.read.ReadNone?
          && state.central.flag != Unmapped
          && (state.exc.ExcPending? ==> state.exc.visited <= ss.t)
        )
      )
    )
  }

  function Interp(a: F) : Base.M
    //requires Inv(a)
  {
    if a == unit() || a.exc.ExcObtained? || !a.read.ReadNone? then (
      Base.unit()
    ) else (
      a.central.stored_value
    )
  }

  function dot3(a: F, b: F, c: F) : F
  requires dot_defined(a, b) && dot_defined(dot(a, b), c)
  {
    dot(dot(a, b), c)
  }

  ////// Handlers

  function CentralHandle(central: CentralState) : F {
    M(central, map[], zero_map(), ExcNone, ReadNone, WritebackNone)
  }

  function RefCount(t: ThreadId, count: nat) : F {
    M(CentralNone, map[t := count], zero_map(), ExcNone, ReadNone, WritebackNone)
  }

  function SharedHandle(ss: SharedState) : F {
    M(CentralNone, map[], unit_fn(ss), ExcNone, ReadNone, WritebackNone)
  }

  function ReadHandle(r: ReadState) : F {
    M(CentralNone, map[], zero_map(), ExcNone, r, WritebackNone)
  }

  function ExcHandle(e: ExcState) : F {
    M(CentralNone, map[], zero_map(), e, ReadNone, WritebackNone)
  }

  function WritebackHandle(wb: WritebackState) : F {
    M(CentralNone, map[], zero_map(), ExcNone, ReadNone, wb)
  }

  ////// Transitions

  predicate TakeWriteback(m: M, m': M)
  {
    && m.central.CentralState?
    && m.central.flag == Available

    && m == CentralHandle(m.central)
    && m' == dot(
      CentralHandle(m.central.(flag := Writeback)),
      WritebackHandle(WritebackObtained(m.central.stored_value))
    )
  }

  lemma TakeWriteback_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires TakeWriteback(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    //assert dot(m', p).refCounts == dot(m, p).refCounts;
    assert dot(m', p).sharedState == dot(m, p).sharedState;
    //assert forall t | 0 <= t < NUM_THREADS ::
    //    CountAllRefs(dot(m', p), t) == CountAllRefs(dot(m, p), t);
    /*var state := dot(m', p);
    forall t | 0 <= t <= NUM_THREADS
    ensures t in state.refCounts && state.refCounts[t] == CountAllRefs(state, t)
    {
      assert 
    }*/
  }

  predicate ReleaseWriteback(m: M, m': M)
  {
    && m.central.CentralState?
    && m.writeback.WritebackObtained?

    && m == dot(
      CentralHandle(m.central),
      WritebackHandle(m.writeback)
    )

    && (m.central.flag == Writeback ==>
      m' == CentralHandle(m.central.(flag := Available))
    )
    && (m.central.flag == Writeback_PendingExcLock ==>
      m' == CentralHandle(m.central.(flag := PendingExcLock))
    )
  }

  lemma ReleaseWriteback_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires ReleaseWriteback(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    assert m.central.flag == Writeback
        || m.central.flag == Writeback_PendingExcLock;
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate ThreadlessExc(m: M, m': M)
  {
    && m.central.CentralState?
    && (m.central.flag == Available || m.central.flag == Writeback)

    && m == CentralHandle(m.central)
    && m' == dot(
      CentralHandle(m.central.(flag := 
          if m.central.flag == Available then PendingExcLock else Writeback_PendingExcLock)),
      ExcHandle(ExcPendingAwaitWriteback(-1, m.central.stored_value))
    )
  }

  lemma ThreadlessExc_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires ThreadlessExc(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate SharedToExc(m: M, m': M, ss: SharedState)
  {
    && m.central.CentralState?
    && (m.central.flag == Available || m.central.flag == Writeback)
    && ss.SharedObtained?

    && m == dot(
      CentralHandle(m.central),
      SharedHandle(ss)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := 
          if m.central.flag == Available then PendingExcLock else Writeback_PendingExcLock)),
      ExcHandle(ExcPendingAwaitWriteback(ss.t, ss.b))
    )
  }

  lemma SharedToExc_Preserves(p: M, m: M, m': M, ss: SharedState)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedToExc(m, m', ss)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    SumFilterSimp<SharedState>();

    assert dot(m', p).refCounts == dot(m, p).refCounts;
    assert forall b | b != ss :: dot(m', p).sharedState[b] == dot(m, p).sharedState[b];
    assert dot(m', p).sharedState[ss] + 1 == dot(m, p).sharedState[ss];
    assert CountAllRefs(dot(m', p), ss.t) == CountAllRefs(dot(m, p), ss.t);
  }

  predicate TakeExcLockFinishWriteback(m: M, m': M, clean: bool)
  {
    && m.central.CentralState?
    && m.exc.ExcPendingAwaitWriteback?
    && m.central.flag != Writeback && m.central.flag != Writeback_PendingExcLock
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == dot(
      CentralHandle(m.central.(flag :=
        if clean then ExcLock_Clean else ExcLock_Dirty)),
      ExcHandle(ExcPending(m.exc.t, 0, clean, m.exc.b))
    )
  }

  lemma TakeExcLockFinishWriteback_Preserves(p: M, m: M, m': M, clean: bool)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires TakeExcLockFinishWriteback(m, m', clean)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate TakeExcLockCheckRefCount(m: M, m': M)
  {
    && m.exc.ExcPending?
    && m.exc.visited in m.refCounts
    && 0 <= m.exc.visited < NUM_THREADS

    && var expected_rc := (if m.exc.visited == m.exc.t then 1 else 0);

    && m == dot(
      ExcHandle(m.exc),
      RefCount(m.exc.visited, expected_rc)
    )
    && m' == dot(
      ExcHandle(m.exc.(visited := m.exc.visited + 1)),
      RefCount(m.exc.visited, expected_rc)
    )
  }

  lemma TakeExcLockCheckRefCount_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires TakeExcLockCheckRefCount(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
    //assert dot(m, p).refCounts[m.exc.visited] == 0;
    var expected_rc := (if m.exc.visited == m.exc.t then 1 else 0);
    assert CountAllRefs(dot(m, p), m.exc.visited) == expected_rc;
    assert CountSharedRefs(dot(m, p).sharedState, m.exc.visited) == 0;
    UseZeroSum(IsSharedRefFor(m.exc.visited), dot(m, p).sharedState);
  }

  predicate Withdraw_TakeExcLockFinish(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcPending?
    && m.exc.visited == NUM_THREADS
    && m == ExcHandle(m.exc)
    && m' == ExcHandle(ExcObtained(m.exc.t, m.exc.clean))
    && b == Base.unit()
    && b' == m.exc.b
  }

  lemma Withdraw_TakeExcLockFinish_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Withdraw_TakeExcLockFinish(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate Deposit_DowngradeExcLoc(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcObtained?
    && m.central.CentralState?
    && 0 <= m.exc.t < NUM_THREADS
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == dot(
      CentralHandle(m.central
        .(flag := Available)
        .(stored_value := b)
      ),
      SharedHandle(SharedObtained(m.exc.t, b))
    )
    && b' == Base.unit()
  }

  lemma Deposit_DowngradeExcLoc_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Deposit_DowngradeExcLoc(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    SumFilterSimp<SharedState>();
    var ss := SharedObtained(m.exc.t, b);
    assert forall b | b != ss :: dot(m', p).sharedState[b] == dot(m, p).sharedState[b];
    assert dot(m', p).sharedState[ss] == dot(m, p).sharedState[ss] + 1;

    var state' := dot(m', p);
    forall ss: SharedState | state'.sharedState[ss] > 0
    ensures 0 <= ss.t < NUM_THREADS
    ensures (ss.SharedObtained? ==> ss.b == state'.central.stored_value)
    {
    }
  }

  predicate Withdraw_Alloc(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.central.CentralState?
    && m.central.flag == Unmapped
    && m == CentralHandle(m.central)

    && m' == dot(
      CentralHandle(m.central.(flag := Reading_ExcLock)),
      ReadHandle(ReadPending)
    )

    && b == Base.unit()
    && b' == m.central.stored_value
  }

  lemma Withdraw_Alloc_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Withdraw_Alloc(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate ReadingIncCount(m: M, m': M, t: int)
  {
    && t in m.refCounts
    && 0 <= t < NUM_THREADS
    && m == dot(
      ReadHandle(ReadPending),
      RefCount(t, m.refCounts[t])
    )
    && m' == dot(
      ReadHandle(ReadPendingCounted(t)),
      RefCount(t, m.refCounts[t] + 1)
    )
  }

  lemma ReadingIncCount_Preserves(p: M, m: M, m': M, t: int)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires ReadingIncCount(m, m', t)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    SumFilterSimp<SharedState>();
    assert dot(m', p).sharedState == dot(m, p).sharedState;
    var state := dot(m, p);
    var state' := dot(m', p);
    forall t0 | 0 <= t0 < NUM_THREADS
    ensures t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0)
    {
      if t == t0 {
        assert CountAllRefs(state', t0) == CountAllRefs(state, t0) + 1;
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      } else{
        assert CountAllRefs(state', t0) == CountAllRefs(state, t0);
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      }
    }
  }

  predicate ObtainReading(m: M, m': M)
  {
    && m.central.CentralState?
    && m.read.ReadPendingCounted?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := Reading)),
      ReadHandle(ReadObtained(m.read.t))
    )
  }

  lemma ObtainReading_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires ObtainReading(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
  }

  predicate Deposit_ReadingToShared(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.central.CentralState?
    && m.read.ReadObtained?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == dot(
      CentralHandle(m.central.(flag := Available).(stored_value := b)),
      SharedHandle(SharedObtained(m.read.t, b))
    )
    && b' == Base.unit()
  }

  lemma Deposit_ReadingToShared_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Deposit_ReadingToShared(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    SumFilterSimp<SharedState>();
    var state := dot(m, p);
    var state' := dot(m', p);
    forall ss: SharedState | state'.sharedState[ss] > 0
    ensures 0 <= ss.t < NUM_THREADS
    ensures ss.SharedObtained? ==>
          && ss.b == state'.central.stored_value
          && !state'.exc.ExcObtained?
          && (state'.exc.ExcPending? ==> state'.exc.visited <= ss.t)
    {
      if ss.SharedObtained? {
        assert ss.b == state'.central.stored_value;
        assert !state'.exc.ExcObtained?;
        assert (state'.exc.ExcPending? ==> state'.exc.visited <= ss.t);
      }
    }
  }

  predicate SharedIncCount(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
    && m' == dot(
      RefCount(t, m.refCounts[t] + 1),
      SharedHandle(SharedPending(t))
    )
  }

  lemma SharedIncCount_Preserves(p: M, m: M, m': M, t: int)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedIncCount(m, m', t)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    SumFilterSimp<SharedState>();
    var state := dot(m, p);
    var state' := dot(m', p);
    forall t0 | 0 <= t0 < NUM_THREADS
    ensures t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0)
    {
      if t == t0 {
        assert CountSharedRefs(state.sharedState, t) + 1
            == CountSharedRefs(state'.sharedState, t);
        assert CountAllRefs(state, t) + 1
            == CountAllRefs(state', t);
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      } else {
        assert CountSharedRefs(state.sharedState, t0) == CountSharedRefs(state'.sharedState, t0);
        assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      }
    }
  }

  predicate SharedDecCountPending(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedPending(t))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  lemma SharedDecCountPending_Preserves(p: M, m: M, m': M, t: int)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedDecCountPending(m, m', t)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    var state := dot(m, p);

    SumFilterSimp<SharedState>();

    assert state.refCounts[t] >= 1 by {
      if state.refCounts[t] == 0 {
        assert CountAllRefs(state, t) == 0;
        assert CountSharedRefs(state.sharedState, t) == 0;
        UseZeroSum(IsSharedRefFor(t), state.sharedState);
        assert false;
      }
    }

    var state' := dot(m', p);

    forall t0 | 0 <= t0 < NUM_THREADS
    ensures t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0)
    {
      if t == t0 {
        assert CountSharedRefs(state.sharedState, t)
            == CountSharedRefs(state'.sharedState, t) + 1;
        assert CountAllRefs(state, t)
            == CountAllRefs(state', t) + 1;
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      } else {
        assert CountSharedRefs(state.sharedState, t0) == CountSharedRefs(state'.sharedState, t0);
        assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      }
    }
  } 

  predicate SharedDecCountObtained(m: M, m': M, t: int, b: Base.M)
  {
    && 0 <= t < NUM_THREADS
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedObtained(t, b))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  lemma SharedDecCountObtained_Preserves(p: M, m: M, m': M, t: int, b: Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedDecCountObtained(m, m', t, b)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    var state := dot(m, p);

    SumFilterSimp<SharedState>();

    assert state.refCounts[t] >= 1 by {
      if state.refCounts[t] == 0 {
        assert CountAllRefs(state, t) == 0;
        assert CountSharedRefs(state.sharedState, t) == 0;
        UseZeroSum(IsSharedRefFor(t), state.sharedState);
        assert false;
      }
    }

    var state' := dot(m', p);

    forall t0 | 0 <= t0 < NUM_THREADS
    ensures t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0)
    {
      if t == t0 {
        assert CountSharedRefs(state.sharedState, t)
            == CountSharedRefs(state'.sharedState, t) + 1;
        assert CountAllRefs(state, t)
            == CountAllRefs(state', t) + 1;
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      } else {
        assert CountSharedRefs(state.sharedState, t0) == CountSharedRefs(state'.sharedState, t0);
        assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
        assert t0 in state'.refCounts && state'.refCounts[t0] == CountAllRefs(state', t0);
      }
    }
  } 

  predicate SharedCheckExc(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && m.central.CentralState?
    && (m.central.flag == Available
        || m.central.flag == Writeback
        || m.central.flag == Reading)
    && m == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending(t))
    )
    && m' == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending2(t))
    )
  }

  lemma SharedCheckExc_Preserves(p: M, m: M, m': M, t: int)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedCheckExc(m, m', t)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    SumFilterSimp<SharedState>();

    var state := dot(m, p);
    var state' := dot(m', p);

    assert CountAllRefs(state, t) == CountAllRefs(state', t);
    //assert forall t0 | t0 != t :: CountAllRefs(state, t) == CountAllRefs(state', t);
  }

  predicate SharedCheckReading(m: M, m': M, t: int)
  {
    && 0 <= t < NUM_THREADS
    && m.central.CentralState?
    && m.central.flag != Reading
    && m.central.flag != Reading_ExcLock
    && m == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending2(t))
    )
    && m' == dot(
      CentralHandle(m.central),
      SharedHandle(SharedObtained(t, m.central.stored_value))
    )
  }

  lemma SharedCheckReading_Preserves(p: M, m: M, m': M, t: int)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires SharedCheckReading(m, m', t)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    SumFilterSimp<SharedState>();

    var state := dot(m, p);
    var state' := dot(m', p);

    assert CountAllRefs(state, t) == CountAllRefs(state', t);
    //assert forall t0 | t0 != t :: CountAllRefs(state, t) == CountAllRefs(state', t);
  }

  predicate Deposit_Unmap(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.exc.ExcObtained?
    && m.exc.t == -1
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == CentralHandle(
      m.central.(flag := Unmapped).(stored_value := b)
    )
    && b' == Base.unit()
  }

  lemma Deposit_Unmap_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Deposit_Unmap(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate AbandonExcPending(m: M, m': M)
  {
    && m.exc.ExcPending?
    && m.exc.t == -1
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' == CentralHandle(m.central.(flag := Available))
  }

  lemma AbandonExcPending_Preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires AbandonExcPending(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == Interp(dot(m', p))
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  predicate Deposit_AbandonReadPending(m: M, m': M, b: Base.M, b': Base.M)
  {
    && m.read.ReadPending?
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ReadHandle(m.read)
    )
    && m' == CentralHandle(m.central.(flag := Unmapped).(stored_value := b))
    && b' == Base.unit()
  }

  lemma Deposit_AbandonReadPending_Preserves(p: M, m: M, m': M, b: Base.M, b': Base.M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires Deposit_AbandonReadPending(m, m', b, b')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m, p)) == b'
  ensures Interp(dot(m', p)) == b
  {
    assert dot(m', p).sharedState == dot(m, p).sharedState;
  }

  ///// 

  datatype InternalStep =
      | TakeWritebackStep
      | ReleaseWritebackStep
      | ThreadlessExcStep
      | SharedToExcStep(ss: SharedState)
      | TakeExcLockFinishWritebackStep(clean: bool)
      | TakeExcLockCheckRefCountStep
      | ReadingIncCountStep(t: int)
      | ObtainReadingStep
      | SharedIncCountStep(t: int)
      | SharedDecCountPendingStep(t: int)
      | SharedDecCountObtainedStep(t: int, b: Base.M)
      | SharedCheckExcStep(t: int)
      | SharedCheckReadingStep(t: int)
      | AbandonExcPendingStep

  datatype CrossStep =
      | Deposit_DowngradeExcLoc_Step
      | Deposit_ReadingToShared_Step
      | Deposit_Unmap_Step
      | Deposit_AbandonReadPending_Step
      | Withdraw_TakeExcLockFinish_Step
      | Withdraw_Alloc_Step

  predicate InternalNextStep(f: F, f': F, step: InternalStep) {
    match step {
      case TakeWritebackStep => TakeWriteback(f, f')
      case ReleaseWritebackStep => ReleaseWriteback(f, f')
      case ThreadlessExcStep => ThreadlessExc(f, f')
      case SharedToExcStep(ss: SharedState) => SharedToExc(f, f', ss)
      case TakeExcLockFinishWritebackStep(clean) => TakeExcLockFinishWriteback(f, f', clean)
      case TakeExcLockCheckRefCountStep => TakeExcLockCheckRefCount(f, f')
      case ReadingIncCountStep(t) => ReadingIncCount(f, f', t)
      case ObtainReadingStep => ObtainReading(f, f')
      case SharedIncCountStep(t) => SharedIncCount(f, f', t)
      case SharedDecCountPendingStep(t) => SharedDecCountPending(f, f', t)
      case SharedDecCountObtainedStep(t, b) => SharedDecCountObtained(f, f', t, b)
      case SharedCheckExcStep(t) => SharedCheckExc(f, f', t)
      case SharedCheckReadingStep(t) => SharedCheckReading(f, f', t)
      case AbandonExcPendingStep => AbandonExcPending(f, f')
    }
  }

  predicate InternalNext(f: F, f': F) {
    exists step :: InternalNextStep(f, f', step)
  }

  predicate CrossNextStep(f: F, f': F, b: Base.M, b': Base.M, step: CrossStep) {
    match step {
      case Deposit_DowngradeExcLoc_Step => Deposit_DowngradeExcLoc(f, f', b, b')
      case Deposit_ReadingToShared_Step => Deposit_ReadingToShared(f, f', b, b')
      case Deposit_Unmap_Step => Deposit_Unmap(f, f', b, b')
      case Deposit_AbandonReadPending_Step => Deposit_AbandonReadPending(f, f', b, b')
      case Withdraw_TakeExcLockFinish_Step => Withdraw_TakeExcLockFinish(f, f', b, b')
      case Withdraw_Alloc_Step => Withdraw_Alloc(f, f', b, b')
    }
  }

  predicate CrossNext(f: F, f': F, b: Base.M, b': Base.M) {
    exists step :: CrossNextStep(f, f', b, b', step)
  }

  lemma interp_unit()
  ensures Inv(unit()) && Interp(unit()) == Base.unit()
  {
  }

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  //requires InternalNext(f, f')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Interp(dot(f', p)) == Interp(dot(f, p))
  {
    var step :| InternalNextStep(f, f', step);
    match step {
      case TakeWritebackStep => TakeWriteback_Preserves(p, f,f');
      case ReleaseWritebackStep => ReleaseWriteback_Preserves(p, f,f');
      case ThreadlessExcStep => ThreadlessExc_Preserves(p, f,f');
      case SharedToExcStep(ss: SharedState) => SharedToExc_Preserves(p, f,f', ss);
      case TakeExcLockFinishWritebackStep(clean) => TakeExcLockFinishWriteback_Preserves(p, f,f', clean);
      case TakeExcLockCheckRefCountStep => TakeExcLockCheckRefCount_Preserves(p, f,f');
      case ReadingIncCountStep(t) => ReadingIncCount_Preserves(p, f,f', t);
      case ObtainReadingStep => ObtainReading_Preserves(p, f,f');
      case SharedIncCountStep(t) => SharedIncCount_Preserves(p, f,f', t);
      case SharedDecCountPendingStep(t) => SharedDecCountPending_Preserves(p, f,f', t);
      case SharedDecCountObtainedStep(t, b) => SharedDecCountObtained_Preserves(p, f,f', t, b);
      case SharedCheckExcStep(t) => SharedCheckExc_Preserves(p, f,f', t);
      case SharedCheckReadingStep(t) => SharedCheckReading_Preserves(p, f,f', t);
      case AbandonExcPendingStep => AbandonExcPending_Preserves(p, f,f');
    }
  }

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: Base.M, b': Base.M)
  //requires CrossNext(f, f', b, b')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  //requires Base.dot_defined(Interp(dot(f, p)), b)
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Base.dot_defined(Interp(dot(f', p)), b')
  ensures Base.dot(Interp(dot(f', p)), b')
       == Base.dot(Interp(dot(f, p)), b)
  {
    var step :| CrossNextStep(f, f', b, b', step);
    match step {
      case Deposit_DowngradeExcLoc_Step => Deposit_DowngradeExcLoc_Preserves(p, f, f', b, b');
      case Deposit_ReadingToShared_Step => Deposit_ReadingToShared_Preserves(p, f, f', b, b');
      case Deposit_Unmap_Step => Deposit_Unmap_Preserves(p, f, f', b, b');
      case Deposit_AbandonReadPending_Step => Deposit_AbandonReadPending_Preserves(p, f, f', b, b');
      case Withdraw_TakeExcLockFinish_Step => Withdraw_TakeExcLockFinish_Preserves(p, f, f', b, b');
      case Withdraw_Alloc_Step => Withdraw_Alloc_Preserves(p, f, f', b, b');
    }
    Base.commutative(Interp(dot(f, p)), b);
  }
}

/*module RWLockExtToken refines SimpleExtToken {
  import SEPCM = RWLockSimpleExtPCM
  import opened RWLockExt

  glinear method ReleaseWriteback(central: Token, handle: Token)
  requires central.loc == handle.loc
  requires
    && central.central.CentralState?
    && handle.writeback.WritebackObtained?
    && central == CentralHandle(central.central)
    && handle == WritebackHandle()

}*/

module RWLockSimpleExtPCM refines SimpleExtPCM {
  import SE = RWLock
}

module RWLockExtToken refines SimpleExtToken {
  import SEPCM = RWLockSimpleExtPCM
  import opened RWLock

  glinear datatype WritebackObtainedHandle = WritebackObtainedHandle(
    ghost b: Base.Handle,
    glinear token: Token)
  {
    predicate is_handle(key: Base.Key) {
      && b.is_handle(key)
      && token.get() == WritebackHandle(WritebackObtained(Base.one(b)))
    }
  }

  glinear method do_internal_step_2(glinear f: Token,
      ghost f1: F, ghost g1: F,
      ghost step: InternalStep)
  returns (glinear f': Token, glinear g': Token)
  requires dot_defined(f1, g1)
  requires InternalNextStep(f.get(), dot(f1, g1), step)
  ensures g'.loc() == f'.loc() == f.loc()
  ensures f'.get() == f1 && g'.get() == g1
  {
    assert InternalNext(f.get(), dot(f1, g1));
    glinear var f_out := do_internal_step(f, dot(f1, g1));
    f', g' := split(f_out, f1, g1);
  }

  glinear method perform_TakeWriteback(glinear c: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.get();
    && m.central.CentralState?
    && m.central.flag == Available
    && m == CentralHandle(m.central)
  ensures c'.loc() == handle'.loc() == c.loc()
  ensures c'.get() == CentralHandle(c.get().central.(flag := Writeback))
  ensures handle'.get() == WritebackHandle(WritebackObtained(c.get().central.stored_value))
  {
    c', handle' := do_internal_step_2(c,
        CentralHandle(c.get().central.(flag := Writeback)),
        WritebackHandle(WritebackObtained(c.get().central.stored_value)),
        TakeWritebackStep);
  }

  function method borrow(gshared f: Token) : (gshared b: Base.Handle)
  requires 
  {

  }
}
