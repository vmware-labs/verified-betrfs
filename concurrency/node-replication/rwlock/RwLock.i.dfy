include "../../framework/Rw.i.dfy"
include "../../scache/rwlock/FullMap.i.dfy"
include "Handle.i.dfy"
include "../../../lib/Base/Option.s.dfy"

module RwLock refines Rw {
  import opened FullMaps
  import Handle

  // TODO find the right constant for perf -- balancing contention
  // and concurrency.
  ghost const RC_WIDTH := 24

  type ThreadId = nat

  type StoredType = Handle.Handle

  // Standard flow for obtaining a 'shared' lock

  datatype SharedState =
    | SharedPending(ghost t: int)                  // inc refcount
    | SharedObtained(ghost t: int, b: StoredType)  // exclusive bit not set

  // Standard flow for obtaining an 'exclusive' lock

  // This is the thread state of a thread working on acquiring
  // the exclusive lock. There can be only one of these, because only
  // one thread can atomically set the ExclusiveState.exc bit to true.
  datatype ExcState =
    | ExcNone
    | ExcPending(ghost visited: int, b: StoredType)
    | ExcObtained

  // This is the actual (non-ghost) state of the exclusive bit that
  // a thread sets before it scans the read flags.
  datatype ExclusiveState =
    | ExclusiveNone
    | ExclusiveState(exc: bool, stored_value: StoredType)

  datatype M = M(
    exclusive: ExclusiveState,
    ghost refCounts: map<ThreadId, nat>,

    ghost sharedState: FullMap<SharedState>,
    exc: ExcState
  ) | Fail

  function unit() : M
  {
    M(ExclusiveNone, map[], zero_map(), ExcNone)
  }

  function dot(x: M, y: M) : M
  {
    if
      x.M? && y.M?
      && !(x.exclusive.ExclusiveState? && y.exclusive.ExclusiveState?)
      && x.refCounts.Keys !! y.refCounts.Keys
      && (x.exc.ExcNone? || y.exc.ExcNone?)
    then
      M(
        if x.exclusive.ExclusiveState? then x.exclusive else y.exclusive,
        (map k | k in x.refCounts.Keys + y.refCounts.Keys ::
            if k in x.refCounts.Keys then x.refCounts[k] else y.refCounts[k]),
        add_fns(x.sharedState, y.sharedState),
        if !x.exc.ExcNone? then x.exc else y.exc
      )
    else
      Fail
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y) == Fail {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, y) == Fail {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }

  function IsSharedRefFor(t: int) : (SharedState) -> bool
  {
    (ss: SharedState) => ss.t == t
  }

  function CountSharedRefs(m: FullMap<SharedState>, t: int) : nat
  {
    SumFilter(IsSharedRefFor(t), m)
  }

  function CountAllRefs(state: M, t: int) : nat
  requires state.M?
  {
    CountSharedRefs(state.sharedState, t)
  }

  predicate Inv(x: M)
  {
    && x != unit() ==> (
      && x.M?
      && x.exclusive.ExclusiveState?
      && (x.exc.ExcPending? ==>
        && 0 <= x.exc.visited <= RC_WIDTH as int
        && x.exc.b == x.exclusive.stored_value
      )
      && (forall t | 0 <= t < RC_WIDTH as int
        :: t in x.refCounts && x.refCounts[t] == CountAllRefs(x, t))

      && (!x.exclusive.exc ==>
        && x.exc.ExcNone?
      )
      && (x.exclusive.exc ==>
        && (x.exc.ExcPending? || x.exc.ExcObtained?)
      )
      && (forall ss: SharedState :: x.sharedState.m[ss] > 0 ==>
        && 0 <= ss.t < RC_WIDTH as int
        && (ss.SharedObtained? ==>
          && ss.b == x.exclusive.stored_value
          && !x.exc.ExcObtained?
          && (x.exc.ExcPending? ==> x.exc.visited <= ss.t)
        )
      )
    )
  }

  function I(x: M) : Option<StoredType>
  //requires Inv(x)
  {
    if !x.M? || x == unit() || x.exc.ExcObtained? then (
      None
    ) else (
      Some(x.exclusive.stored_value)
    )
  }

  function dot3(a: M, b: M, c: M) : M
  {
    dot(dot(a, b), c)
  }

  ////// Handlers

  function CentralHandle(exclusive: ExclusiveState) : M {
    M(exclusive, map[], zero_map(), ExcNone)
  }

  function RefCount(t: ThreadId, count: nat) : M {
    M(ExclusiveNone, map[t := count], zero_map(), ExcNone)
  }

  function SharedHandle(ss: SharedState) : M {
    M(ExclusiveNone, map[], unit_fn(ss), ExcNone)
  }

  function ExcHandle(e: ExcState) : M {
    M(ExclusiveNone, map[], zero_map(), e)
  }

  ////// Transitions

  predicate ExcBegin(m: M, m': M)
  {
    && m.M?
    && m.exclusive.ExclusiveState?
    && !m.exclusive.exc

    && m == CentralHandle(m.exclusive)
    && m' == dot(
      CentralHandle(m.exclusive.(exc := true)),
      ExcHandle(ExcPending(0, m.exclusive.stored_value))
    )
  }

  lemma ExcBegin_Preserves(m: M, m': M)
  requires ExcBegin(m, m')
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert dot(m', p).sharedState == dot(m, p).sharedState;
    }
  }

  predicate TakeExcLockCheckRefCount(m: M, m': M)
  {
    && m.M?
    && m.exc.ExcPending?
    && m.exc.visited in m.refCounts
    && 0 <= m.exc.visited < RC_WIDTH as int

    && m == dot(
      ExcHandle(m.exc),
      RefCount(m.exc.visited, 0)
    )
    && m' == dot(
      ExcHandle(m.exc.(visited := m.exc.visited + 1)),
      RefCount(m.exc.visited, 0)
    )
  }

  lemma TakeExcLockCheckRefCount_Preserves(m: M, m': M)
  requires TakeExcLockCheckRefCount(m, m')
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert dot(m', p).sharedState == dot(m, p).sharedState;
      //assert dot(m, p).refCounts[m.exc.visited] == 0;
      assert CountAllRefs(dot(m, p), m.exc.visited) == 0;
      assert CountSharedRefs(dot(m, p).sharedState, m.exc.visited) == 0;
      UseZeroSum(IsSharedRefFor(m.exc.visited), dot(m, p).sharedState);
    }
  }

  predicate Withdraw_TakeExcLockFinish(m: M, m': M, b': StoredType)
  {
    && m.M?
    && m.exc.ExcPending?
    && m.exc.visited == RC_WIDTH as int
    && m == ExcHandle(m.exc)
    && m' == ExcHandle(ExcObtained)
    && b' == m.exc.b
  }

  lemma Withdraw_TakeExcLockFinish_Preserves(m: M, m': M, b': StoredType)
  requires Withdraw_TakeExcLockFinish(m, m', b')
  ensures withdraw(m, m', b')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
    ensures I(dot(m, p)) == Some(b')
    ensures I(dot(m', p)) == None
    {
      assert dot(m', p).sharedState == dot(m, p).sharedState;
    }
  }

  predicate Deposit_ReleaseExcLock(m: M, m': M, b: StoredType)
  {
    && m.M?
    && m.exc.ExcObtained?
    && m.exclusive.ExclusiveState?
    && m == dot(
      CentralHandle(m.exclusive),
      ExcHandle(m.exc)
    )
    && m' ==
      CentralHandle(m.exclusive
        .(exc := false)
        .(stored_value := b)
      )
  }

  lemma Deposit_ReleaseExcLock_Preserves(m: M, m': M, b: StoredType)
  requires Deposit_ReleaseExcLock(m, m', b)
  ensures deposit(m, m', b)
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p))
    ensures I(dot(m, p)) == None
    ensures I(dot(m', p)) == Some(b)
    {
      SumFilterSimp<SharedState>();
      assert forall b :: dot(m', p).sharedState.m[b] == dot(m, p).sharedState.m[b];

      var state' := dot(m', p);
      forall ss: SharedState | state'.sharedState.m[ss] > 0
      ensures 0 <= ss.t < RC_WIDTH as int
      ensures (ss.SharedObtained? ==> ss.b == state'.exclusive.stored_value)
      {
      }
    }
  }

  predicate SharedIncCount(m: M, m': M, t: int)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
    && m' == dot(
      RefCount(t, m.refCounts[t] + 1),
      SharedHandle(SharedPending(t))
    )
  }

  lemma SharedIncCount_Preserves(m: M, m': M, t: int)
  requires SharedIncCount(m, m', t)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      SumFilterSimp<SharedState>();
      var state := dot(m, p);
      var state' := dot(m', p);
      forall t0 | 0 <= t0 < RC_WIDTH as int
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
  }

  predicate SharedDecCountPending(m: M, m': M, t: int)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedPending(t))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  lemma SharedDecCountPending_Preserves(m: M, m': M, t: int)
  requires SharedDecCountPending(m, m', t)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
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

      forall t0 | 0 <= t0 < RC_WIDTH as int
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
  }

  predicate SharedDecCountObtained(m: M, m': M, t: int, b: StoredType)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == dot(
      RefCount(t, m.refCounts[t]),
      SharedHandle(SharedObtained(t, b))
    )
    && (m.refCounts[t] >= 1 ==>
      m' == RefCount(t, m.refCounts[t] - 1)
    )
  }

  lemma SharedDecCountObtained_Preserves(m: M, m': M, t: int, b: StoredType)
  requires SharedDecCountObtained(m, m', t, b)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
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

      forall t0 | 0 <= t0 < RC_WIDTH as int
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
  }

  predicate SharedCheckExc(m: M, m': M, t: int)
  {
    && m.M?
    //&& 0 <= t < RC_WIDTH as int
    && m.exclusive.ExclusiveState?
    && !m.exclusive.exc
    && m == dot(
      CentralHandle(m.exclusive),
      SharedHandle(SharedPending(t))
    )
    && m' == dot(
      CentralHandle(m.exclusive),
      SharedHandle(SharedObtained(t, m.exclusive.stored_value))
    )
  }

  lemma SharedCheckExc_Preserves(m: M, m': M, t: int)
  requires SharedCheckExc(m, m', t)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      SumFilterSimp<SharedState>();

      var state := dot(m, p);
      var state' := dot(m', p);

      assert CountAllRefs(state, t) == CountAllRefs(state', t);
      //assert forall t0 | t0 != t :: CountAllRefs(state, t) == CountAllRefs(state', t);
    }
  }

  function Rcs(s: nat, t: nat) : M
  requires s <= t
  decreases t - s
  {
    if t == s then
      unit()
    else
      dot(RefCount(s, 0), Rcs(s+1, t))
  }

  predicate Init(s: M)
  {
    && s.M?
    && s.exclusive.ExclusiveState?
    && s.exclusive.exc
    && s.refCounts == (map threadId | 0 <= threadId < RC_WIDTH :: 0)
    && s.sharedState == FullMaps.zero_map()
    && s.exc == ExcObtained // client starts out holding the exc lock so it can determine the inital value of the lock-protected field.
  }

  lemma InitImpliesInv(x: M)
//  requires Init(x)
//  ensures Inv(x)
//  ensures I(x) == None
  {
    SumFilterSimp<SharedState>();
    assert Init(x);
    assert Inv(x);
    assert I(x) == None;
  }

  lemma inv_unit()
  // ensures Inv(unit())
  // ensures I(unit()) == None
  {}
}

module RwLockToken {
  import opened Options
  import opened RwLock
  import HandleModule = Handle
  import T = RwTokens(RwLock)

  type Token = T.Token
  type Handle = HandleModule.Handle

  glinear method perform_ExcBegin(glinear centralToken: Token)
  returns (glinear centralToken': Token, glinear excToken': Token)
  requires var m := centralToken.val;
    && m.M?
    && m.exclusive.ExclusiveState?
    && !m.exclusive.exc
    && m == CentralHandle(m.exclusive)
  ensures centralToken'.val == CentralHandle(centralToken.val.exclusive.(exc := true))
  ensures excToken'.val == ExcHandle(ExcPending(0, centralToken.val.exclusive.stored_value))
  ensures centralToken'.loc == excToken'.loc == centralToken.loc
  {
    var m := centralToken.val;
    var a := CentralHandle(m.exclusive.(exc := true));
    var b := ExcHandle(ExcPending(0, m.exclusive.stored_value));
    ExcBegin_Preserves(centralToken.val, dot(a, b));
    centralToken', excToken' := T.internal_transition_1_2(centralToken, a, b);
  }

  glinear method perform_TakeExcLockCheckRefCount(glinear handle: Token, glinear rc: Token)
  returns (glinear handle': Token, glinear rc': Token)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPending?
    && m == ExcHandle(m.exc)
    && 0 <= m.exc.visited < RC_WIDTH as int
  requires rc.val == RefCount(handle.val.exc.visited, 0)
  requires rc.loc == handle.loc
  ensures rc'.loc == handle'.loc == rc.loc
  ensures handle'.val == ExcHandle(handle.val.exc.(visited := handle.val.exc.visited + 1))
  ensures rc'.val == rc.val
  {
    var a := ExcHandle(handle.val.exc.(visited := handle.val.exc.visited + 1));
    var b := rc.val;
    TakeExcLockCheckRefCount_Preserves(dot(handle.val, rc.val), dot(a, b));
    handle', rc' := T.internal_transition_2_2(handle, rc, a, b);
  }

  glinear method perform_SharedIncCount(glinear rc: Token, ghost t: int)
  returns (glinear rc': Token, glinear handle': Token)
  requires var m := rc.val;
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
  ensures rc'.loc == handle'.loc == rc.loc
  ensures rc'.val == RefCount(t, rc.val.refCounts[t] + 1)
  ensures handle'.val == SharedHandle(SharedPending(t))
  {
    var a := RefCount(t, rc.val.refCounts[t] + 1);
    var b := SharedHandle(SharedPending(t));
    SharedIncCount_Preserves(rc.val, dot(a, b), t);
    rc', handle' := T.internal_transition_1_2(rc, a, b);
  }

  glinear method pre_SharedDecCountPending(glinear rc: Token, glinear handle: Token, ghost t: int)
  returns (glinear rc': Token, glinear handle': Token)
  requires rc.val.M?
  requires handle.val.M?
  requires rc.loc == handle.loc
  requires t in rc.val.refCounts
  requires handle.val.sharedState.m[SharedPending(t)] >= 1
  ensures rc.val.refCounts[t] >= 1
  ensures handle' == handle
  ensures rc' == rc
  {
    rc' := rc;
    handle' := handle;
    ghost var rest := T.obtain_invariant_2(inout rc', inout handle');
    var m := dot(rc'.val, handle'.val);
    ghost var state := dot(m, rest);
    if CountSharedRefs(state.sharedState, t) == 0 {
      assert state.sharedState.m[SharedPending(t)] >= 1;
      FullMaps.UseZeroSum(IsSharedRefFor(t), state.sharedState);
      assert false;
    }
    assert state.refCounts[t] >= 1;
    assert m.refCounts[t] == state.refCounts[t];
  }

  glinear method perform_SharedDecCountPending(glinear rc: Token, glinear handle: Token, ghost t: int)
  returns (glinear rc': Token)
  requires var m := rc.val;
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
  requires var m := handle.val;
    && m.M?
    && m == SharedHandle(SharedPending(t))
  requires rc.loc == handle.loc
  ensures rc'.loc == rc.loc
  ensures rc.val.refCounts[t] >= 1
  ensures rc'.val == RefCount(t, rc.val.refCounts[t] - 1)
  {
    rc' := rc;
    glinear var handle' := handle;
    rc', handle' := pre_SharedDecCountPending(rc', handle', t);
    var a := RefCount(t, rc.val.refCounts[t] - 1);
    SharedDecCountPending_Preserves(dot(rc'.val, handle.val), a, t);
    rc' := T.internal_transition_2_1(rc', handle', a);
  }

  glinear method pre_SharedDecCountObtained(glinear rc: Token, glinear handle: Token, ghost t: int, ghost b: StoredType)
  returns (glinear rc': Token, glinear handle': Token)
  requires rc.val.M?
  requires handle.val.M?
  requires rc.loc == handle.loc
  requires t in rc.val.refCounts
  requires handle.val.sharedState.m[SharedObtained(t, b)] >= 1
  ensures rc.val.refCounts[t] >= 1
  ensures handle' == handle
  ensures rc' == rc
  {
    rc' := rc;
    handle' := handle;
    ghost var rest := T.obtain_invariant_2(inout rc', inout handle');
    var m := dot(rc'.val, handle'.val);
    ghost var state := dot(m, rest);
    if CountSharedRefs(state.sharedState, t) == 0 {
      assert state.sharedState.m[SharedObtained(t, b)] >= 1;
      FullMaps.UseZeroSum(IsSharedRefFor(t), state.sharedState);
      assert false;
    }
    assert state.refCounts[t] >= 1;
    assert m.refCounts[t] == state.refCounts[t];
  }

  glinear method perform_SharedDecCountObtained(glinear rc: Token, glinear handle: Token,
      ghost t: int, ghost b: StoredType)
  returns (glinear rc': Token)
  requires var m := rc.val;
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.refCounts
    && m == RefCount(t, m.refCounts[t])
  requires var m := handle.val;
    && m.M?
    && m == SharedHandle(SharedObtained(t, b))
  requires rc.loc == handle.loc
  ensures rc'.loc == rc.loc
  ensures rc.val.refCounts[t] >= 1
  ensures rc'.val == RefCount(t, rc.val.refCounts[t] - 1)
  {
    rc' := rc;
    glinear var handle' := handle;
    rc', handle' := pre_SharedDecCountObtained(rc', handle', t, b);
    var a := RefCount(t, rc.val.refCounts[t] - 1);
    SharedDecCountObtained_Preserves(dot(rc'.val, handle.val), a, t, b);
    rc' := T.internal_transition_2_1(rc', handle', a);
  }

  glinear method perform_SharedCheckExc(glinear c: Token, glinear handle: Token, ghost t: int)
  returns (glinear c': Token, glinear handle': Token)
  //requires 0 <= t < RC_WIDTH as int
  requires var m := c.val;
    && m.M?
    && m.exclusive.ExclusiveState?
    && !m.exclusive.exc
    && m == CentralHandle(m.exclusive)
  requires handle.val == SharedHandle(SharedPending(t))
  requires c.loc == handle.loc
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == c.val
  ensures handle'.val == SharedHandle(SharedObtained(t, c.val.exclusive.stored_value))
  {
    var a := c.val;
    var b := SharedHandle(SharedObtained(t, c.val.exclusive.stored_value));
    SharedCheckExc_Preserves(dot(c.val, handle.val), dot(a, b), t);
    c', handle' := T.internal_transition_2_2(c, handle, a, b);
  }

  glinear method perform_Withdraw_TakeExcLockFinish(glinear handle: Token)
  returns (glinear handle': Token, glinear b': Handle)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPending?
    && m.exc.visited == RC_WIDTH as int
    && m == ExcHandle(m.exc)
  ensures handle'.loc == handle.loc
  ensures handle'.val == ExcHandle(ExcObtained)
  ensures b' == handle.val.exc.b
  {
    var a := ExcHandle(ExcObtained);
    var d := handle.val.exc.b;
    Withdraw_TakeExcLockFinish_Preserves(handle.val, a, d);
    handle', b' := T.withdraw_1_1(handle, a, d);
  }

//  function method {:opaque} borrow_sot(gshared sot: SharedObtainedToken) : (gshared b: Handle)
//  requires sot.is_valid()
//  ensures b == sot.b
//
//  glinear method perform_Init(glinear b: Handle)
//  returns (glinear exclusive: Token, glinear rcs: Token)
//  ensures exclusive.loc == rcs.loc
//  ensures exclusive.val == CentralHandle(ExclusiveState(Unmapped, b))
//  ensures rcs.val == Rcs(0, RC_WIDTH as int)
//
//  glinear method pop_rcs(glinear t: Token, ghost a: nat, ghost b: nat)
//  returns (glinear x: Token, glinear t': Token)
//  requires a < b
//  requires t.val == Rcs(a, b)
//  ensures t'.val == Rcs(a+1, b)
//  ensures x.val == RefCount(a, 0)
//  ensures x.loc == t'.loc == t.loc
}
