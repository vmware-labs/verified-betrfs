include "../../framework/Rw.i.dfy"
include "../../scache/rwlock/FullMap.i.dfy"
include "Handle.i.dfy"
include "../../../lib/Base/Option.s.dfy"

module RwLock refines Rw {
  import opened FullMaps
  import Handle

  ghost const RC_WIDTH := 24

  type ThreadId = nat

  type StoredType = Handle.Handle

  // Standard flow for obtaining a 'shared' lock

  datatype SharedState =
    | SharedPending(ghost t: int)                  // inc refcount
    | SharedObtained(ghost t: int, b: StoredType)  // exclusive bit not set

  // Standard flow for obtaining an 'exclusive' lock

  datatype ExcState = 
    | ExcNone
    | ExcPending(ghost visited: int, b: StoredType)
    | ExcObtained

  datatype CentralState =
    | CentralNone
    | CentralState(exc: bool, stored_value: StoredType)

  datatype M = M(
    central: CentralState,
    ghost refCounts: map<ThreadId, nat>,

    ghost sharedState: FullMap<SharedState>,
    exc: ExcState
  ) | Fail

  function unit() : M
  {
    M(CentralNone, map[], zero_map(), ExcNone)
  }

  function dot(x: M, y: M) : M
  {
    if
      x.M? && y.M?
      && !(x.central.CentralState? && y.central.CentralState?)
      && x.refCounts.Keys !! y.refCounts.Keys
      && (x.exc.ExcNone? || y.exc.ExcNone?)
    then
      M(
        if x.central.CentralState? then x.central else y.central,
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

  function CountAllRefs(state: M, t: int) : nat
  requires state.M?
  {
    CountSharedRefs(state.sharedState, t)
  }

  predicate Inv(x: M)
  {
    && x != unit() ==> (
      && x.M?
      && x.central.CentralState?
      && (x.exc.ExcPending? ==>
        && 0 <= x.exc.visited <= RC_WIDTH as int
        && x.exc.b == x.central.stored_value
      )
      && (forall t | 0 <= t < RC_WIDTH as int
        :: t in x.refCounts && x.refCounts[t] == CountAllRefs(x, t))

      && (!x.central.exc ==>
        && x.exc.ExcNone?
      )
      && (x.central.exc ==>
        && (x.exc.ExcPending? || x.exc.ExcObtained?)
      )
      && (forall ss: SharedState :: x.sharedState.m[ss] > 0 ==>
        && 0 <= ss.t < RC_WIDTH as int
        && (ss.SharedObtained? ==>
          && ss.b == x.central.stored_value
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
      Some(x.central.stored_value)
    )
  }

  function dot3(a: M, b: M, c: M) : M
  {
    dot(dot(a, b), c)
  }

  ////// Handlers

  function CentralHandle(central: CentralState) : M {
    M(central, map[], zero_map(), ExcNone)
  }

  function RefCount(t: ThreadId, count: nat) : M {
    M(CentralNone, map[t := count], zero_map(), ExcNone)
  }

  function SharedHandle(ss: SharedState) : M {
    M(CentralNone, map[], unit_fn(ss), ExcNone)
  }

  function ExcHandle(e: ExcState) : M {
    M(CentralNone, map[], zero_map(), e)
  }

  ////// Transitions

  predicate ExcBegin(m: M, m': M)
  {
    && m.M?
    && m.central.CentralState?
    && !m.central.exc

    && m == CentralHandle(m.central)
    && m' == dot(
      CentralHandle(m.central.(exc := true)),
      ExcHandle(ExcPending(0, m.central.stored_value))
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
    && m.central.CentralState?
    && m == dot(
      CentralHandle(m.central),
      ExcHandle(m.exc)
    )
    && m' ==
      CentralHandle(m.central
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
      ensures (ss.SharedObtained? ==> ss.b == state'.central.stored_value)
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
    && m.central.CentralState?
    && !m.central.exc
    && m == dot(
      CentralHandle(m.central),
      SharedHandle(SharedPending(t))
    )
    && m' == dot(
      CentralHandle(m.central),
      SharedHandle(SharedObtained(t, m.central.stored_value))
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
}

/*
module RwLockToken {
  import opened RwLock
  import opened Constants
  import opened CacheHandle
  import T = RwTokens(RwLock)

  type Token = T.Token

  glinear datatype CentralToken = CentralToken(
    ghost flag: Flag,
    ghost stored_value: StoredType,
    glinear token: Token)
  {
    predicate has_flag(flag: Flag) {
      && this.flag == flag
      && token.val == CentralHandle(CentralState(flag, stored_value))
    }
    predicate is_handle(flag: Flag, stored_value: StoredType) {
      && this.flag == flag
      && this.stored_value == stored_value
      && token.val == CentralHandle(CentralState(flag, stored_value))
    }
  }

  glinear datatype WritebackObtainedToken = WritebackObtainedToken(
    ghost b: Handle,
    glinear token: Token)
  {
    predicate has_state(b: StoredType) {
      && this.b == b
      && token.val == WritebackHandle(WritebackObtained(b))
    }
    predicate is_handle(key: Key) {
      && b.is_handle(key)
      && token.val == WritebackHandle(WritebackObtained(b))
    }
  }

  glinear datatype SharedPendingToken = SharedToken(
    ghost t: ThreadId,
    glinear token: Token)
  {
    predicate is_handle(t: ThreadId) {
      && this.t == t
      && token.val == SharedHandle(SharedPending(t))
    }
  }

  glinear datatype SharedPending2Token = SharedToken(
    ghost t: ThreadId,
    glinear token: Token)
  {
    predicate is_handle(t: ThreadId) {
      && this.t == t
      && token.val == SharedHandle(SharedPending2(t))
    }
  }

  glinear datatype SharedObtainedToken = SharedObtainedToken(
    ghost t: ThreadId,
    ghost b: StoredType,
    glinear token: Token)
  {
    predicate is_valid() {
      && token.val == SharedHandle(SharedObtained(t, b))
    }

    predicate is_handle(key: Key) {
      && b.is_handle(key)
      && is_valid()
    }
  }

  glinear method perform_TakeWriteback(glinear c: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires c.val.M?
  requires var m := c.val;
    && m.central.CentralState?
    && m.central.flag == Available
    && m == CentralHandle(m.central)
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := Writeback))
  ensures handle'.val == WritebackHandle(WritebackObtained(c.val.central.stored_value))
  {
    var a := CentralHandle(c.val.central.(flag := Writeback));
    var b := WritebackHandle(WritebackObtained(c.val.central.stored_value));
    TakeWriteback_Preserves(c.val, dot(a, b));
    c', handle' := T.internal_transition_1_2(c, a, b);
  }

  glinear method pre_ReleaseWriteback(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires c.val.M? && handle.val.M?
  requires var m := c.val;
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.writeback.WritebackObtained?
    && m == WritebackHandle(m.writeback)
  requires c.loc == handle.loc
  ensures c.val == c'.val && handle'.val == handle.val
  ensures c.loc == c'.loc && handle'.loc == handle.loc
  ensures c.val.central.flag == Writeback
       || c.val.central.flag == Writeback_PendingExcLock
       || c.val.central.flag == Writeback_Claimed
  {
    c' := c;
    handle' := handle;
    ghost var rest := T.obtain_invariant_2(inout c', inout handle');
  }

  glinear method perform_ReleaseWriteback(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.writeback.WritebackObtained?
    && m == WritebackHandle(m.writeback)
  requires c.loc == handle.loc
  ensures c'.loc == c.loc
  ensures c.val.central.flag == Writeback
       || c.val.central.flag == Writeback_PendingExcLock
       || c.val.central.flag == Writeback_Claimed
  ensures c.val.central.flag == Writeback ==>
      c'.val == CentralHandle(c.val.central.(flag := Available))
  ensures c.val.central.flag == Writeback_PendingExcLock ==>
      c'.val == CentralHandle(c.val.central.(flag := PendingExcLock))
  ensures c.val.central.flag == Writeback_Claimed ==>
      c'.val == CentralHandle(c.val.central.(flag := Claimed))
  {
    var a := CentralHandle(c.val.central.(flag :=
            if c.val.central.flag == Writeback
            then Available
            else
              if c.val.central.flag == Writeback_PendingExcLock
              then PendingExcLock
              else Claimed));
    ReleaseWriteback_Preserves(dot(c.val, handle.val), a);
    glinear var c1, handle1 := pre_ReleaseWriteback(c, handle);
    c' := T.internal_transition_2_1(c1, handle1, a);
  }

  glinear method perform_ThreadlessClaim(glinear c: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m.central.flag == Available
    && m == CentralHandle(m.central)
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag :=
      if c.val.central.flag == Available then Claimed else Writeback_Claimed))
  ensures handle'.val == ExcHandle(ExcClaim(-1, c.val.central.stored_value))
  {
    var a := CentralHandle(c.val.central.(flag :=
      if c.val.central.flag == Available then Claimed else Writeback_Claimed));
    var b := ExcHandle(ExcClaim(-1, c.val.central.stored_value));
    ThreadlessClaim_Preserves(c.val, dot(a, b));
    c', handle' := T.internal_transition_1_2(c, a, b);
  }

  glinear method perform_SharedToClaim(glinear c: Token, glinear handle: Token,
      ghost ss: SharedState)
  returns (glinear c': Token, glinear handle': Token)
  requires ss.SharedObtained?
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m.central.flag != Claimed
    && m.central.flag != Writeback_Claimed
    && m.central.flag != Writeback_PendingExcLock
    && m.central.flag != PendingExcLock
    && m.central.flag != ExcLock_Clean
    && m.central.flag != ExcLock_Dirty
    && m == CentralHandle(m.central)
  requires handle.val == SharedHandle(ss)
  requires c.loc == handle.loc
  ensures (c.val.central.flag == Available || c.val.central.flag == Writeback)
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := 
          if c.val.central.flag == Available then Claimed else Writeback_Claimed))
  ensures handle'.val == ExcHandle(ExcClaim(ss.t, ss.b))
  {
    var a := CentralHandle(c.val.central.(flag := 
          if c.val.central.flag == Available then Claimed else Writeback_Claimed));
    var b := ExcHandle(ExcClaim(ss.t, ss.b));
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    SharedToClaim_Preserves(dot(c.val, handle.val), dot(a, b), ss);
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_ClaimToShared(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcClaim?
    && m.exc.t != -1
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures c.val.central.flag == Writeback_Claimed
       || c.val.central.flag == Claimed
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := 
          if c.val.central.flag == Writeback_Claimed then Writeback else Available))
  ensures handle'.val == SharedHandle(SharedObtained(handle.val.exc.t, handle.val.exc.b))
  {
    var a := CentralHandle(c.val.central.(flag := 
          if c.val.central.flag == Writeback_Claimed then Writeback else Available));
    var b := SharedHandle(SharedObtained(handle.val.exc.t, handle.val.exc.b));
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    ClaimToShared_Preserves(dot(c.val, handle.val), dot(a, b));
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_ClaimToPending(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcClaim?
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures c.val.central.flag == Writeback_Claimed || c.val.central.flag == Claimed
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag :=
      if c.val.central.flag == Writeback_Claimed then Writeback_PendingExcLock else PendingExcLock))
  ensures handle'.val == ExcHandle(ExcPendingAwaitWriteback(handle.val.exc.t, handle.val.exc.b))
  {
    var a := CentralHandle(c.val.central.(flag :=
      if c.val.central.flag == Writeback_Claimed then Writeback_PendingExcLock else PendingExcLock));
    var b := ExcHandle(ExcPendingAwaitWriteback(handle.val.exc.t, handle.val.exc.b));
    ClaimToPending_Preserves(dot(c.val, handle.val), dot(a, b));
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_TakeExcLockFinishWriteback(glinear c: Token, glinear handle: Token, ghost clean: bool)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m.central.flag != Writeback && m.central.flag != Writeback_PendingExcLock
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPendingAwaitWriteback?
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures c.val.central.flag == PendingExcLock
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == 
      CentralHandle(c.val.central.(flag :=
        if clean then ExcLock_Clean else ExcLock_Dirty))
  ensures handle'.val == 
      ExcHandle(ExcPending(handle.val.exc.t, 0, clean, handle.val.exc.b))
  {
    var a := CentralHandle(c.val.central.(flag :=
        if clean then ExcLock_Clean else ExcLock_Dirty));
    var b := ExcHandle(ExcPending(handle.val.exc.t, 0, clean, handle.val.exc.b));
    TakeExcLockFinishWriteback_Preserves(dot(c.val, handle.val), dot(a, b), clean);
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_TakeExcLockCheckRefCount(glinear handle: Token, glinear rc: Token)
  returns (glinear handle': Token, glinear rc': Token)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPending?
    && m == ExcHandle(m.exc)
    && 0 <= m.exc.visited < RC_WIDTH as int
  requires var expected_rc := (if handle.val.exc.visited == handle.val.exc.t then 1 else 0);
    && rc.val == RefCount(handle.val.exc.visited, expected_rc)
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

  glinear method perform_ReadingIncCount(glinear handle: Token, glinear rc: Token, ghost t: int)
  returns (glinear handle': Token, glinear rc': Token)
  requires handle.val == ReadHandle(ReadPending)
  requires var m := rc.val;
      && m.M?
      && t in m.refCounts
      && 0 <= t < RC_WIDTH as int
      && m == RefCount(t, m.refCounts[t])
  requires handle.loc == rc.loc
  ensures rc'.loc == handle'.loc == rc.loc
  ensures handle'.val == ReadHandle(ReadPendingCounted(t))
  ensures rc'.val == RefCount(t, rc.val.refCounts[t] + 1)
  {
    var a := ReadHandle(ReadPendingCounted(t));
    var b := RefCount(t, rc.val.refCounts[t] + 1);
    ReadingIncCount_Preserves(dot(handle.val, rc.val), dot(a, b), t);
    handle', rc' := T.internal_transition_2_2(handle, rc, a, b);
  }

  glinear method perform_ObtainReading(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.read.ReadPendingCounted?
    && m == ReadHandle(m.read)
  requires c.loc == handle.loc
  ensures c.val.central.flag == Reading_ExcLock
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := Reading))
  ensures handle'.val == ReadHandle(ReadObtained(handle.val.read.t))
  {
    var a := CentralHandle(c.val.central.(flag := Reading));
    var b := ReadHandle(ReadObtained(handle.val.read.t));
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    ObtainReading_Preserves(dot(c.val, handle.val), dot(a, b));
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
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
    && m.central.CentralState?
    && (m.central.flag == Available
        || m.central.flag == Writeback
        || m.central.flag == Claimed
        || m.central.flag == Writeback_Claimed
        || m.central.flag == Reading)
    && m == CentralHandle(m.central)
  requires handle.val == SharedHandle(SharedPending(t))
  requires c.loc == handle.loc
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == c.val
  ensures handle'.val == SharedHandle(SharedPending2(t))
  {
    var a := c.val;
    var b := SharedHandle(SharedPending2(t));
    SharedCheckExc_Preserves(dot(c.val, handle.val), dot(a, b), t);
    c', handle' := T.internal_transition_2_2(c, handle, a, b);
  }

  glinear method possible_flags_SharedPending2(
      glinear c: Token, glinear handle: Token, ghost t: int)
  returns (glinear c': Token, glinear handle': Token)
  requires 0 <= t < RC_WIDTH as int
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires handle.val == SharedHandle(SharedPending2(t))
  requires c.loc == handle.loc
  ensures c' == c
  ensures handle' == handle
  ensures c.val.central.flag != Unmapped
  {
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
  }


  glinear method perform_SharedCheckReading(glinear c: Token, glinear handle: Token, ghost t: int)
  returns (glinear c': Token, glinear handle': Token)
  requires 0 <= t < RC_WIDTH as int
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m.central.flag != Reading
    && m.central.flag != Reading_ExcLock
    && m == CentralHandle(m.central)
  requires handle.val == SharedHandle(SharedPending2(t))
  requires c.loc == handle.loc
  ensures c.val.central.flag != Unmapped
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == c.val
  ensures handle'.val == SharedHandle(SharedObtained(t, c.val.central.stored_value))
  {
    var a := c.val;
    var b := SharedHandle(SharedObtained(t, c.val.central.stored_value));
    SharedCheckReading_Preserves(dot(c.val, handle.val), dot(a, b), t);
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_AbandonExcPending(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPending?
    && m.exc.t == -1
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures handle.val.exc.clean ==> c.val.central.flag == ExcLock_Clean
  ensures !handle.val.exc.clean ==> c.val.central.flag == ExcLock_Dirty
  ensures c'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := Available))
  {
    var a := CentralHandle(c.val.central.(flag := Available));
    AbandonExcPending_Preserves(dot(c.val, handle.val), a);
    c' := c;
    glinear var handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c' := T.internal_transition_2_1(c', handle', a);
  }

  glinear method perform_MarkDirty(glinear c: Token, glinear handle: Token)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcObtained?
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures c'.loc == c.loc
  ensures c.val.central.flag == ExcLock_Dirty || c.val.central.flag == ExcLock_Clean
  ensures c'.val == CentralHandle(c.val.central.(flag := ExcLock_Dirty))
  ensures handle'.loc == handle.loc
  ensures handle'.val == ExcHandle(handle.val.exc.(clean := false))
  {
    var a := CentralHandle(c.val.central.(flag := ExcLock_Dirty));
    var b := ExcHandle(handle.val.exc.(clean := false));
    MarkDirty_Preserves(dot(c.val, handle.val), dot(a, b));
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.internal_transition_2_2(c', handle', a, b);
  }

  glinear method perform_Withdraw_TakeExcLockFinish(glinear handle: Token)
  returns (glinear handle': Token, glinear b': Handle)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcPending?
    && m.exc.visited == RC_WIDTH as int
    && m == ExcHandle(m.exc)
  ensures handle'.loc == handle.loc
  ensures handle'.val == ExcHandle(ExcObtained(handle.val.exc.t, handle.val.exc.clean))
  ensures b' == handle.val.exc.b
  {
    var a := ExcHandle(ExcObtained(handle.val.exc.t, handle.val.exc.clean));
    var d := handle.val.exc.b;
    Withdraw_TakeExcLockFinish_Preserves(handle.val, a, d);
    handle', b' := T.withdraw_1_1(handle, a, d);
  }

  glinear method perform_Withdraw_Alloc(glinear c: Token)
  returns (glinear c': Token, glinear handle': Token, glinear b': Handle)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m.central.flag == Unmapped
    && m == CentralHandle(m.central)
  ensures handle'.loc == c'.loc == c.loc
  ensures c'.val == CentralHandle(c.val.central.(flag := Reading_ExcLock))
  ensures handle'.val == ReadHandle(ReadPending)
  ensures b' == c.val.central.stored_value
  {
    var a := CentralHandle(c.val.central.(flag := Reading_ExcLock));
    var d := ReadHandle(ReadPending);
    var e := c.val.central.stored_value;
    Withdraw_Alloc_Preserves(c.val, dot(a, d), e);
    c', handle', b' := T.withdraw_1_2(c, a, d, e);
  }

  glinear method perform_Deposit_DowngradeExcLockToClaim(
      glinear c: Token, glinear handle: Token, glinear b: Handle)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcObtained?
    && 0 <= m.exc.t < RC_WIDTH as int
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures handle.val.exc.clean ==> c.val.central.flag == ExcLock_Clean
  ensures !handle.val.exc.clean ==> c.val.central.flag == ExcLock_Dirty
  ensures handle'.loc == c'.loc == c.loc
  ensures c'.val == 
      CentralHandle(c.val.central
        .(flag := Claimed)
        .(stored_value := b)
      )
  ensures handle'.val ==
      ExcHandle(ExcClaim(handle.val.exc.t, b))
  {
    var a := CentralHandle(c.val.central
        .(flag := Claimed)
        .(stored_value := b)
      );
    var d := ExcHandle(ExcClaim(handle.val.exc.t, b));
    Deposit_DowngradeExcLockToClaim_Preserves(dot(c.val, handle.val), dot(a, d), b);
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.deposit_2_2(c', handle', b, a, d);
  }

  glinear method perform_Deposit_ReadingToShared(
      glinear c: Token, glinear handle: Token, glinear b: Handle)
  returns (glinear c': Token, glinear handle': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.read.ReadObtained?
    && m.read.t != -1
    && m == ReadHandle(m.read)
  requires c.loc == handle.loc
  ensures handle'.loc == c'.loc == c.loc
  ensures c.val.central.flag == Reading
  ensures c'.val == 
      CentralHandle(c.val.central.(flag := Available).(stored_value := b))
  ensures handle'.val ==
      SharedHandle(SharedObtained(handle.val.read.t, b))
  {
    var a := CentralHandle(c.val.central.(flag := Available).(stored_value := b));
    var d := SharedHandle(SharedObtained(handle.val.read.t, b));
    Deposit_ReadingToShared_Preserves(dot(c.val, handle.val), dot(a, d), b);
    c' := c;
    handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c', handle' := T.deposit_2_2(c', handle', b, a, d);
  }

  glinear method perform_Deposit_ReadingToDone(
      glinear c: Token, glinear handle: Token, glinear b: Handle)
  returns (glinear c': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.read.ReadObtained?
    && m.read.t == -1
    && m == ReadHandle(m.read)
  requires c.loc == handle.loc
  ensures c'.loc == c.loc
  ensures c.val.central.flag == Reading
  ensures c'.val == 
      CentralHandle(c.val.central.(flag := Available).(stored_value := b))
  {
    var a := CentralHandle(c.val.central.(flag := Available).(stored_value := b));
    Deposit_ReadingToDone_Preserves(dot(c.val, handle.val), a, b);
    c' := c;
    glinear var handle' := handle;
    var rest := T.obtain_invariant_2(inout c', inout handle');
    c' := T.deposit_2_1(c', handle', b, a);
  }

  glinear method perform_Deposit_Unmap(
      glinear c: Token, glinear handle: Token, glinear b: Handle)
  returns (glinear c': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.exc.ExcObtained?
    && m.exc.t == -1
    && m == ExcHandle(m.exc)
  requires c.loc == handle.loc
  ensures c'.loc == c.loc
  ensures c'.val == 
    CentralHandle(
      c.val.central.(flag := Unmapped).(stored_value := b)
    )
  {
    var a := CentralHandle(c.val.central.(flag := Unmapped).(stored_value := b));
    Deposit_Unmap_Preserves(dot(c.val, handle.val), a, b);
    c' := T.deposit_2_1(c, handle, b, a);
  }

  glinear method perform_Deposit_AbandonReadPending(
      glinear c: Token, glinear handle: Token, glinear b: Handle)
  returns (glinear c': Token)
  requires var m := c.val;
    && m.M?
    && m.central.CentralState?
    && m == CentralHandle(m.central)
  requires var m := handle.val;
    && m.M?
    && m.read.ReadPending?
    && m == ReadHandle(m.read)
  requires c.loc == handle.loc
  ensures c'.loc == c.loc
  ensures c'.val == 
    CentralHandle(c.val.central.(flag := Unmapped).(stored_value := b))
  {
    var a := CentralHandle(c.val.central.(flag := Unmapped).(stored_value := b));
    Deposit_AbandonReadPending_Preserves(dot(c.val, handle.val), a, b);
    c' := T.deposit_2_1(c, handle, b, a);
  }

  function method {:opaque} borrow_wb(gshared f: Token) : (gshared b: Handle)
  requires f.val.M?
  requires f.val.writeback.WritebackObtained?
  ensures b == f.val.writeback.b
  /*{
    ghost var b := Base.one(f.val.writeback.b);
    Base.unwrap_borrow( borrow_back_interp_exact(f, b) )
  }*/

  function method {:opaque} borrow_sot(gshared sot: SharedObtainedToken) : (gshared b: Handle)
  requires sot.is_valid()
  ensures b == sot.b

  glinear method perform_Init(glinear b: Handle)
  returns (glinear central: Token, glinear rcs: Token)
  ensures central.loc == rcs.loc
  ensures central.val == CentralHandle(CentralState(Unmapped, b))
  ensures rcs.val == Rcs(0, RC_WIDTH as int)

  glinear method pop_rcs(glinear t: Token, ghost a: nat, ghost b: nat)
  returns (glinear x: Token, glinear t': Token)
  requires a < b
  requires t.val == Rcs(a, b)
  ensures t'.val == Rcs(a+1, b)
  ensures x.val == RefCount(a, 0)
  ensures x.loc == t'.loc == t.loc
}
*/
