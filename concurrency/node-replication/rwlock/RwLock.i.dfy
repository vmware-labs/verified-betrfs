include "../../framework/Rw.i.dfy"
include "../../scache/rwlock/FullMap.i.dfy"
include "Handle.i.dfy"
include "../Constants.i.dfy"
include "../../../lib/Base/Option.s.dfy"

module RwLock(contentsTypeMod: ContentsTypeMod) refines Rw {
  import opened FullMaps
  import opened NativeTypes
  import opened Constants
  import HandleTypeMod = Handle(contentsTypeMod)

  type ThreadId = nat

  type StoredType = HandleTypeMod.Handle

  // Flags
  // A "flag" is heap state stored "near" the protected StoredType (cell or reference).

  // ExclusiveFlag is the flag set by a thread that then is pending or has
  // obtained exclusiveFlag access.
  // There is always exactly one of these somewhere in the complete monoid giving the value
  // of the flag.
  datatype ExclusiveFlag =
    | ExclusiveFlagUnknown  // Not known in this monoid shard
    | ExclusiveFlag(acquired: bool, stored_value: StoredType)

  // SharedFlags is the map of reference counts (one per thread id) set by a
  // thread that then is pending or has obtained shared access.
  // There may be none of these in the complete monoid; that corresponds to
  // every thread's refcount being zero.
  type SharedFlags = map<ThreadId, nat>

  // AcquisitionState
  // An "acquisition state" is the thread-local state of a thread participating in this
  // instance of the locking protocol. The values of these states cover some subset of
  // threads.

  // State of a thread acquiring exclusiveFlag access.
  // If no thread in the covered subset is trying, the value is ExcAcqNotAttempting.
  // If some thread is trying, the value is ExcAcqPending, or if it has obtained the
  // exclusiveFlag lock, the value is ExcAcqObtained.
  // The protocol enforces (by access to the ExclusiveFlag) that no subset of
  // threads can have more than one thread in {Pending, Obtained} simultaneously.
  datatype ExclusiveAcquisitionState =
    | ExcAcqNotAttempting  // no thread in this shard is attempting to acquire exclusively
    | ExcAcqPending(ghost visited: int, ghost b: StoredType)
    | ExcAcqObtained

  // State of threads acquiring shared access.
  // SharedAcqPending(t) means thread t is known to be in the pending phase of the protocol.
  // SharedAcqObtained (t) means thread t is known to have obtained shared access.
  datatype SharedAcquisitionStatus =
    | SharedAcqPending(ghost t: int)
    | SharedAcqObtained(ghost t: int, b: StoredType)

  // The number of acquisitions for each thread. If monoid represents thread t,
  // and no elements of the multiset mention t, then t is not Pending or
  // Obtained shared access. (Note that the multiset may contain multiple entries
  // because a logical "thread id" in this world might be an equivalence class
  // of physical threads or asynchronous continuations.)
// Dafny module bug: this type synonym works in this module, but fails when imported from RwLockToken with:
// Error: type parameter (K) passed to type FullMap must support equality (got SharedAcquisitionStatus)
//  type SharedAcquisitionState = FullMap<SharedAcquisitionStatus>
//  type SharedAcquisitionState = multiset<SharedAcquisitionStatus> // TODO FullMap->multiset

  datatype M = M(
    // lock protocol state stored in the heap allocation for this instance
    ghost exclusiveFlag: ExclusiveFlag,
    ghost sharedFlags: SharedFlags,

    // lock protocol state "stored in" stack frames of participating threads
    ghost exclusiveAcquisition: ExclusiveAcquisitionState,
    ghost sharedAcquisition: FullMap<SharedAcquisitionStatus>
  ) | Fail

  function unit() : M
  {
    M(ExclusiveFlagUnknown, map[], ExcAcqNotAttempting,
      zero_map()
//      multiset{}  // TODO FullMap->multiset
      )
  }

  function dot(x: M, y: M) : M
  {
    if
      x.M? && y.M?
      && !(x.exclusiveFlag.ExclusiveFlag? && y.exclusiveFlag.ExclusiveFlag?)
      && x.sharedFlags.Keys !! y.sharedFlags.Keys
      && (x.exclusiveAcquisition.ExcAcqNotAttempting? || y.exclusiveAcquisition.ExcAcqNotAttempting?)
    then
      M(
        if x.exclusiveFlag.ExclusiveFlag? then x.exclusiveFlag else y.exclusiveFlag,
        x.sharedFlags + y.sharedFlags,
        if !x.exclusiveAcquisition.ExcAcqNotAttempting? then x.exclusiveAcquisition else y.exclusiveAcquisition,
        add_fns(x.sharedAcquisition, y.sharedAcquisition)
//        x.sharedAcquisition + y.sharedAcquisition // TODO FullMap->multiset
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

  function IsSharedRefFor(t: int) : (SharedAcquisitionStatus) -> bool
  {
    (ss: SharedAcquisitionStatus) => ss.t == t
  }

//  // TODO FullMap->multiset
//  // TODO into a library
//  function MultisetFilter<K(!new)>(selectfn: (K) -> bool, m: multiset<K>) : (rc:multiset<K>)
//    ensures forall k :: k in rc <==> selectfn(k) && k in m
//    ensures forall k | k in rc :: rc[k]==m[k]
//  {
//    if |m|==0
//    then m
//    else
//      var elt :| elt in m;
//      var smaller := m[elt := 0];
//      if selectfn(elt)
//      then
//        MultisetFilter(selectfn, smaller)[elt := m[elt]]
//      else
//        smaller
//  }
//
//  function MultisetSumFilter<K(!new)>(fn: (K) -> bool, m: multiset<K>) : nat
//  {
//    |MultisetFilter(fn, m)|
//  }

  function CountSharedRefs(m: FullMap<SharedAcquisitionStatus>, t: int) : nat
  {
    SumFilter(IsSharedRefFor(t), m)
  }

  function CountAllRefs(state: M, t: int) : nat
  requires state.M?
  {
    CountSharedRefs(state.sharedAcquisition, t)
  }

  // Invariant over the complete monoid
  predicate Inv(x: M)
  {
    && x != unit() ==> (
      && x.M?
      && x.exclusiveFlag.ExclusiveFlag?
      && (x.exclusiveAcquisition.ExcAcqPending? ==>
        && 0 <= x.exclusiveAcquisition.visited <= RC_WIDTH as int
        && x.exclusiveAcquisition.b == x.exclusiveFlag.stored_value
      )
      && (forall t | 0 <= t < RC_WIDTH as int
        :: t in x.sharedFlags && x.sharedFlags[t] == CountAllRefs(x, t))

      && (!x.exclusiveFlag.acquired ==>
        && x.exclusiveAcquisition.ExcAcqNotAttempting?
      )
      && (x.exclusiveFlag.acquired ==>
        && (x.exclusiveAcquisition.ExcAcqPending? || x.exclusiveAcquisition.ExcAcqObtained?)
      )
      && (forall ss: SharedAcquisitionStatus :: x.sharedAcquisition.m[ss] > 0 ==>
        && 0 <= ss.t < RC_WIDTH as int
        && (ss.SharedAcqObtained? ==>
          && ss.b == x.exclusiveFlag.stored_value
          && !x.exclusiveAcquisition.ExcAcqObtained?
          && (x.exclusiveAcquisition.ExcAcqPending? ==> x.exclusiveAcquisition.visited <= ss.t)
        )
      )
    )
  }

  // Interpretation of the complete monoid
  function I(x: M) : Option<StoredType>
  //requires Inv(x)
  {
    if !x.M? || x == unit() || x.exclusiveAcquisition.ExcAcqObtained? then (
      None
    ) else (
      Some(x.exclusiveFlag.stored_value)
    )
  }

  function dot3(a: M, b: M, c: M) : M
  {
    dot(dot(a, b), c)
  }

  ////// A "Handle" is a single-serving slice of monoid; a minimal non-trivial fact.

  function ExcFlagHandle(exclusiveFlag: ExclusiveFlag) : M {
    M(exclusiveFlag, map[], ExcAcqNotAttempting, zero_map())
  }

  function SharedFlagHandle(t: ThreadId, count: nat) : M {
    M(ExclusiveFlagUnknown, map[t := count], ExcAcqNotAttempting, zero_map())
  }

  function ExcAcqHandle(e: ExclusiveAcquisitionState) : M {
    M(ExclusiveFlagUnknown, map[], e, zero_map())
  }

  function SharedAcqHandle(ss: SharedAcquisitionStatus) : M {
    M(ExclusiveFlagUnknown, map[], ExcAcqNotAttempting, unit_fn(ss))
  }

  function RefCount(t: nat, n: nat) : M {
    M(ExclusiveFlagUnknown, map[t := n], ExcAcqNotAttempting, zero_map())
  }

  ////// Transitions

  //
  // acquire transitions
  //

  predicate ExcBegin(m: M, m': M)
  {
    && m.M?
    && m.exclusiveFlag.ExclusiveFlag?
    && !m.exclusiveFlag.acquired

    && m == ExcFlagHandle(m.exclusiveFlag)
    && m' == dot(
      ExcFlagHandle(m.exclusiveFlag.(acquired := true)),
      ExcAcqHandle(ExcAcqPending(0, m.exclusiveFlag.stored_value))
    )
  }

  lemma ExcBegin_Preserves(m: M, m': M)
  requires ExcBegin(m, m')
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert dot(m', p).sharedAcquisition == dot(m, p).sharedAcquisition;
    }
  }

  predicate TakeExcLockCheckRefCount(m: M, m': M)
  {
    && m.M?
    && m.exclusiveAcquisition.ExcAcqPending?
    && m.exclusiveAcquisition.visited in m.sharedFlags
    && 0 <= m.exclusiveAcquisition.visited < RC_WIDTH as int

    && m == dot(
      ExcAcqHandle(m.exclusiveAcquisition),
      SharedFlagHandle(m.exclusiveAcquisition.visited, 0)
    )
    && m' == dot(
      ExcAcqHandle(m.exclusiveAcquisition.(visited := m.exclusiveAcquisition.visited + 1)),
      SharedFlagHandle(m.exclusiveAcquisition.visited, 0)
    )
  }

  lemma TakeExcLockCheckRefCount_Preserves(m: M, m': M)
  requires TakeExcLockCheckRefCount(m, m')
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert dot(m', p).sharedAcquisition == dot(m, p).sharedAcquisition;
      //assert dot(m, p).sharedFlags[m.exclusiveAcquisition.visited] == 0;
      assert CountAllRefs(dot(m, p), m.exclusiveAcquisition.visited) == 0;
      assert CountSharedRefs(dot(m, p).sharedAcquisition, m.exclusiveAcquisition.visited) == 0;
      UseZeroSum(IsSharedRefFor(m.exclusiveAcquisition.visited), dot(m, p).sharedAcquisition);
    }
  }

  predicate Withdraw_TakeExcLockFinish(m: M, m': M, b': StoredType)
  {
    && m.M?
    && m.exclusiveAcquisition.ExcAcqPending?
    && m.exclusiveAcquisition.visited == RC_WIDTH as int
    && m == ExcAcqHandle(m.exclusiveAcquisition)
    && m' == ExcAcqHandle(ExcAcqObtained)
    && b' == m.exclusiveAcquisition.b
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
      assert dot(m', p).sharedAcquisition == dot(m, p).sharedAcquisition;
    }
  }

  //
  // release transitions
  //

  predicate Deposit_ReleaseExcLock(m: M, m': M, b: StoredType)
  {
    && m.M?
    && m.exclusiveAcquisition.ExcAcqObtained?
    && m.exclusiveFlag.ExclusiveFlag?
    && m == dot(
      ExcFlagHandle(m.exclusiveFlag),
      ExcAcqHandle(m.exclusiveAcquisition)
    )
    && m' ==
      ExcFlagHandle(m.exclusiveFlag
        .(acquired := false)
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
      SumFilterSimp<SharedAcquisitionStatus>();
      assert forall b :: dot(m', p).sharedAcquisition.m[b] == dot(m, p).sharedAcquisition.m[b];

      var state' := dot(m', p);
      forall ss: SharedAcquisitionStatus | state'.sharedAcquisition.m[ss] > 0
      ensures 0 <= ss.t < RC_WIDTH as int
      ensures (ss.SharedAcqObtained? ==> ss.b == state'.exclusiveFlag.stored_value)
      {
      }
    }
  }

  //
  // acquire_shared transitions
  //

  predicate SharedIncCount(m: M, m': M, t: int)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == SharedFlagHandle(t, m.sharedFlags[t])
    && m' == dot(
      SharedFlagHandle(t, m.sharedFlags[t] + 1),
      SharedAcqHandle(SharedAcqPending(t))
    )
  }

  lemma SharedIncCount_Preserves(m: M, m': M, t: int)
  requires SharedIncCount(m, m', t)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      SumFilterSimp<SharedAcquisitionStatus>();
      var state := dot(m, p);
      var state' := dot(m', p);
      forall t0 | 0 <= t0 < RC_WIDTH as int
      ensures t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0)
      {
        if t == t0 {
          assert CountSharedRefs(state.sharedAcquisition, t) + 1
              == CountSharedRefs(state'.sharedAcquisition, t);
          assert CountAllRefs(state, t) + 1
              == CountAllRefs(state', t);
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        } else {
          assert CountSharedRefs(state.sharedAcquisition, t0) == CountSharedRefs(state'.sharedAcquisition, t0);
          assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        }
      }
    }
  }

  // decide whether we obtain or abandon.
  predicate SharedCheckExc(m: M, m': M, t: int)
  {
    && m.M?
    //&& 0 <= t < RC_WIDTH as int
    && m.exclusiveFlag.ExclusiveFlag?
    && !m.exclusiveFlag.acquired
    && m == dot(
      ExcFlagHandle(m.exclusiveFlag),
      SharedAcqHandle(SharedAcqPending(t))
    )
    && m' == dot(
      ExcFlagHandle(m.exclusiveFlag),
      SharedAcqHandle(SharedAcqObtained(t, m.exclusiveFlag.stored_value))
    )
  }

  lemma SharedCheckExc_Preserves(m: M, m': M, t: int)
  requires SharedCheckExc(m, m', t)
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      SumFilterSimp<SharedAcquisitionStatus>();

      var state := dot(m, p);
      var state' := dot(m', p);

      assert CountAllRefs(state, t) == CountAllRefs(state', t);
      //assert forall t0 | t0 != t :: CountAllRefs(state, t) == CountAllRefs(state', t);
    }
  }

  // abandon this acquisition attempt. Rats!
  predicate SharedDecCountPending(m: M, m': M, t: int)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == dot(
      SharedFlagHandle(t, m.sharedFlags[t]),
      SharedAcqHandle(SharedAcqPending(t))
    )
    && (m.sharedFlags[t] >= 1 ==>
      m' == SharedFlagHandle(t, m.sharedFlags[t] - 1)
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

      SumFilterSimp<SharedAcquisitionStatus>();

      assert state.sharedFlags[t] >= 1 by {
        if state.sharedFlags[t] == 0 {
          assert CountAllRefs(state, t) == 0;
          assert CountSharedRefs(state.sharedAcquisition, t) == 0;
          UseZeroSum(IsSharedRefFor(t), state.sharedAcquisition);
          assert false;
        }
      }

      var state' := dot(m', p);

      forall t0 | 0 <= t0 < RC_WIDTH as int
      ensures t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0)
      {
        if t == t0 {
          assert CountSharedRefs(state.sharedAcquisition, t)
              == CountSharedRefs(state'.sharedAcquisition, t) + 1;
          assert CountAllRefs(state, t)
              == CountAllRefs(state', t) + 1;
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        } else {
          assert CountSharedRefs(state.sharedAcquisition, t0) == CountSharedRefs(state'.sharedAcquisition, t0);
          assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        }
      }
    }
  }

  //
  // acquire_release transitions
  //

  predicate SharedDecCountObtained(m: M, m': M, t: int, b: StoredType)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == dot(
      SharedFlagHandle(t, m.sharedFlags[t]),
      SharedAcqHandle(SharedAcqObtained(t, b))
    )
    && (m.sharedFlags[t] >= 1 ==>
      m' == SharedFlagHandle(t, m.sharedFlags[t] - 1)
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

      SumFilterSimp<SharedAcquisitionStatus>();

      assert state.sharedFlags[t] >= 1 by {
        if state.sharedFlags[t] == 0 {
          assert CountAllRefs(state, t) == 0;
          assert CountSharedRefs(state.sharedAcquisition, t) == 0;
          UseZeroSum(IsSharedRefFor(t), state.sharedAcquisition);
          assert false;
        }
      }

      var state' := dot(m', p);

      forall t0 | 0 <= t0 < RC_WIDTH as int
      ensures t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0)
      {
        if t == t0 {
          assert CountSharedRefs(state.sharedAcquisition, t)
              == CountSharedRefs(state'.sharedAcquisition, t) + 1;
          assert CountAllRefs(state, t)
              == CountAllRefs(state', t) + 1;
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        } else {
          assert CountSharedRefs(state.sharedAcquisition, t0) == CountSharedRefs(state'.sharedAcquisition, t0);
          assert CountAllRefs(state, t0) == CountAllRefs(state', t0);
          assert t0 in state'.sharedFlags && state'.sharedFlags[t0] == CountAllRefs(state', t0);
        }
      }
    }
  }

  //////// Lock initializations

//  function Rcs(s: nat, t: nat) : M
//  requires s <= t
//  decreases t - s
//  {
//    if t == s then
//      unit()
//    else
//      dot(SharedFlagHandle(s, 0), Rcs(s+1, t))
//  }

  predicate Init(s: M)
  {
    && s.M?
    && s.exclusiveFlag.ExclusiveFlag?
    && s.exclusiveFlag.acquired
    && s.sharedFlags == (map threadId | 0 <= threadId < RC_WIDTH :: 0)
    && s.sharedAcquisition == FullMaps.zero_map()
    && s.exclusiveAcquisition == ExcAcqObtained // client starts out holding the exclusiveAcquisition lock so it can determine the inital value of the lock-protected field.
  }

  // TODO(travis): this used to be a module-refinement-driven obligation, but now it's not. What happened?
  lemma InitImpliesInv(x: M)
  requires Init(x)
//  ensures Inv(x)
//  ensures I(x) == None
  {
    SumFilterSimp<SharedAcquisitionStatus>();
    assert Init(x);
    assert Inv(x);
    assert I(x) == None;
  }

  lemma inv_unit()
  // ensures Inv(unit())
  // ensures I(unit()) == None
  {}

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

module RwLockToken(contentsTypeMod: ContentsTypeMod) {
  import opened Options
  import opened Constants
  import opened RwLock(contentsTypeMod)
  import opened FullMaps
  import HandleTypeMod = Handle(contentsTypeMod)
  import T = RwTokens(RwLock)

  type Token = T.Token
  type Handle = HandleTypeMod.Handle

  glinear method perform_ExcBegin(glinear flagToken: Token)
  returns (glinear flagToken': Token, glinear excAcqToken': Token)
  requires var m := flagToken.val;
    && m.M?
    && m.exclusiveFlag.ExclusiveFlag?
    && !m.exclusiveFlag.acquired
    && m == ExcFlagHandle(m.exclusiveFlag)
  ensures flagToken'.val == ExcFlagHandle(flagToken.val.exclusiveFlag.(acquired := true))
  ensures excAcqToken'.val == ExcAcqHandle(ExcAcqPending(0, flagToken.val.exclusiveFlag.stored_value))
  ensures flagToken'.loc == excAcqToken'.loc == flagToken.loc
  {
    var m := flagToken.val;
    var a := ExcFlagHandle(m.exclusiveFlag.(acquired := true));
    var b := ExcAcqHandle(ExcAcqPending(0, m.exclusiveFlag.stored_value));
    ExcBegin_Preserves(flagToken.val, dot(a, b));
    flagToken', excAcqToken' := T.internal_transition_1_2(flagToken, a, b);
  }

  glinear method perform_TakeExcLockCheckRefCount(glinear handle: Token, glinear rc: Token)
  returns (glinear handle': Token, glinear rc': Token)
  requires var m := handle.val;
    && m.M?
    && m.exclusiveAcquisition.ExcAcqPending?
    && m == ExcAcqHandle(m.exclusiveAcquisition)
    && 0 <= m.exclusiveAcquisition.visited < RC_WIDTH as int
  requires rc.val == SharedFlagHandle(handle.val.exclusiveAcquisition.visited, 0)
  requires rc.loc == handle.loc
  ensures rc'.loc == handle'.loc == rc.loc
  ensures handle'.val == ExcAcqHandle(handle.val.exclusiveAcquisition.(visited := handle.val.exclusiveAcquisition.visited + 1))
  ensures rc'.val == rc.val
  {
    var a := ExcAcqHandle(handle.val.exclusiveAcquisition.(visited := handle.val.exclusiveAcquisition.visited + 1));
    var b := rc.val;
    TakeExcLockCheckRefCount_Preserves(dot(handle.val, rc.val), dot(a, b));
    handle', rc' := T.internal_transition_2_2(handle, rc, a, b);
  }

  glinear method perform_Withdraw_TakeExcLockFinish(glinear handle: Token)
  returns (glinear handle': Token, glinear b': Handle)
  requires var m := handle.val;
    && m.M?
    && m.exclusiveAcquisition.ExcAcqPending?
    && m.exclusiveAcquisition.visited == RC_WIDTH as int
    && m == ExcAcqHandle(m.exclusiveAcquisition)
  ensures handle' == T.T.Token(handle.loc, ExcAcqHandle(ExcAcqObtained))
  ensures b' == handle.val.exclusiveAcquisition.b
  {
    var a := ExcAcqHandle(ExcAcqObtained);
    var d := handle.val.exclusiveAcquisition.b;
    Withdraw_TakeExcLockFinish_Preserves(handle.val, a, d);
    handle', b' := T.withdraw_1_1(handle, a, d);
  }

  predicate IsExcFlagAcquired(m: M)
  {
    && m.M?
    && m.exclusiveFlag.ExclusiveFlag?
    && m == ExcFlagHandle(m.exclusiveFlag)
  }

  predicate IsExcAcqObtained(m: M)
  {
    && m.M?
    && m.exclusiveAcquisition.ExcAcqObtained?
    && m == ExcAcqHandle(m.exclusiveAcquisition)
  }

  glinear method perform_Deposit_ReleaseExcLock(glinear flagToken: Token, glinear excAcqToken: Token, glinear b: Handle)
  returns (glinear flagToken': Token)
  requires flagToken.loc == excAcqToken.loc
  requires IsExcFlagAcquired(flagToken.val)
  requires IsExcAcqObtained(excAcqToken.val)
  ensures flagToken' == T.T.Token(flagToken.loc, ExcFlagHandle(ExclusiveFlag(false, b)))
  {
    ghost var expected_flag' := ExcFlagHandle(ExclusiveFlag(false, b));
    Deposit_ReleaseExcLock_Preserves(dot(flagToken.val, excAcqToken.val), expected_flag', b);
    flagToken' := T.deposit_2_1(flagToken, excAcqToken, b, expected_flag');
  }

  predicate IsSharedFlagHandleForThread(m: M, t: int)
  {
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == SharedFlagHandle(t, m.sharedFlags[t])
  }

  glinear method perform_SharedIncCount(glinear rc: Token, ghost t: int)
  returns (glinear rc': Token, glinear handle': Token)
  requires IsSharedFlagHandleForThread(rc.val, t);
  ensures rc'.loc == handle'.loc == rc.loc
  ensures rc'.val == SharedFlagHandle(t, rc.val.sharedFlags[t] + 1)
  ensures handle'.val == SharedAcqHandle(SharedAcqPending(t))
  {
    var a := SharedFlagHandle(t, rc.val.sharedFlags[t] + 1);
    var b := SharedAcqHandle(SharedAcqPending(t));
    SharedIncCount_Preserves(rc.val, dot(a, b), t);
    rc', handle' := T.internal_transition_1_2(rc, a, b);
  }

  glinear method perform_SharedCheckExc(glinear c: Token, glinear handle: Token, ghost t: int)
  returns (glinear c': Token, glinear handle': Token)
  //requires 0 <= t < RC_WIDTH as int
  requires var m := c.val;
    && m.M?
    && m.exclusiveFlag.ExclusiveFlag?
    && !m.exclusiveFlag.acquired
    && m == ExcFlagHandle(m.exclusiveFlag)
  requires handle.val == SharedAcqHandle(SharedAcqPending(t))
  requires c.loc == handle.loc
  ensures c'.loc == handle'.loc == c.loc
  ensures c'.val == c.val
  ensures handle'.val == SharedAcqHandle(SharedAcqObtained(t, c.val.exclusiveFlag.stored_value))
  {
    var a := c.val;
    var b := SharedAcqHandle(SharedAcqObtained(t, c.val.exclusiveFlag.stored_value));
    SharedCheckExc_Preserves(dot(c.val, handle.val), dot(a, b), t);
    c', handle' := T.internal_transition_2_2(c, handle, a, b);
  }

  glinear method pre_SharedDecCountPending(glinear rc: Token, glinear handle: Token, ghost t: int)
  returns (glinear rc': Token, glinear handle': Token)
  requires rc.val.M?
  requires handle.val.M?
  requires rc.loc == handle.loc
  requires t in rc.val.sharedFlags
  requires handle.val.sharedAcquisition.m[SharedAcqPending(t)] >= 1
  ensures rc.val.sharedFlags[t] >= 1
  ensures handle' == handle
  ensures rc' == rc
  {
    rc' := rc;
    handle' := handle;
    ghost var rest := T.obtain_invariant_2(inout rc', inout handle');
    var m := dot(rc'.val, handle'.val);
    ghost var state := dot(m, rest);
    if CountSharedRefs(state.sharedAcquisition, t) == 0 {
      assert state.sharedAcquisition.m[SharedAcqPending(t)] >= 1;
      FullMaps.UseZeroSum(IsSharedRefFor(t), state.sharedAcquisition);
      assert false;
    }
    assert state.sharedFlags[t] >= 1;
    assert m.sharedFlags[t] == state.sharedFlags[t];
  }

  glinear method perform_SharedDecCountPending(glinear rc: Token, glinear handle: Token, ghost t: int)
  returns (glinear rc': Token)
  requires var m := rc.val;
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == SharedFlagHandle(t, m.sharedFlags[t])
  requires var m := handle.val;
    && m.M?
    && m == SharedAcqHandle(SharedAcqPending(t))
  requires rc.loc == handle.loc
  ensures rc'.loc == rc.loc
  ensures rc.val.sharedFlags[t] >= 1
  ensures rc'.val == SharedFlagHandle(t, rc.val.sharedFlags[t] - 1)
  {
    rc' := rc;
    glinear var handle' := handle;
    rc', handle' := pre_SharedDecCountPending(rc', handle', t);
    var a := SharedFlagHandle(t, rc.val.sharedFlags[t] - 1);
    SharedDecCountPending_Preserves(dot(rc'.val, handle.val), a, t);
    rc' := T.internal_transition_2_1(rc', handle', a);
  }

  glinear method pre_SharedDecCountObtained(glinear rc: Token, glinear handle: Token, ghost t: int, ghost b: StoredType)
  returns (glinear rc': Token, glinear handle': Token)
  requires rc.val.M?
  requires handle.val.M?
  requires rc.loc == handle.loc
  requires t in rc.val.sharedFlags
  requires handle.val.sharedAcquisition.m[SharedAcqObtained(t, b)] >= 1
  ensures rc.val.sharedFlags[t] >= 1
  ensures handle' == handle
  ensures rc' == rc
  {
    rc' := rc;
    handle' := handle;
    ghost var rest := T.obtain_invariant_2(inout rc', inout handle');
    var m := dot(rc'.val, handle'.val);
    ghost var state := dot(m, rest);
    if CountSharedRefs(state.sharedAcquisition, t) == 0 {
      assert state.sharedAcquisition.m[SharedAcqObtained(t, b)] >= 1;
      FullMaps.UseZeroSum(IsSharedRefFor(t), state.sharedAcquisition);
      assert false;
    }
    assert state.sharedFlags[t] >= 1;
    assert m.sharedFlags[t] == state.sharedFlags[t];
  }

  glinear method perform_SharedDecCountObtained(glinear rc: Token, glinear handle: Token,
      ghost t: int, ghost b: StoredType)
  returns (glinear rc': Token)
  requires var m := rc.val;
    && m.M?
    && 0 <= t < RC_WIDTH as int
    && t in m.sharedFlags
    && m == SharedFlagHandle(t, m.sharedFlags[t])
  requires var m := handle.val;
    && m.M?
    && m == SharedAcqHandle(SharedAcqObtained(t, b))
  requires rc.loc == handle.loc
  ensures rc'.loc == rc.loc
  ensures rc.val.sharedFlags[t] >= 1
  ensures rc'.val == SharedFlagHandle(t, rc.val.sharedFlags[t] - 1)
  {
    rc' := rc;
    glinear var handle' := handle;
    rc', handle' := pre_SharedDecCountObtained(rc', handle', t, b);
    var a := SharedFlagHandle(t, rc.val.sharedFlags[t] - 1);
    SharedDecCountObtained_Preserves(dot(rc'.val, handle.val), a, t, b);
    rc' := T.internal_transition_2_1(rc', handle', a);
  }

  lemma ShardAcqObtained_guard(t: nat, b: StoredType)
    ensures guard(SharedAcqHandle(SharedAcqObtained(t, b)), b)
  {
    SumFilterSimp<SharedAcquisitionStatus>();

    var m := SharedAcqHandle(SharedAcqObtained(t, b));
    forall p: M | Inv(dot(m, p))
    ensures I(dot(m, p)) == Some(b)
    {
      var x := dot(m, p);
      assert x != unit() by {
        var ss := SharedAcqObtained(t, b);
        assert x.sharedAcquisition.m[ss] > 0;
        assert unit().sharedAcquisition.m[ss] == 0;
      }
      assert x.exclusiveFlag.stored_value == b;
    }
  }

  glinear method borrow_inner(gshared tok: Token, ghost t: nat, ghost b: StoredType)
  returns (gshared b': StoredType)
  requires tok.val == SharedAcqHandle(SharedAcqObtained(t, b))
  ensures b' == b
  {
    ShardAcqObtained_guard(t, b);
    b' := T.borrow_from_guard(tok, b);
  }

  glinear method perform_Init(glinear b: StoredType)
  returns (glinear excFlagToken: Token, glinear rcs: Token)
  ensures excFlagToken.loc == rcs.loc
  ensures excFlagToken.val == ExcFlagHandle(ExclusiveFlag(false, b))
  ensures rcs.val == Rcs(0, RC_WIDTH as int)
  {
    //reveal_RcRange(); // not sure why we don't need this anymore?
    var x := ExcFlagHandle(ExclusiveFlag(false, b));
    var y := Rcs(0, RC_WIDTH as int);
    var z := dot(x, y);

    forall t | 0 <= t < RC_WIDTH as int
    ensures CountAllRefs(z, t) == 0
    {
      SumFilterSimp<SharedAcquisitionStatus>();
    }

    glinear var tok := T.initialize_nonempty(b, z);
    excFlagToken, rcs := T.T.split(tok, x, y);
  }

  glinear method pop_rcs(glinear t: Token, ghost a: nat, ghost b: nat)
  returns (glinear x: Token, glinear t': Token)
  requires a < b
  requires t.val == Rcs(a, b)
  ensures t'.val == Rcs(a+1, b)
  ensures x.val == RefCount(a, 0)
  ensures x.loc == t'.loc == t.loc

  // crib from scache


//  function method {:opaque} borrow_sot(gshared sot: SharedObtainedToken) : (gshared b: Handle)
//  requires sot.is_valid()
//  ensures b == sot.b
}
