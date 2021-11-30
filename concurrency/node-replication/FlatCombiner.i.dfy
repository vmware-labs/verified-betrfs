include "../framework/AsyncSSM.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "Constants.i.dfy"
include "../framework/Rw.i.dfy"
include "../../lib/Base/Maps.i.dfy"

module FlatCombiner refines Rw {
  import opened RequestIds
  import opened Constants
  import Maps

  type Key(!new) = nat
  type StoredType(!new) = nat

  datatype Elem = Elem(ghost rid: nat)

  datatype FCClientState =
    | FCClientIdle
    | FCClientWaiting(ghost rid: RequestId)

  datatype FCSlotState =
    | FCEmpty
    | FCRequest(ghost rid: RequestId)
    | FCInProgress(ghost rid: RequestId)
    | FCResponse(ghost rid: RequestId)

  datatype FCCombinerState =
    // no 'idle' state - just use Collecting([])
    | FCCombinerCollecting(ghost elems: seq<Option<Elem>>)
    | FCCombinerResponding(ghost elems: seq<Option<Elem>>, ghost idx: nat)

  datatype M = M(
    ghost clients: map<nat, FCClientState>,
    ghost slots: map<nat, FCSlotState>,
    ghost combiner: Option<FCCombinerState>
  ) | Fail


  /*
   * ============================================================================================
   * Invariant
   * ============================================================================================
   */

  predicate ClientsComplete(c: map<nat, FCClientState>) {
    && (forall i : nat | i in c :: 0 <= i < (MAX_THREADS_PER_REPLICA as nat))
    && (forall i : nat | 0 <= i < (MAX_THREADS_PER_REPLICA as nat) :: i in c)
  }

  predicate SlotsComplete(s: map<nat, FCSlotState>) {
    && (forall i : nat | i in s :: 0 <= i < (MAX_THREADS_PER_REPLICA as nat))
    && (forall i : nat | 0 <= i < (MAX_THREADS_PER_REPLICA as nat) :: i in s)
  }

  predicate Complete(x: M) {
    && x.M?
    && x.combiner.Some?
    && ClientsComplete(x.clients)
    && SlotsComplete(x.slots)
  }

  predicate ClientIdle_SlotEmtpy(x: M)
    requires Complete(x)
  {
    // the slot must be empty if the client is idling, and it's not empty if the client is waiting
    && (forall i : nat | i in x.clients :: x.clients[i].FCClientIdle? <==> x.slots[i].FCEmpty?)
  }

  predicate ClientWaiting_RequestId(x: M)
    requires Complete(x)
    requires ClientIdle_SlotEmtpy(x)
  {
    // forall waiting clients, the request id in the slots must match
    && (forall i : nat | i in x.clients && x.clients[i].FCClientWaiting? :: x.clients[i].rid == x.slots[i].rid)
  }

  predicate CombinerState_Elems(x: M)
    requires Complete(x)
  {
    // the number of elements must not exceed the number of threads
    && (|x.combiner.value.elems| <= MAX_THREADS_PER_REPLICA as nat)
    && (x.combiner.value.FCCombinerResponding? ==>
        (&& |x.combiner.value.elems| == MAX_THREADS_PER_REPLICA as nat
        && x.combiner.value.idx <= |x.combiner.value.elems|
        )
      )
  }

  predicate CombinerState_RequestIds(x: M)
    requires Complete(x)
    requires CombinerState_Elems(x)
  {
    match x.combiner.value {
      case FCCombinerCollecting(elems: seq<Option<Elem>>) => (
        forall i : nat | 0 <= i < |x.combiner.value.elems| && x.combiner.value.elems[i].Some? :: (
            x.slots[i].FCInProgress? || x.slots[i].FCResponse? ==> x.slots[i].rid == x.combiner.value.elems[i].value.rid
        )
      )
      case FCCombinerResponding(elems: seq<Option<Elem>>, idx: nat) => (
        forall i : nat | idx <= i < |x.combiner.value.elems| && x.combiner.value.elems[i].Some? :: (
            x.slots[i].FCInProgress? || x.slots[i].FCResponse? ==> x.slots[i].rid == x.combiner.value.elems[i].value.rid
        )
      )
    }
  }

  predicate Inv(x: M) {
    && Complete(x)
    && ClientIdle_SlotEmtpy(x)
    && ClientWaiting_RequestId(x)
    && CombinerState_Elems(x)
    && CombinerState_RequestIds(x)
  }


  /*
   * ============================================================================================
   * Initialization
   * ============================================================================================
   */

  predicate Init(s: M) {
    s == M(
      map x : nat | 0 <= x < (MAX_THREADS_PER_REPLICA as nat) :: x := FCClientIdle,
      map x : nat | 0 <= x < (MAX_THREADS_PER_REPLICA as nat) :: x := FCEmpty,
      Some(FCCombinerCollecting([]))
    )
  }

  lemma InitImpliesInv(x: M)
    requires Init(x)
    ensures Inv(x)
  {
  }

   /*
   * ============================================================================================
   * Dot
   * ============================================================================================
   */

  function dot(x: M, y: M) : M {
    if (
      && x.M?                &&  y.M?
      && !(x.combiner.Some?  &&  y.combiner.Some?)
      && (x.slots.Keys       !!  y.slots.Keys)
      && (x.clients.Keys     !!  y.clients.Keys)
    )
    then
      M(
        Maps.MapUnionPreferB(x.clients, y.clients),
        Maps.MapUnionPreferB(x.slots, y.slots),
        if x.combiner.Some? then x.combiner else y.combiner
      )
    else
      Fail
  }

  function unit() : M {
    M(map[], map[], None)
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
    assert unit().M?;
    assert dot(unit(), unit()).M?;
    assert dot(unit(), unit()) == unit();
    assert dot(x, unit()) == x;
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
    if dot(x, dot(y, z)) == Fail {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }


  /*
   * ============================================================================================
   * Interpretation Function
   * ============================================================================================
   */
  // probably don't need?
  function I(x: M) : Option<StoredType> {
    None
  }


  /*
   * ============================================================================================
   * Guards
   * ============================================================================================
   */

  predicate CombinerValid(m: M) {
    && m.M?
    && m.combiner.Some?
  }

  predicate CombinerIsCollecting(m: M)
    requires CombinerValid(m)
  {
    && m.combiner.value.FCCombinerCollecting?
    && |m.combiner.value.elems| < MAX_THREADS_PER_REPLICA as nat
  }

  predicate CombinerIsCollectingDone(m: M)
    requires CombinerValid(m)
  {
    && m.combiner.value.FCCombinerCollecting?
    && |m.combiner.value.elems| == MAX_THREADS_PER_REPLICA as nat
  }

  predicate CombinerIsResponding(m: M)
    requires CombinerValid(m)
  {
     && m.combiner.value.FCCombinerResponding?
     && m.combiner.value.idx < |m.combiner.value.elems|
  }

  predicate CombinerIsRespondingDone(m: M)
    requires CombinerValid(m)
  {
     && m.combiner.value.FCCombinerResponding?
     && m.combiner.value.idx == |m.combiner.value.elems|
  }

  predicate ClientIdle(m: M, tid: nat)
    requires m.M?
  {
    && tid in m.clients
    && m.clients[tid].FCClientIdle?
  }

  predicate ClientWaiting(m: M, tid:nat)
    requires m.M?
  {
    && tid in m.clients
    && m.clients[tid].FCClientWaiting?
  }

  predicate SlotIsEmpty(m: M, tid: nat)
    requires m.M?
  {
    && tid in m.slots
    && m.slots[tid].FCEmpty?
  }

  predicate SlotHasRequest(m: M, tid: nat)
    requires m.M?
  {
    && tid in m.slots
    && m.slots[tid].FCRequest?
  }

  predicate SlotInProgress(m: M, tid: nat)
    requires m.M?
  {
    && tid in m.slots
    && m.slots[tid].FCRequest?
  }

  predicate SlotHasResponse(m: M, tid: nat)
    requires m.M?
  {
    && tid in m.slots
    && m.slots[tid].FCRequest?
  }

  /*
   * ============================================================================================
   * State Transitions
   * ============================================================================================
   */

  // -------------------------------- fc_initialize ---------------------------------------------

  // TODO?

  // -------------------------------- combiner_collect ------------------------------------------

  // TODO: break the up into two transitions?
  predicate CombinerDoCollectEmpty(m: M, m': M) {
    && m.M?
    && CombinerValid(m)
    && CombinerIsCollecting(m)

    // get the thread id as the current number of elements in the combiner elements
    && var tid := |m.combiner.value.elems|;

    // the slot was empty
    && SlotIsEmpty(m, tid)

    // add a None to the collected elements
    && m' == m.(combiner := Some(FCCombinerCollecting(m.combiner.value.elems + [None])))
  }

  lemma CombinerDoCollectEmpty_is_transition(m: M, m': M)
  requires CombinerDoCollectEmpty(m, m')
  ensures transition(m, m')
  {

  }

  // -------------------------------- combiner_collect ------------------------------------------

  predicate CombinerDoCollectRequest(m: M, m': M) {
    && m.M?
    && CombinerValid(m)
    && CombinerIsCollecting(m)

    // get the thread id as the current number of elements in the combiner elements
    && var tid := |m.combiner.value.elems|;

    // the slot had a request
    && SlotHasRequest(m, tid)

    // mark the slot as in progress, and add the request Id to the elements
    && m' == m.(
      combiner := Some(FCCombinerCollecting(m.combiner.value.elems + [Some(Elem(m.slots[tid].rid))])),
      slots := m.slots[tid := FCInProgress(m.slots[tid].rid)]
    )
  }

  lemma CombinerDoCollectRequest_is_transition(m: M, m': M)
  requires CombinerDoCollectRequest(m, m')
  ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
      ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {

    }
  }


  // -------------------------------- combiner_goto_responding ----------------------------------

  predicate CombinerGoToResponding(m: M, m': M) {
    && m.M?
    && CombinerValid(m)
    && CombinerIsCollectingDone(m)

    // keep the elements, set the index to 0
    && m' == m.(combiner := Some(FCCombinerResponding(m.combiner.value.elems, 0)))
  }

  lemma CombinerGoToResponding_is_transition(m: M, m': M)
    requires CombinerGoToResponding(m, m')
    ensures transition(m, m')
  {

  }


  // -------------------------------- combiner_response_skip ------------------------------------

  predicate CombinerDoResponseSkip(m: M, m': M)
  {
    && m.M?
    && CombinerValid(m)
    && CombinerIsResponding(m)

    // the current thread we're responding to
    && var tid := m.combiner.value.idx;

    // the element was none, so nothing to be done
    && m.combiner.value.elems[tid].None?

    && m' == m.(combiner := Some(FCCombinerResponding(m.combiner.value.elems, tid + 1)))
  }

  lemma CombinerDoResponseSkip_is_transition(m: M, m': M)
    requires CombinerDoResponseSkip(m, m')
    ensures transition(m, m')
  {

  }

  // -------------------------------- combiner_response -----------------------------------------

  predicate CombinerDoResponse(m: M, m': M)
  {
    && m.M?
    && CombinerValid(m)
    && CombinerIsResponding(m)
    // the current thread we're responding to
    && var tid := m.combiner.value.idx;

    // the element was none, so nothing to be done
    && m.combiner.value.elems[tid].Some?

    // the slot state must be in progress
    && tid in m.slots && m.slots[tid].FCInProgress?

    && m' == m.(
      combiner := Some(FCCombinerResponding(m.combiner.value.elems, tid + 1)),
      slots := m.slots[tid := FCResponse(m.slots[tid].rid)]
    )
  }

  lemma CombinerDoResponse_is_transition(m: M, m': M)
    requires CombinerDoResponse(m, m')
    ensures transition(m, m')
  {

  }

  // -------------------------------- combiner_goto_collecting ----------------------------------

  predicate CombinerGoToCollecting(m: M, m': M)
  {
    && m.M?
    && CombinerValid(m)
    && CombinerIsRespondingDone(m)

    && m' == m.(combiner := Some(FCCombinerCollecting([])))
  }

  lemma CombinerGoToCollecting_is_transition(m: M, m': M)
    requires CombinerGoToCollecting(m, m')
    ensures transition(m, m')
  {

  }


  // -------------------------------- fc_send ---------------------------------------------------

  predicate FCSend(m: M, m': M, tid: nat, rid: RequestId) {
    && m.M?
    && ClientIdle(m, tid)

    // we're modifying this
    && tid in m.slots

    && m' == m.(
      clients := m.clients[tid := FCClientWaiting(rid)],
      slots  := m.slots[tid := FCRequest(rid)])
  }

  lemma FCSend_is_transition(m: M, m': M, tid: nat, rid: RequestId)
    requires FCSend(m, m', tid, rid)
    ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
      ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
     assume false;
    }
  }

  // -------------------------------- fc_recv ---------------------------------------------------


  predicate FCRecv(m: M, m': M, tid: nat, rid: RequestId) {
    && m.M?
    && ClientWaiting(m, tid)

    && SlotHasResponse(m, tid)

    // && rid == m.clients[tid].rid

    && m' == m.(
      clients := m.clients[tid := FCClientIdle],
      slots  := m.slots[tid := FCEmpty])
  }

  lemma FCRecv_is_transition(m: M, m': M, tid: nat, rid: RequestId)
    requires FCRecv(m, m', tid, rid)
    ensures transition(m, m')
  {
    forall p: M | Inv(dot(m, p))
      ensures Inv(dot(m', p))
      && I(dot(m, p)) == I(dot(m', p))
    {
      assert (CombinerState_RequestIds(dot(m', p)));
    }
  }

}

