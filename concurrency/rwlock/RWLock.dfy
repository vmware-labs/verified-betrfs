include "../../lib/Base/Option.s.dfy"

module RWLock {
  import opened Options

  /*
    This file defines a 'monoid extension' usable for verifying
    a basic 'reader-writer lock' implementation.
   
    The physical implementation of the reader-writer lock is
    as follows: the lock consists of two fields
       - exc: bool
       - rc: nat

    To acquire the exclusive lock:
       1. Atomically set exc from false to true
       2. Wait until 'rc' is 0.

    To acquire the shared lock:
       1. Atomically increment 'rc' by 1
       2. Wait until 'exc' is set to false.
  */

  /*
    The RWLock is designed to manage a resource out of
    some monoidal state Base. We abstract over it here.
  */

  datatype Base = Base(m: nat)

  function base_unit() : Base

  /*
     Now we define our 'extension state' M.
     The "Central State" is the state the lock maintains; it is state that
     doesn't get linearly borrowed away to lock clients.
   */

  datatype CentralState = CentralState(
    // These values will correspond to the physical values
    // of the 'exc' and 'rc' fields described above
    phys_exc: bool,
    phys_rc: nat,

    // 'logical_exc' means that the lock has ACTUALLY been
    // exclusively taken, while 'logical_rc' is the count
    // of readers. Note that these don't necessarily correspond
    // to the physical values. For example, a thread trying to
    // acquire the lock will set 'exc' to true, but it must
    // then do another step (confirm the readers have left) before
    // they fully obtain the lock.
    // So for example we will have invariants like
    //    logical_exc ==> phys_exc
    // but not the other way around.
    logical_exc: bool,
    logical_rc: nat,

    // The base resource currently "checked into" the lock.
    // None means no value is currently checked in (because a value is
    // exclusively checked out; held_value.None? <==> logical_exc).
    // Thus, should be None iff logical_exc.
    held_value: Option<Base>
  )

  /*
     Now let's define out full monoid extension. 
     This will include both the central state above,
     as well as several handlers.
     A 'handler' is held onto by the thread performing an operation.
     There are four types of handlers:
   
      - exclusive pending (for when a thread is in the middle of acquiring the
        exclusive lock; it set phys_exc, but logical_exc isn't true yet)
      - exclusive taken (for when a thread has successfully taken the exclusive lock)
      - shared pending (for when a thread is in the middle of acquiring the
        shared lock; it incremented phys_rc, but logical_rc is still zero)
      - shared taken (for when a thread has successfully taken the shared lock)

     Note that the 'taken' handles will be part of the rwlock specification
     (i.e., when a client takes the lock in either mode, it gets a 'taken' handle).
     On the other hand, the 'pending' handles are used only internally.
     {@jonh I don't know what "internally" means. The handle gets owned by the thread,
     but doesn't leave the library? The handle is only ever owned by the lock, never
     by a thread?}
   */

  datatype M = M(
    central: Option<CentralState>,

    // We represent these handles with bools, because
    // it's only possible to have a single one.
    // It might be better to think of them as Option<unit>
    // Remember for a fragment of the M-state,
    // 'true' means 'I know I have the handle' whereas
    // 'false' means 'I don't know if someone else has the handle, but I don't have it'.

    exc_pending_handle: bool,
    exc_taken_handle: bool,

    // We represent shared pending handles by a single nat,
    // the number of (fungible) handles.

    shared_pending_handles: nat,

    // We represent shared handles by functions `Base -> nat`.
    // For a given element b of Base, we represent a handler
    // to it by the function `b |--> 1` (everything else maps to 0).
    // This allows the handlers to be additive. (Although we will
    // have an invariant that any reader handler has to match the
    // `held_value`, i.e., there won't be two distinct values b, b'
    // for which these functions are nonzero).
    // {@jonh: I'm curious why you carefully define the data structure
    // to allow adding
    //  {"cat" -> 1} + {"dog"->2} == {"cat" -> 1, "dog"->2}
    // when it seems like in other situations we'd just say:
    //  {"cat" -> 1} + {"dog"->2} == \bottom
    // }

    shared_taken_handles: Base -> nat
  )

  function CentralHandle(cs: CentralState) : M {
    M(Some(cs), false, false, 0, (b) => 0)
  }

  function ExcPendingHandle() : M {
    M(None, true, false, 0, (b) => 0)
  }

  function ExcTakenHandle() : M {
    M(None, false, true, 0, (b) => 0)
  }

  function unit_fn(elem: Base) : (Base -> nat) {
    (b) => (if elem == b then 1 else 0)
  }

  function SharedPendingHandle() : M  {
    M(None, false, false, 1, (b) => 0)
  }

  function SharedTakenHandle(elem: Base) : M  {
    M(None, false, false, 0, unit_fn(elem))
  }

  // Defining the 'dot' operation on the monoid M is pretty
  // straightforward.
  // {@jonh this is called 'add' in the exclusive world. We
  // should unify the naming. I like the 'add' terminology;
  // these things "feel" like addition. I know hardcore mathematicians
  // wouldn't blink at "dot" here, but if "add" works, it might
  // reduce friction for some future CS-background reader.}

  // We'll define dot partially, admitting a "failure" case where
  // adding two Ms fails.
  // Later, we'll show that every transition of the extension monoid
  // state machine preserves dot_okay {@jonh (locally, or globally?)}.
  // {@jonh and that's a long list of lemma ensures clauses. What's the
  // .s condition that demands that we do so? Be nice to mention it
  // here, as the 'fail' idea can be a bit slippery/suspcious.}
  // {@jonh so yeah, why can't we exclude conflicting fn Bases here?}
  predicate dot_okay(m: M, p: M) {
    && !(m.central.Some? && p.central.Some?)
    && !(m.exc_pending_handle && p.exc_pending_handle)
    && !(m.exc_taken_handle && p.exc_taken_handle)
  }

  // {@jonh well look who brought add back into the house.}
  function add_fns(f: Base -> nat, g: Base -> nat) : Base -> nat {
    (b) => f(b) + g(b)
  }

  function dot(m: M, p: M) : M
  requires dot_okay(m, p)
  {
    M(
      (if m.central.Some? then m.central else p.central),
      m.exc_pending_handle || p.exc_pending_handle,
      m.exc_taken_handle || p.exc_taken_handle,
      m.shared_pending_handles + p.shared_pending_handles,
      add_fns(m.shared_taken_handles, p.shared_taken_handles)
    )
  }

  // Define the invariant. Every transition on M maintains this
  // invariant across a "whole" M-state.
  // It won't necessarily hold for a fragment; for example {@jonh please}.
  // {@jonh again a pointer to where in the proof tree this invariant's
  // correctness is employed.}

  predicate Inv(m: M)
  {
    && m.central.Some?
    && var central := m.central.value;
    && (central.logical_exc ==> central.logical_rc == 0)
    && (central.logical_exc ==> central.phys_exc)
    && (central.logical_rc <= central.phys_rc)
    && (m.exc_pending_handle ==> central.phys_exc && !central.logical_exc)
    && (m.exc_taken_handle ==> central.logical_exc)
    && (!central.logical_exc <==> central.held_value.Some?)

    && (central.held_value.None? ==>
      && (forall b :: m.shared_taken_handles(b) == 0)
      && central.phys_rc == m.shared_pending_handles
      && central.logical_rc == 0
    )

    && (central.held_value.Some? ==>
      && (forall b :: b != central.held_value.value ==> m.shared_taken_handles(b) == 0)
      && central.phys_rc == m.shared_pending_handles
          + m.shared_taken_handles(central.held_value.value)
      && central.logical_rc == m.shared_taken_handles(central.held_value.value)
    )
  }

  // Map the M-state to the Base-state it represents.

  function Interp(m: M) : Base
  requires Inv(m)
  {
    if m.central.value.held_value.Some? then
      m.central.value.held_value.value
    else
      // {@jonh  wait wut? Shouldn't you go ask the thread that has the exc handle?}
      base_unit()
  }

  /*
  You might remember the google doc relates M and Base via
  some f-function. In this file, I'm presenting the relationship
  in terms of Inv and Interp instead, which is hopefully clearer.
  However, the original 'f' could then be constructed as follows:

  predicate f(m: M, b: Base) {
    Inv(m) && b == Interp(m)
  }
  */

  // Now we define the transitions of the system
  // and prove the important properties about them
  // (i.e., that they are valid transitions)

  //////// 'Acquire exclusive lock' flow

  // Step 1: atomically set 'exc' flag from false to true

  // {@jonh How should I think about the fact that every transition has m, m',
  // but also this CentralState thingy? I can see that it's state-machine shaped,
  // but something is a little different.}
  predicate acquire_exc_pending_step(m: M, m': M, central: CentralState)
  {
    && central.phys_exc == false
    && m == CentralHandle(central)
    && m' == dot(
      CentralHandle(central.(phys_exc := true)),
      ExcPendingHandle()
    )
  }

  lemma acquire_exc_pending_step_preserves(p: M, m: M, m': M, central: CentralState)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires acquire_exc_pending_step(m, m', central)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    //assert forall b :: m'.shared_taken_handles(b) == m.shared_taken_handles(b);
    assert forall b :: dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }

  // Step 2: check the 'rc' field
  // In this step, we extract some Base-state.

  predicate acquire_exc_finish_step(m: M, m': M, b: Base, b': Base, central: CentralState)
  {
    && central.held_value.Some?
    && central.logical_rc == 0

    && b == base_unit()
    && b' == central.held_value.value

    && m == dot(
      CentralHandle(central),
      ExcPendingHandle()
    )
    && m' == dot(
      CentralHandle(central.(logical_exc := true).(held_value := None)),
      ExcTakenHandle()
    )
  }

  lemma acquire_exc_finish_step_preserves(p: M, m: M, m': M, b: Base, b': Base, central: CentralState)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires acquire_exc_finish_step(m, m', b, b', central)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == b
  ensures Interp(dot(m, p)) == b'
  {
    assert forall b :: dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }

  //////// 'Acquire shared lock' flow

  // Step 1: Increment 'rc' field

  predicate acquire_shared_pending_step(m: M, m': M, central: CentralState)
  {
    && m == CentralHandle(central)
    && m' == dot(
      CentralHandle(central.(phys_rc := central.phys_rc + 1)),
      SharedPendingHandle()
    )
  }

  lemma acquire_shared_pending_step_preserves(p: M, m: M, m': M, central: CentralState)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires acquire_shared_pending_step(m, m', central)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert forall b :: dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }

  // Step 2: Check 'exc' is false

  predicate acquire_shared_finish_step(m: M, m': M, central: CentralState)
  {
    && central.phys_exc == false
    && central.held_value.Some?
    && m == dot(
      CentralHandle(central),
      SharedPendingHandle()
    )
    && m' == dot(
      CentralHandle(central.(logical_rc := central.logical_rc + 1)),
      SharedTakenHandle(central.held_value.value)
    )
  }

  lemma acquire_shared_finish_step_preserves(p: M, m: M, m': M, central: CentralState)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires acquire_shared_finish_step(m, m', central)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert forall b :: b != central.held_value.value ==>
        dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }

  // Ability to borrow state from a ReadingHandle

  lemma borrow_shared_handle(p: M, b: Base)
  requires dot_okay(p, SharedTakenHandle(b))
  requires Inv(dot(p, SharedTakenHandle(b)))
    // {@jonh this ensures is another spot where it would be good to tie in
    // these lemmas to where they're going to be needed (in a .s file?). That
    // would help me understand what this ensures means, and how it connects.}
  ensures Interp(dot(p, SharedTakenHandle(b))) == b
  {
    assert dot(p, SharedTakenHandle(b)).shared_taken_handles(b) > 0;
  }

  //////// 'Release exclusive lock'

  // Step 'exc' field to 'false'

  predicate release_exc_step(m: M, m': M, b: Base, b': Base, central: CentralState)
  {
    && b' == base_unit()

    && m == dot(
      CentralHandle(central),
      ExcTakenHandle()
    )
    && m' ==
      CentralHandle(central
        .(phys_exc := false)
        .(logical_exc := false)
        .(held_value := Some(b))
      )
  }

  lemma release_exc_step_preserves(p: M, m: M, m': M, b: Base, b': Base, central: CentralState)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires release_exc_step(m, m', b, b', central)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == b
  ensures Interp(dot(m, p)) == b'
  {
    assert forall b :: dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }

  //////// 'Release shared lock'

  // Decrement 'rc' field

  predicate release_shared_step(m: M, m': M, central: CentralState, b: Base)
  {
    && central.phys_rc >= 1
    && central.logical_rc >= 1
    && m == dot(
      CentralHandle(central),
      SharedTakenHandle(b)
    )
    && m' ==
      CentralHandle(central
        .(phys_rc := central.phys_rc - 1)
        .(logical_rc := central.logical_rc - 1)
      )
  }

  lemma release_shared_step_preserves(p: M, m: M, m': M, central: CentralState, b: Base)
  requires dot_okay(m, p)
  requires Inv(dot(m, p))
  requires release_shared_step(m, m', central, b)
  ensures dot_okay(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert dot(m, p).shared_taken_handles(b) > 0;
    assert b == central.held_value.value;
    assert forall b :: b != central.held_value.value ==>
        dot(m',p).shared_taken_handles(b) == dot(m,p).shared_taken_handles(b);
  }
}
