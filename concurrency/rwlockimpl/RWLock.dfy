include "../../lib/Base/Option.s.dfy"
include "Ext.i.dfy"
include "FullMap.i.dfy"

module SomeBase refines PCM {
}

module RWLockExt refines SimpleExt {
  import opened Options
  import opened FullMaps

  /*
    This file defines a 'monoid extension' usable for verifying
    a basic 'reader-writer lock' implementation.
   
    The physical implementation of the reader-writer lock is
    as follows: the lock consists of two fields
       - exc: bool
       - rc: nat

    To acquire the exclusive lock:
       1. Atomically set exc from false to true
       2. Wait until observing 'rc' to be 0.

    To acquire the shared lock:
       1. Atomically increment 'rc' by 1
       2. Check that 'exc' is set to false.
        (If 'exc' is true, abort: decrement 'rc' to give exc waiter opportunity
        to complete exc lock, and try again. This is a liveness concern.)
  */

  /*
    The RWLock is designed to manage a resource out of
    some monoidal state Base. Ideally we would define RWLockExt to be
    abstract over Base.
  */

  import Base = SomeBase

  /*
     Now we define our 'extension state' M.
     The "Central State" is the state the lock maintains; it is state that
     doesn't get linearly borrowed away to lock clients.
   */

  datatype CentralState = CentralState(
    // These values will correspond to the physical values
    // of the 'exc' and 'rc' fields described above
    // (note: these two fields moved out of CentralState)
    //phys_exc: bool,
    //phys_rc: nat,

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
    // (Yes, this means logical_exc is completely redundant information,
    // but the structure is kept parallel to clarify the presentation.)
    held_value: Option<Base.M>
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
        shared lock; it incremented phys_rc, but it hasn't observed phys_exc
        false, and hence hasn't ghostily incremented logical_rc)
      - shared taken (for when a thread has successfully taken the shared lock)

     Note that the 'taken' handles are part of the library's external interface;
     when a client takes the lock in either mode, it recieves a 'taken' handle.
     The pending handles are "internal": they're held by different threads, but
     only during a call into the library; they're release before the library's
     stack frame expires.
   */

  datatype M = M(
    phys_exc: Option<bool>,
    phys_rc: Option<nat>,
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
    // (NB "allowing the handlers to be additive" isn't a design goal;
    // we could have excluded such conflicting keys from dot_defined.
    // Travis suspects that would have required sucking the entire invariant
    // into dot_defined.)

    shared_taken_handles: FullMap<Base.M, nat>
  )
  type F = M

  function zero_map() : imap<Base.M, nat> {
    imap k | true :: 0
  }

  function unit() : F
  {
    M(None, None, None, false, false, 0, zero_map())
  }

  lemma dot_unit(x: F)
  //ensures dot_defined(x, unit())
  //ensures dot(x, unit()) == x
  {
    //assert forall b :: x.shared_taken_handles(b)
    //    == dot(x, unit()).shared_taken_handles(b);
    //assert x.shared_taken_handles
    //    == dot(x, unit()).shared_taken_handles;
  }

  lemma commutative(x: F, y: F)
  //requires dot_defined(x, y)
  //ensures dot_defined(y, x)
  //ensures dot(x, y) == dot(y, x)
  { }

  lemma associative(x: F, y: F, z: F)
  //requires dot_defined(y, z)
  //requires dot_defined(x, dot(y, z))
  //ensures dot_defined(x, y)
  //ensures dot_defined(dot(x, y), z)
  //ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  { }

  function PhysExcHandle(phys_exc: bool) : M {
    M(Some(phys_exc), None, None, false, false, 0, zero_map())
  }

  function PhysRcHandle(phys_rc: nat) : M {
    M(None, Some(phys_rc), None, false, false, 0, zero_map())
  }

  function CentralHandle(cs: CentralState) : M {
    M(None, None, Some(cs), false, false, 0, zero_map())
  }

  function ExcPendingHandle() : M {
    M(None, None, None, true, false, 0, zero_map())
  }

  function ExcTakenHandle() : M {
    M(None, None, None, false, true, 0, zero_map())
  }

  function unit_fn(elem: Base.M) : FullMap<Base.M, nat> {
    imap b | true :: (if elem == b then 1 else 0)
  }

  function SharedPendingHandle() : M  {
    M(None, None, None, false, false, 1, zero_map())
  }

  function SharedTakenHandle(elem: Base.M) : M  {
    M(None, None, None, false, false, 0, unit_fn(elem))
  }

  // Defining the 'dot' operation on the monoid M is pretty
  // straightforward.

  // We'll define dot partially, admitting a "failure" case where
  // adding two Ms fails.
  // Later, we'll show that every transition of the extension monoid
  // state machine preserves dot_defined (over the fragment it transforms).
  predicate dot_defined(a: F, b: F) {
    && !(a.phys_exc.Some? && b.phys_exc.Some?)
    && !(a.phys_rc.Some? && b.phys_rc.Some?)
    && !(a.central.Some? && b.central.Some?)
    && !(a.exc_pending_handle && b.exc_pending_handle)
    && !(a.exc_taken_handle && b.exc_taken_handle)
  }

  function add_fns(f: FullMap<Base.M, nat>, g: FullMap<Base.M, nat>) : FullMap<Base.M, nat> {
    imap b | true :: f[b] + g[b]
  }

  function dot(a: F, b: F) : F
  //requires dot_defined(a, b)
  {
    M(
      (if a.phys_exc.Some? then a.phys_exc else b.phys_exc),
      (if a.phys_rc.Some? then a.phys_rc else b.phys_rc),
      (if a.central.Some? then a.central else b.central),
      a.exc_pending_handle || b.exc_pending_handle,
      a.exc_taken_handle || b.exc_taken_handle,
      a.shared_pending_handles + b.shared_pending_handles,
      add_fns(a.shared_taken_handles, b.shared_taken_handles)
    )
  }

  // Define the invariant. Every transition on M maintains this
  // invariant across a "whole" M-state.
  // It won't necessarily hold for a fragment: for example a thread
  // holds a handle but has no idea what the central state is, so
  // it has m.central.None?.
  // The invariant's ultimate job is to prepare for lemma borrow_shared_handle.

  predicate Inv(a: F)
  {
    a != unit() ==> (
      && a.central.Some?
      && a.phys_exc.Some?
      && a.phys_rc.Some?
      && var central := a.central.value;
      && var phys_exc := a.phys_exc.value;
      && var phys_rc := a.phys_rc.value;
      && (central.logical_exc ==> central.logical_rc == 0)
      && (central.logical_exc ==> phys_exc)
      && (central.logical_rc <= phys_rc)
      && (a.exc_pending_handle ==> phys_exc && !central.logical_exc)
      && (a.exc_taken_handle ==> central.logical_exc)
      && (!central.logical_exc <==> central.held_value.Some?)

      && (central.held_value.None? ==>
        && (forall b :: a.shared_taken_handles[b] == 0)
        && phys_rc == a.shared_pending_handles
        && central.logical_rc == 0
      )

      && (central.held_value.Some? ==>
        && (forall b :: b != central.held_value.value ==> a.shared_taken_handles[b] == 0)
        && phys_rc == a.shared_pending_handles
            + a.shared_taken_handles[central.held_value.value]
        && central.logical_rc == a.shared_taken_handles[central.held_value.value]
      )
    )
  }

  // Map the M-state to the Base-state it represents.

  function Interp(a: F) : Base.M
  //requires Inv(m)
  {
    if a == unit() then
      Base.unit()
    else if a.central.value.held_value.Some? then
      a.central.value.held_value.value
    else
      // Some thread has the exclusive lock, which means that thread has the
      // fragment of the Base resource that this RWlock protects. So this
      // RWlock *doesn't* have any non-trivial fragment of the Base resource;
      // it has the Base unit.
      Base.unit()
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

  predicate acquire_exc_pending_step(m: M, m': M)
  {
    && m == PhysExcHandle(false)
    && m' == dot(
      PhysExcHandle(true),
      ExcPendingHandle()
    )
  }

  lemma acquire_exc_pending_step_preserves(p: M, m: M, m': M)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires acquire_exc_pending_step(m, m')
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    //assert forall b :: m'.shared_taken_handles(b) == m.shared_taken_handles(b);
    assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  // Step 2: check the 'rc' field
  // In this step, we extract some Base-state.

  predicate acquire_exc_finish_step(m: M, m': M, b: Base.M, b': Base.M, central: CentralState)
  {
    && central.held_value.Some?
    && central.logical_rc == 0

    && b == Base.unit()
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

  lemma acquire_exc_finish_step_preserves(p: M, m: M, m': M, b: Base.M, b': Base.M, central: CentralState)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires acquire_exc_finish_step(m, m', b, b', central)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == b
  ensures Interp(dot(m, p)) == b'
  {
    assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  //////// 'Acquire shared lock' flow

  // Step 1: Increment 'rc' field

  predicate acquire_shared_pending_step(m: M, m': M, rc: nat)
  {
    && m == PhysRcHandle(rc)
    && m' == dot(
      PhysRcHandle(rc + 1),
      SharedPendingHandle()
    )
  }

  lemma acquire_shared_pending_step_preserves(p: M, m: M, m': M, rc: nat)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires acquire_shared_pending_step(m, m', rc)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  // Step 2: Check 'exc' is false

  predicate acquire_shared_finish_step(m: M, m': M, central: CentralState)
  {
    && central.held_value.Some?
    && m == dot(
      PhysExcHandle(false),
      dot(
        CentralHandle(central),
        SharedPendingHandle()
      )
    )
    && m' == dot(
      PhysExcHandle(false),
      dot(
        CentralHandle(central.(logical_rc := central.logical_rc + 1)),
        SharedTakenHandle(central.held_value.value)
      )
    )
  }

  lemma acquire_shared_finish_step_preserves(p: M, m: M, m': M, central: CentralState)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires acquire_shared_finish_step(m, m', central)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert forall b :: b != central.held_value.value ==>
        dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  // Ability to borrow state from a ReadingHandle

  lemma borrow_shared_handle(p: M, b: Base.M)
  requires dot_defined(p, SharedTakenHandle(b))
  requires Inv(dot(p, SharedTakenHandle(b)))
    // TODO(travis): the monoid-extension .s file will have a proof obligation
    // that explains when it's okay to do borrow-shared; this lemma will satisfy
    // that obligation, enabling the implementation to borrow-shared.
    // This is the lemma the Inv serves.
  ensures Interp(dot(p, SharedTakenHandle(b))) == b
  {
    assert dot(p, SharedTakenHandle(b)).shared_taken_handles[b] > 0;
  }

  //////// 'Release exclusive lock'

  // Step 'exc' field to 'false'

  predicate release_exc_step(m: M, m': M, b: Base.M, b': Base.M, central: CentralState, pe: bool)
  {
    && b' == Base.unit()

    && m == dot(
      PhysExcHandle(pe),
      dot(
        CentralHandle(central),
        ExcTakenHandle()
      )
    )
    && m' == dot(
      PhysExcHandle(false),
      CentralHandle(central
        .(logical_exc := false)
        .(held_value := Some(b))
      )
    )
  }

  lemma release_exc_step_preserves(p: M, m: M, m': M, b: Base.M, b': Base.M, central: CentralState, pe: bool)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires release_exc_step(m, m', b, b', central, pe)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == b
  ensures Interp(dot(m, p)) == b'
  {
    assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  //////// 'Release shared lock'

  // Decrement 'rc' field

  predicate release_shared_step(m: M, m': M, central: CentralState, b: Base.M, rc: nat)
  {
    && rc >= 1
    && central.logical_rc >= 1
    && m == dot(
      PhysRcHandle(rc),
      dot(
        CentralHandle(central),
        SharedTakenHandle(b)
      )
    )
    && m' == dot(
      PhysRcHandle(rc - 1),
      CentralHandle(central
        .(logical_rc := central.logical_rc - 1)
      )
    )
  }

  lemma release_shared_step_preserves(p: M, m: M, m': M, central: CentralState, b: Base.M, rc: nat)
  requires dot_defined(m, p)
  requires Inv(dot(m, p))
  requires release_shared_step(m, m', central, b, rc)
  ensures dot_defined(m', p)
  ensures Inv(dot(m', p))
  ensures Interp(dot(m', p)) == Interp(dot(m, p))
  {
    assert dot(m, p).shared_taken_handles[b] > 0;
    assert b == central.held_value.value;
    assert forall b :: b != central.held_value.value ==>
        dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
  }

  //// Put it all together

  datatype InternalStep =
    | AcquireExcPendingStep
    | AcquireSharedPendingStep(rc: nat)
    | AcquireSharedFinishStep(central: CentralState)
    | ReleaseSharedStep(central: CentralState, b: Base.M, rc: nat)

  datatype CrossStep =
    | AcquireExcFinishStep(central: CentralState)
    | ReleaseExcStep(central: CentralState, pe: bool)

  predicate InternalNextStep(f: F, f': F, step: InternalStep)
  {
    match step {
      case AcquireExcPendingStep => acquire_exc_pending_step(f, f')
      case AcquireSharedPendingStep(rc) => acquire_shared_pending_step(f, f', rc)
      case AcquireSharedFinishStep(central) => acquire_shared_finish_step(f, f', central)
      case ReleaseSharedStep(central, b, c) => release_shared_step(f, f', central, b, c)
    }
  }

  predicate CrossNextStep(f: F, f': F, b: Base.M, b': Base.M, step: CrossStep)
  {
    match step {
      case AcquireExcFinishStep(central) => acquire_exc_finish_step(f, f', b, b', central)
      case ReleaseExcStep(central, pe) => release_exc_step(f, f', b, b', central, pe)
    }
  }

  predicate InternalNext(f: F, f': F)
  {
    exists step :: InternalNextStep(f, f', step)
  }

  predicate CrossNext(f: F, f': F, b: Base.M, b': Base.M)
  {
    exists step :: CrossNextStep(f, f', b, b', step)
  }

  lemma interp_unit()
  //ensures Inv(unit()) && Interp(unit()) == Base.unit()
  {
  }

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  //requires InternalNext(f, f')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  //ensures dot_defined(f', p)
  //ensures Inv(dot(f', p))
  //ensures Interp(dot(f', p)) == Interp(dot(f, p))
  {
    var step :| InternalNextStep(f, f', step);
    match step {
      case AcquireExcPendingStep => acquire_exc_pending_step_preserves(p, f, f');
      case AcquireSharedPendingStep(rc) => acquire_shared_pending_step_preserves(p, f, f', rc);
      case AcquireSharedFinishStep(central) => acquire_shared_finish_step_preserves(p, f, f', central);
      case ReleaseSharedStep(central, b, c) => release_shared_step_preserves(p, f, f', central, b, c);
    }
  }

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: Base.M, b': Base.M)
  //requires CrossNext(f, f', b, b')
  //requires dot_defined(f, p)
  //requires Inv(dot(f, p))
  //requires Base.dot_defined(Interp(dot(f, p)), b)
  //ensures dot_defined(f', p)
  //ensures Inv(dot(f', p))
  //ensures Base.dot_defined(Interp(dot(f', p)), b')
  //ensures Base.dot(Interp(dot(f', p)), b')
  //     == Base.dot(Interp(dot(f, p)), b)
  {
    Base.dot_unit(b);
    Base.commutative(b, Base.unit());

    Base.dot_unit(b');
    Base.commutative(b', Base.unit());

    var step :| CrossNextStep(f, f', b, b', step);
    match step {
      case AcquireExcFinishStep(central) => {
        acquire_exc_finish_step_preserves(p, f, f', b, b', central);
      }
      case ReleaseExcStep(central, pe) => {
        release_exc_step_preserves(p, f, f', b, b', central, pe);
      }
    }
  }
}
