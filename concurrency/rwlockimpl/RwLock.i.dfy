include "../../lib/Base/Option.s.dfy"
include "../framework/Rw.i.dfy"
include "FullMap.i.dfy"

abstract module StoredTypeModule {
  type StoredType(!new)
}

module RwLock(stm: StoredTypeModule) refines Rw {
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
    The RWLock is designed to manage a resource of type `StoredType`
  */

  type StoredType = stm.StoredType

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
    //logical_exc: bool,
    //logical_rc: nat,

    // The base resource currently "checked into" the lock.
    // None means no value is currently checked in (because a value is
    // exclusively checked out; held_value.None? <==> logical_exc).
    // (Yes, this means logical_exc is completely redundant information,
    // but the structure is kept parallel to clarify the presentation.)
    held_value: StoredType
  ) | CentralNone

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
    central: CentralState,

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

    ghost shared_taken_handles: FullMap<StoredType, nat>
  ) | Fail

  function zero_map() : imap<StoredType, nat> {
    imap k | true :: 0
  }

  function unit() : M
  {
    M(None, None, CentralNone, false, false, 0, zero_map())
  }

  // Defining the 'dot' operation on the monoid M is pretty
  // straightforward.

  function add_fns(f: FullMap<StoredType, nat>, g: FullMap<StoredType, nat>) : FullMap<StoredType, nat> {
    imap b | true :: f[b] + g[b]
  }

  function dot(x: M, y: M) : M
  {
    if
      && x != Fail && y != Fail
      && !(x.phys_exc.Some? && y.phys_exc.Some?)
      && !(x.phys_rc.Some? && y.phys_rc.Some?)
      && !(x.central.CentralState? && y.central.CentralState?)
      && !(x.exc_pending_handle && y.exc_pending_handle)
      && !(x.exc_taken_handle && y.exc_taken_handle)
    then M(
      (if x.phys_exc.Some? then x.phys_exc else y.phys_exc),
      (if x.phys_rc.Some? then x.phys_rc else y.phys_rc),
      (if x.central.CentralState? then x.central else y.central),
      x.exc_pending_handle || y.exc_pending_handle,
      x.exc_taken_handle || y.exc_taken_handle,
      x.shared_pending_handles + y.shared_pending_handles,
      add_fns(x.shared_taken_handles, y.shared_taken_handles)
    )
    else Fail
  }

  lemma dot_unit(x: M)
  //ensures dot(x, unit()) == x
  {
    if dot(x, unit()) != Fail {
      /*assert forall b :: x.shared_taken_handles[b]
          == dot(x, unit()).shared_taken_handles[b];
      assert x.shared_taken_handles
          == dot(x, unit()).shared_taken_handles;*/
    } else {
    }
  }

  lemma commutative(x: M, y: M)
  //ensures dot(x, y) == dot(y, x)
  {
    if dot(x,y) != Fail {
    } else {
    }
  }

  lemma associative(x: M, y: M, z: M)
  //ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x,dot(y,z)) != Fail {
    } else {
    }
  }

  function PhysExcHandle(phys_exc: bool) : M {
    M(Some(phys_exc), None, CentralNone, false, false, 0, zero_map())
  }

  function PhysRcHandle(phys_rc: nat) : M {
    M(None, Some(phys_rc), CentralNone, false, false, 0, zero_map())
  }

  function CentralHandle(cs: CentralState) : M {
    M(None, None, cs, false, false, 0, zero_map())
  }

  function ExcPendingHandle() : M {
    M(None, None, CentralNone, true, false, 0, zero_map())
  }

  function ExcTakenHandle() : M {
    M(None, None, CentralNone, false, true, 0, zero_map())
  }

  function unit_fn(elem: StoredType) : FullMap<StoredType, nat> {
    imap b | true :: (if elem == b then 1 else 0)
  }

  function SharedPendingHandle() : M  {
    M(None, None, CentralNone, false, false, 1, zero_map())
  }

  function SharedTakenHandle(elem: StoredType) : M  {
    M(None, None, CentralNone, false, false, 0, unit_fn(elem))
  }

  // Define the invariant. Every transition on M maintains this
  // invariant across a "whole" M-state.
  // It won't necessarily hold for a fragment: for example a thread
  // holds a handle but has no idea what the central state is, so
  // it has m.central.None?.
  // The invariant's ultimate job is to prepare for lemma borrow_shared_handle.

  predicate Inv(x: M)
  {
    && x != Fail
    && (x != unit() ==> (
      && x.central.CentralState?
      && x.phys_exc.Some?
      && x.phys_rc.Some?
      && var phys_exc := x.phys_exc.value;
      && var phys_rc := x.phys_rc.value;
      && phys_rc == x.shared_pending_handles + x.shared_taken_handles[x.central.held_value]
      && (!phys_exc ==> !x.exc_pending_handle && !x.exc_taken_handle)
      && (phys_exc ==> (x.exc_pending_handle || x.exc_taken_handle)
              && !(x.exc_pending_handle && x.exc_taken_handle))

      && (x.exc_taken_handle ==> forall y :: x.shared_taken_handles[y] == 0)
      && (forall y :: x.shared_taken_handles[y] != 0 ==> x.central.held_value == y)
    ))
  }

  // Map the M-state to the Base-state it represents.

  function I(x: M) : Option<StoredType>
  //requires Inv(m)
  {
    if x == unit() then
      None
    else if !x.exc_taken_handle then
      Some(x.central.held_value)
    else
      // Some thread has the exclusive lock, which means that thread has the
      // fragment of the Base resource that this RWlock protects. So this
      // RWlock *doesn't* have any non-trivial fragment of the Base resource;
      // it has the Base unit.
      None
  }

  // Now we define the transitions of the system
  // and prove the important properties about them
  // (i.e., that they are valid transitions)

  //////// 'Acquire exclusive lock' flow

  // Step 1: atomically set 'exc' flag from false to true

  lemma acquire_exc_pending_step_preserves()
  ensures transition(
      PhysExcHandle(false),
      dot(
        PhysExcHandle(true),
        ExcPendingHandle()
      ))
  {
    var m := PhysExcHandle(false);
    var m' := dot(
        PhysExcHandle(true),
        ExcPendingHandle()
      );
    forall p | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      //assert forall b :: m'.shared_taken_handles(b) == m.shared_taken_handles(b);
      assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  // Step 2: check the 'rc' field
  // In this step, we extract some Base-state.

  lemma acquire_exc_finish_step_withdraw(held_value: StoredType)
  ensures withdraw(
    dot(
      PhysRcHandle(0),
      dot(
        CentralHandle(CentralState(held_value)),
        ExcPendingHandle()
      )),
    dot(
      PhysRcHandle(0),
      dot(
        CentralHandle(CentralState(held_value)),
        ExcTakenHandle()
      )),
      held_value
   )
  {
    var m := dot( PhysRcHandle(0), dot( CentralHandle(CentralState(held_value)), ExcPendingHandle()));
    var m' := dot( PhysRcHandle(0), dot( CentralHandle(CentralState(held_value)), ExcTakenHandle()));
    var x := held_value;
    forall p: M | Inv(dot(m, p)) ensures Inv(dot(m', p))
        && I(dot(m, p)) == Some(x)
        && I(dot(m', p)) == None
    {
      assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  //////// 'Acquire shared lock' flow

  // Step 1: Increment 'rc' field

  lemma acquire_shared_pending_step_preserves(rc: nat)
  ensures transition(
    PhysRcHandle(rc),
    dot(
      PhysRcHandle(rc + 1),
      SharedPendingHandle()
    ))
  {
    var m := PhysRcHandle(rc);
    var m' := dot(PhysRcHandle(rc + 1), SharedPendingHandle());
    forall p | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  // Abort step: Decrement 'rc' field (to try again later)

  lemma abort_shared_step_preserves(rc: nat)
  requires rc >= 1
  ensures transition(
    dot(
      PhysRcHandle(rc),
      SharedPendingHandle()
    ),
    PhysRcHandle(rc - 1)
  )
  {
    var m := dot( PhysRcHandle(rc), SharedPendingHandle());
    var m' := PhysRcHandle(rc - 1);
    forall p | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  // Step 2: Check 'exc' is false

  lemma acquire_shared_finish_step_preserves(held_value: StoredType)
  ensures transition(
    dot(
      PhysExcHandle(false),
      dot(
        CentralHandle(CentralState(held_value)),
        SharedPendingHandle()
      )
    ),
    dot(
      PhysExcHandle(false),
      dot(
        CentralHandle(CentralState(held_value)),
        SharedTakenHandle(held_value)
      )
    ))
  {
    var m := dot( PhysExcHandle(false), dot( CentralHandle(CentralState(held_value)), SharedPendingHandle()));
    var m' := dot( PhysExcHandle(false), dot( CentralHandle(CentralState(held_value)), SharedTakenHandle(held_value)));
    forall p | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert forall b :: b != held_value ==>
          dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  // Ability to borrow state from a ReadingHandle

  lemma shared_handle_borrow(b: StoredType)
  ensures borrow(SharedTakenHandle(b), b)
  {
    var a := SharedTakenHandle(b);
    var x := b;
    forall p: M | Inv(dot(a, p)) ensures I(dot(a, p)) == Some(x)
    {
      assert dot(p, SharedTakenHandle(b)).shared_taken_handles[b] > 0;
    }
  }

  //////// 'Release exclusive lock'

  // Step 'exc' field to 'false'

  lemma release_exc_step_deposit(b_old: StoredType, b: StoredType, pe: bool)
  ensures deposit(
    dot(
      PhysExcHandle(pe),
      dot(
        CentralHandle(CentralState(b_old)),
        ExcTakenHandle()
      )
    ),
    dot(
      PhysExcHandle(false),
      CentralHandle(CentralState(b))
    ),
    b)
  {
    var m := dot(
      PhysExcHandle(pe),
      dot(
        CentralHandle(CentralState(b_old)),
        ExcTakenHandle()
      )
    );
    var m' := dot(
      PhysExcHandle(false),
      CentralHandle(CentralState(b))
    );
    var x := b;
    forall p: M | Inv(dot(m, p)) ensures Inv(dot(m', p))
        && I(dot(m, p)) == None
        && I(dot(m', p)) == Some(x)
    {
      assert forall b :: dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }

  //////// 'Release shared lock'

  // Decrement 'rc' field

  lemma release_shared_step_preserves(b0: StoredType, b: StoredType, rc: nat)
  requires rc >= 1
  ensures transition(
    dot(
      PhysRcHandle(rc),
      dot(
        CentralHandle(CentralState(b0)),
        SharedTakenHandle(b)
      )
    ),
    dot(
      PhysRcHandle(rc - 1),
      CentralHandle(CentralState(b0))
    )
  )
  {
    var m := dot( PhysRcHandle(rc), dot( CentralHandle(CentralState(b0)), SharedTakenHandle(b)));
    var m' := dot( PhysRcHandle(rc - 1), CentralHandle(CentralState(b0)));

    forall p | Inv(dot(m, p))
    ensures Inv(dot(m', p)) && I(dot(m, p)) == I(dot(m', p))
    {
      assert dot(m, p).shared_taken_handles[b] > 0;
      assert b == b0;
      assert forall b :: b != b0 ==>
          dot(m',p).shared_taken_handles[b] == dot(m,p).shared_taken_handles[b];
    }
  }
}

module RwLockTokens(stm: StoredTypeModule) {
  import rwlock = RwLock(stm)
  import T = RwTokens(RwLock(stm))

  import opened Options

  type Token = T.Token

  glinear method initialize(glinear init_value: rwlock.StoredType)
  returns (glinear pe': Token, glinear pr': Token, glinear ce': Token)
  ensures pe'.loc == pr'.loc == ce'.loc
  ensures pe'.val == rwlock.PhysExcHandle(false)
  ensures pr'.val == rwlock.PhysRcHandle(0)
  ensures ce'.val == rwlock.CentralHandle(rwlock.CentralState(init_value))

  glinear method perform_exc_pending(glinear pe: Token)
  returns (glinear pe': Token, glinear handle: Token)
  requires pe.val == rwlock.PhysExcHandle(false)
  ensures pe'.val == rwlock.PhysExcHandle(true)
  ensures handle.val == rwlock.ExcPendingHandle()
  ensures pe'.loc == handle.loc == pe.loc
  {
    ghost var a := rwlock.PhysExcHandle(true);
    ghost var b := rwlock.ExcPendingHandle();
    rwlock.acquire_exc_pending_step_preserves();
    pe', handle := T.internal_transition_1_2(pe, a, b);
  }

  glinear method perform_exc_finish(
      glinear pe: Token,
      glinear ct: Token,
      glinear handle: Token,
      ghost held_value: rwlock.StoredType)
  returns (glinear pe': Token, glinear ct': Token, glinear handle': Token, glinear resource': rwlock.StoredType)
  requires pe.val == rwlock.PhysRcHandle(0)
  requires ct.val == rwlock.CentralHandle(rwlock.CentralState(held_value))
  requires handle.val == rwlock.ExcPendingHandle()
  requires ct.loc == handle.loc == pe.loc
  requires ct.loc.ExtLoc?
  ensures pe'.val == rwlock.PhysRcHandle(0)
  ensures ct'.val == rwlock.CentralHandle(rwlock.CentralState(held_value))
  ensures handle'.val == rwlock.ExcTakenHandle()
  ensures resource' == held_value
  ensures pe'.loc == ct'.loc == handle'.loc == ct.loc
  {
    ghost var a := rwlock.PhysRcHandle(0);
    ghost var b := rwlock.CentralHandle(rwlock.CentralState(held_value));
    ghost var c := rwlock.ExcTakenHandle();

    rwlock.acquire_exc_finish_step_withdraw(held_value);
    pe', ct', handle', resource' := T.withdraw_3_3(pe, ct, handle,
        a, b, c, held_value);
  }

  glinear method perform_exc_release(
      glinear pe: Token,
      glinear ct: Token,
      glinear handle: Token,
      glinear resource: rwlock.StoredType,
      ghost held_value: rwlock.StoredType,
      ghost phys_exc: bool)
  returns (glinear pe': Token, glinear ct': Token)
  requires pe.val == rwlock.PhysExcHandle(phys_exc)
  requires ct.val == rwlock.CentralHandle(rwlock.CentralState(held_value))
  requires handle.val == rwlock.ExcTakenHandle()
  requires pe.loc == ct.loc == handle.loc

  ensures pe'.val == rwlock.PhysExcHandle(false)
  ensures ct'.val == rwlock.CentralHandle(rwlock.CentralState(resource))
  ensures pe'.loc == ct'.loc == pe.loc
  {
    ghost var a := rwlock.PhysExcHandle(false);
    ghost var b := rwlock.CentralHandle(rwlock.CentralState(resource));

    rwlock.release_exc_step_deposit(held_value, resource, phys_exc);
    pe', ct' := T.deposit_3_2(pe, ct, handle, resource, a, b);
  }

  glinear method perform_shared_pending(glinear pe: Token, ghost rc: nat)
  returns (glinear pe': Token, glinear handle: Token)
  requires pe.val == rwlock.PhysRcHandle(rc)
  ensures pe'.val == rwlock.PhysRcHandle(rc + 1)
  ensures handle.val == rwlock.SharedPendingHandle()
  ensures pe'.loc == handle.loc == pe.loc
  {
    ghost var a := rwlock.PhysRcHandle(rc + 1);
    ghost var b := rwlock.SharedPendingHandle();
    rwlock.acquire_shared_pending_step_preserves(rc);
    pe', handle := T.internal_transition_1_2(pe, a, b);
  }

  glinear method perform_abort_shared(glinear pe: Token, glinear handle: Token, ghost rc: nat)
  returns (glinear pe': Token)
  requires pe.val == rwlock.PhysRcHandle(rc)
  requires handle.val == rwlock.SharedPendingHandle()
  requires pe.loc == handle.loc
  ensures rc >= 1
  ensures pe'.val == rwlock.PhysRcHandle(rc - 1)
  ensures pe'.loc == pe.loc
  {
    glinear var pe1 := pe;
    glinear var handle1 := handle;
    ghost var z := T.obtain_invariant_2(inout pe1, inout handle1);
    ghost var a := rwlock.PhysRcHandle(rc - 1);

    rwlock.abort_shared_step_preserves(rc);
    pe' := T.internal_transition_2_1(pe1, handle1, a);
  }

  glinear method perform_shared_finish(
    glinear pe: Token,
    glinear ct: Token,
    glinear handle: Token,
    ghost held_value: rwlock.StoredType)
  returns (glinear pe': Token, glinear ct': Token, glinear handle': Token)

  requires pe.val == rwlock.PhysExcHandle(false)
  requires ct.val == rwlock.CentralHandle(rwlock.CentralState(held_value))
  requires handle.val == rwlock.SharedPendingHandle()
  requires pe.loc == ct.loc == handle.loc

  ensures pe'.val == rwlock.PhysExcHandle(false)
  ensures ct'.val == rwlock.CentralHandle(rwlock.CentralState(held_value))
  ensures handle'.val == rwlock.SharedTakenHandle(held_value)
  ensures pe'.loc == ct'.loc == handle'.loc == pe.loc
  {
    ghost var a := rwlock.PhysExcHandle(false);
    ghost var b := rwlock.CentralHandle(rwlock.CentralState(held_value));
    ghost var c := rwlock.SharedTakenHandle(held_value);

    rwlock.acquire_shared_finish_step_preserves(held_value);
    pe', ct', handle' := T.internal_transition_3_3(pe, ct, handle, a, b, c);
  }

  glinear method perform_release_shared(
    glinear pe: Token,
    glinear ct: Token,
    glinear handle: Token,
    ghost b0: rwlock.StoredType,
    ghost b: rwlock.StoredType,
    ghost rc: nat)
  returns (glinear pe': Token, glinear ct': Token)

  requires pe.val == rwlock.PhysRcHandle(rc)
  requires ct.val == rwlock.CentralHandle(rwlock.CentralState(b0))
  requires handle.val == rwlock.SharedTakenHandle(b)
  requires pe.loc == ct.loc == handle.loc

  ensures rc >= 1
  ensures pe'.val == rwlock.PhysRcHandle(rc - 1)
  ensures ct'.val == rwlock.CentralHandle(rwlock.CentralState(b0))
  ensures pe'.loc == ct'.loc == pe.loc
  {
    glinear var pe1 := pe;
    glinear var ct1 := ct;
    glinear var handle1 := handle;
    ghost var z := T.obtain_invariant_3(inout pe1, inout ct1, inout handle1);
    var complete :=
        rwlock.dot(rwlock.dot(rwlock.dot(pe.val, ct.val), handle.val), z);

    assert complete.shared_taken_handles[b] >= 1;
    assert b0 == b;
    assert complete.shared_taken_handles[b0] >= 1;
    assert rc >= 1;

    ghost var a := rwlock.PhysRcHandle(rc - 1);
    ghost var b1 := rwlock.CentralHandle(rwlock.CentralState(b0));

    rwlock.release_shared_step_preserves(b0, b, rc);
    pe', ct' := T.internal_transition_3_2(pe1, ct1, handle1, a, b1);
  }
}
