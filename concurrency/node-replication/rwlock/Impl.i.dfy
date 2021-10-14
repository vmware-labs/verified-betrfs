include "../../framework/Atomic.s.dfy"
include "../../framework/Cells.s.dfy"
include "../Runtime.i.dfy"
include "../../../lib/Lang/LinearSequence.i.dfy"
include "RwLock.i.dfy"

module RwLockImpl {
  import opened NativeTypes
  import opened RwLockToken
  import opened Atomics
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened LinearCells
  import opened GhostLoc
  import opened GlinearOption
  import opened Runtime

  import RwLockMod = RwLock
  import Handle

  // We wish that V were a type parameter, but we don't actually have
  // type parameters.
  type V = Handle.ContentsType

  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method new_mutex(glinear v: V, ghost inv: (V) -> bool)
  returns (m: RwLock)
  requires inv(v)
  ensures m.inv == inv

  /*
   * An ExclusiveGuard is a special ghost object you get when you
   * call `acquire` on a RwLock. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  glinear datatype ExclusiveGuard = ExclusiveGuard(
    glinear exc_obtained_token: Token,
    glinear empty_cell_contents: Handle.Handle,
    ghost m: RwLock)
  {
    predicate Inv() {
      && exc_obtained_token.loc == m.loc
      && IsExcAcqObtained(exc_obtained_token.val)
      && empty_cell_contents.lcell == m.lcell // empty_cell_contents is talking about m's cell
      && empty_cell_contents.v.None?  // m.cell is empty, ready to be give-n back a value at release time.
    }
  }

  /*
   * A SharedGuard is for shared access.
   * Use the `borrow_shared` method below to obtain shared access
   * to the data structure stored in the mutex.
   */

  datatype SharedGuard = SharedGuard(ghost m: RwLock, ghost v: V)

  /*
   * RwLock that protects a piece of data with some invariant.
   */

  linear datatype RwLock = RwLock(
    linear exclusiveFlag: Atomic<bool, Token>,    // implements ExclusiveState.exc
    linear refCounts: lseq<Atomic<uint8, Token>>,   // implements map<ThreadId, nat>
    linear lcell: LinearCell<Handle.ContentsType>, // implements the actual value that ExclusiveState.shared_value represents
    ghost loc: Loc                                // which instance of this lock we're talking about
  )
  {
    predicate inv(v: V)  // client's invariant

    predicate InternalInv()
    {
      && loc.ExtLoc?
      && loc.base_loc == RwLockToken.T.Wrap.singleton_loc()
      && |refCounts| == RwLockMod.RC_WIDTH
      && lseq_full(refCounts)
      && (forall v, token :: atomic_inv(exclusiveFlag, v, token)
            <==> (
              // This token for this location.
              && token.loc == loc

              && token.val.M?
              && token.val.exclusiveFlag.ExclusiveFlag?          // Token can observe ExclusiveFlag
              && token.val == RwLockMod.ExcFlagHandle(token.val.exclusiveFlag)  // Token doesn't have anything else in it
              && v == token.val.exclusiveFlag.acquired            // Token lock state matches protected bool
              // The token and the physical cell are talking about the same reference
              // (but not necessarily the same value -- while a thread holds the lock, it may
              // tamper with the cell contents in a way that temporarily breaks inv, putting
              // it back before release. That doesn't change the token's maintenance of inv
              // based on the "stale" value at the point at which acquire happened.)
              && lcell == token.val.exclusiveFlag.stored_value.lcell
              // The value the token thinks is behind the cell always maintains the client inv.
              && token.val.exclusiveFlag.stored_value.v.Some?
              && inv(token.val.exclusiveFlag.stored_value.v.value)
            )
          )
      && (forall t, count, token | 0 <= t < RwLockMod.RC_WIDTH
          :: atomic_inv(refCounts[t], count, token)
            <==> (
              // Token is a single refcount that matches the protected count
              && token.val == RwLockMod.SharedFlagHandle(t, count as nat)
              && token.loc == loc
              )
          )
    }

    /*
     * `acquire`
     * Provides the client with the guarantee that the data
     * inside meets the invariant.
     */

    predicate IsPendingHandle(token: RwLockToken.Token, visited: int)
    {
      && token.val.M?
      && token.val == RwLockMod.ExcAcqHandle(token.val.exclusiveAcquisition)  // it's an ExcState
      && token.val.exclusiveAcquisition.ExcAcqPending?
      && token.val.exclusiveAcquisition.visited == visited
      && token.val.exclusiveAcquisition.b.lcell == this.lcell
      && token.loc == this.loc

      // ...and the handle is carrying forward the invariants on the value it protects
      && token.val.exclusiveAcquisition.b.v.Some?
      && inv(token.val.exclusiveAcquisition.b.v.value)
    }

    shared method acquire()
    returns (linear v: V, glinear handle: ExclusiveGuard)
    requires InternalInv()
    // ensures InternalInv() -- comes for free because this method is shared! we didn't modify it!
    ensures this.inv(v)
    ensures handle.m == this
    decreases *
    {
      var got_exc := false;
      glinear var pending_handle := RwLockToken.T.get_unit(this.loc);

      while !got_exc
      invariant got_exc ==> IsPendingHandle(pending_handle, 0)
      decreases *
      {
        atomic_block got_exc := execute_atomic_compare_and_set_strong(this.exclusiveFlag, false, true) {
          ghost_acquire g;
          if got_exc {
            RwLockToken.T.dispose(pending_handle);
            g, pending_handle := RwLockToken.perform_ExcBegin(g);
          }
          ghost_release g;
        }
      }

      var visited:uint64 := 0;
      var rc_width:uint64 := 24;

      while visited < rc_width
        invariant 0 <= visited as int <= RwLockMod.RC_WIDTH
        invariant rc_width as int == RwLockMod.RC_WIDTH
        // if we find a nonzero refcount, we'll just keep waiting.
        // (Deadlock breaking is the shared-acquirer's problem.)
        invariant this.InternalInv()
        invariant IsPendingHandle(pending_handle, visited as int)
        invariant pending_handle.loc == this.loc
        decreases *
      {
        atomic_block var ret_value := execute_atomic_load(lseq_peek(this.refCounts, visited)) {
          ghost_acquire token_g; // the token in refCounts[visited]

          if ret_value == 0 {
            // If we find a zero, we advance visited
            pending_handle, token_g := RwLockToken.perform_TakeExcLockCheckRefCount(pending_handle, token_g);
          }
          // else try checking this slot again; maybe a reader left. visited stays where it is.

          ghost_release token_g;
        }
        if ret_value == 0 {
          visited := visited + 1;
        }
      }

      glinear var b':Handle.Handle;
      pending_handle, b' := RwLockToken.perform_Withdraw_TakeExcLockFinish(pending_handle);

      v, b' := take_lcell(lcell, b');
      
      assert inv(v);

      handle := ExclusiveGuard(pending_handle, b', this);
    }

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    shared method release(linear v: V, glinear guard: ExclusiveGuard)
    requires InternalInv()
    requires guard.Inv()
    requires this.inv(v)
    requires guard.m == this
    ensures InternalInv()
    {
      glinear var ExclusiveGuard(exc_obtained_token, empty_cell_contents, m) := guard;

      // Store the incoming value into the cell
      glinear var v_cell_contents := give_lcell(lcell, empty_cell_contents, v);

      // Release the lock.
      atomic_block var _ := execute_atomic_store(this.exclusiveFlag, false) {
        ghost_acquire g;
        g := RwLockToken.perform_Deposit_ReleaseExcLock(g, exc_obtained_token, v_cell_contents);
        ghost_release g;
      }
    }

    /*
     * `acquire_shared`
     * Like acquire, but can be held by more than one client at a time.
     * Returns a handle that can be borrowed from
     */

    shared method acquire_shared(thread_id: uint8)
//    returns (linear handle: SharedGuard)
    requires 0 <= thread_id as nat < RwLockMod.RC_WIDTH;
//    ensures this.inv(handle.v)
//    ensures handle.m == this
    decreases *
    {

      while (true) {
        var exc_acquired: bool;

        // Spin loop until nobody has the exclusive access acquired.
        // Note we don't do anything with handles here, because correctness
        // doesn't (can't!) depend on the value we observe for the
        // exclusiveFlag here.
        atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) { }
        while (exc_acquired)
        {
          SpinLoopHint();
          atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) { }
        }

        // Increment my thread-specific refcount to indicate my enthusiasm to get this shared access.
        atomic_block var orig_count :=
          execute_atomic_fetch_add_uint8(lseq_peek(this.refCounts, thread_id as uint64), 1) {
          ghost_acquire g;
          g := perform_SharedIncCount(g, 1);
          assert wrapped_add_uint8(orig_count, 1) as nat == orig_count as nat + 1;
          ghost_release g;
        }

        // Check if we acquired the shared access (because no exclusive locker got in our way)
        atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) {
          ghost_acquire g;
          if (exc_acquired) {
          }
          ghost_release g;
        }

        if (!exc_acquired)
        {
          // Yay! Any exclusive locker that arrives now will wait behind our incremented refcount.
          break;
        }

        // Decrement the refcount and go back to spinlooping
        atomic_block var count_before_decr :=
          execute_atomic_fetch_add_uint8(lseq_peek(this.refCounts, thread_id as uint64), 1) {
        }
      }
    }

    /*
     * `acquire_release`
     */

    shared method release_shared(linear handle: SharedGuard)
    requires handle.m == this
  }

  function method borrow_shared(shared handle: SharedGuard)
      : (shared v: V)
  ensures v == handle.v
}
