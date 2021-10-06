include "../../framework/Atomic.s.dfy"
include "../../framework/Cells.s.dfy"
include "../../../lib/Lang/LinearSequence.i.dfy"
include "RwLock.i.dfy"

module RwLockImpl {
  import opened RwLockToken
  import opened Atomics
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Cells
  import opened GhostLoc
  import opened GlinearOption

  import RwLockMod = RwLock
  import Handle

  // We wish that V were a type parameter, but we don't actually have
  // type parameters.
  type V = Handle.Handle

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

  datatype ExclusiveGuard = ExclusiveGuard(ghost m: RwLock)

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
    linear exclusiveFlag: Atomic<bool, Token>,  // implements ExclusiveState.exc
    linear refCounts: lseq<Atomic<nat, Token>>,  // implements map<ThreadId, nat>
    linear cell: Cell<Handle.ContentsType>,      // implements the actual value that ExclusiveState.shared_value represents
    ghost loc: Loc                              // which instance of this lock we're talking about
  )
  {
    predicate inv(v: V)  // client's invariant

    predicate InternalInv()
    {
      && (forall v, token :: atomic_inv(exclusiveFlag, v, token)
            <==> (
              && token.val.exclusive.ExclusiveState?          // Token has an ExclusiveState in it
              && token.val == RwLockMod.CentralHandle(token.val.exclusive)  // Token doesn't have anything else in it
              && v == token.val.exclusive.exc                 // Token lock state matches protected bool
              && cell == token.val.exclusive.stored_value.cell  // Token stored value reflects what's in the cell
              && token.loc == loc
            )
          )
      && (forall t, count, token :: atomic_inv(refCounts[t], count, token)
            <==> (
              // Token is a single refcount that matches the protected count
              && token.val == RwLockMod.RefCount(t, count)
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
      && token.val == RwLockMod.ExcHandle(token.val.exc)  // it's an ExcState
      && token.val.exc.visited == visited
      && token.val.exc.b.cell == this.cell
      && token.loc == this.loc
    }

    shared method acquire()
    returns (glinear v: V, glinear handle: ExclusiveGuard)
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

      var visited := 0;

      while visited < RwLockMod.RC_WIDTH
        invariant 0 <= visited < RwLockMod.RC_WIDTH
        // if we find a nonzero refcount, we'll just keep waiting.
        // (Deadlock breaking is the shared-acquirer's problem.)
        invariant this.InternalInv()
        invariant if visited==RwLockMod.RC_WIDTH
          then pending_handle.val == RwLockMod.ExcHandle(RwLockMod.ExcObtained)
          else IsPendingHandle(pending_handle, visited)
        invariant pending_handle.loc == this.loc
        decreases *
      {
        atomic_block var ret_value := execute_atomic_load(this.refCounts[visited]) {
          ghost_acquire token_g; // the token in refCounts[visited]

          if ret_value == 0 {
            // If we find a zero, we advance visited
            pending_handle, token_g := RwLockToken.perform_TakeExcLockCheckRefCount(pending_handle, token_g);
            visited := visited + 1;
          }
          // else try checking this slot again; maybe a reader left. visited stays where it is.

          ghost_release token_g;
        }
      }

      handle := pending_handle;
    }

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    method release(glinear v: V, glinear handle: ExclusiveGuard)
    requires this.inv(v)
    requires handle.m == this

    /*
     * `acquire_shared`
     * Like acquire, but can be held by more than one client at a time.
     * Returns a handle that can be borrowed from
     */

<<<<<<< HEAD
    shared method acquire_shared()
    returns (linear handle: SharedGuard<V>)
=======
    method acquire_shared()
    returns (linear handle: SharedGuard)
>>>>>>> 58375053 (progress on rwlock/Impl)
    ensures this.inv(handle.v)
    ensures handle.m == this

    /*
     * `acquire_release`
     */

<<<<<<< HEAD
    shared method release_shared(linear handle: SharedGuard<V>)
=======
    method release_shared(linear handle: SharedGuard)
>>>>>>> 58375053 (progress on rwlock/Impl)
    requires handle.m == this
  }

  function method borrow_shared(shared handle: SharedGuard)
      : (shared v: V)
  ensures v == handle.v
}
