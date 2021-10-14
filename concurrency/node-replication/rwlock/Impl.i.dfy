include "../../framework/Atomic.s.dfy"
include "../../framework/Cells.s.dfy"
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

  glinear datatype ExclusiveGuard = ExclusiveGuard(glinear obtained_token: Token, ghost m: RwLock)

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
    linear refCounts: lseq<Atomic<nat, Token>>,   // implements map<ThreadId, nat>
    linear lcell: LinearCell<Handle.ContentsType>, // implements the actual value that ExclusiveState.shared_value represents
    ghost loc: Loc                                // which instance of this lock we're talking about
  )
  {
    predicate inv(v: V)  // client's invariant

    predicate InternalInv()
    {
      && loc.ExtLoc?
      && |refCounts| == RwLockMod.RC_WIDTH
      && (forall v, token :: atomic_inv(exclusiveFlag, v, token)
            <==> (
              && token.val.M?
              && token.val.exclusiveFlag.ExclusiveFlag?          // Token can observe ExclusiveFlag
              && token.val == RwLockMod.ExcFlagHandle(token.val.exclusiveFlag)  // Token doesn't have anything else in it
              && v == token.val.exclusiveFlag.acquired            // Token lock state matches protected bool
              && lcell == token.val.exclusiveFlag.stored_value.lcell  // Token stored value reflects what's in the cell
              && token.loc == loc
            )
          )
      && (forall t, count, token | 0 <= t < RwLockMod.RC_WIDTH
          :: atomic_inv(refCounts[t], count, token)
            <==> (
              // Token is a single refcount that matches the protected count
              && token.val == RwLockMod.SharedFlagHandle(t, count)
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
    }

    shared method acquire()
    returns (linear v: V, glinear handle: ExclusiveGuard)
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
      assert rc_width as int == RwLockMod.RC_WIDTH;  // TODO(travis): why is RC_WIDTH ghost?

      while visited < rc_width
        invariant 0 <= visited as int < RwLockMod.RC_WIDTH
        // if we find a nonzero refcount, we'll just keep waiting.
        // (Deadlock breaking is the shared-acquirer's problem.)
        invariant this.InternalInv()
        invariant if visited as int ==RwLockMod.RC_WIDTH
          then pending_handle.val == RwLockMod.ExcAcqHandle(RwLockMod.ExcAcqObtained)
          else IsPendingHandle(pending_handle, visited as int)
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
      Ptrs.dispose_anything(b'); // TODO(travis): I have no idea if this is okay. Do I need to remember the CellContents b'?
      handle := ExclusiveGuard(pending_handle, this);
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

    shared method acquire_shared()
    returns (linear handle: SharedGuard)
    ensures this.inv(handle.v)
    ensures handle.m == this

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
