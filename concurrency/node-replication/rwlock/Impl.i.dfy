include "../../framework/Atomic.s.dfy"
include "../../framework/Cells.s.dfy"
include "../Runtime.i.dfy"
include "../../../lib/Lang/LinearSequence.i.dfy"
include "RwLock.i.dfy"
include "../Runtime.i.dfy"

module RwLockImpl(contentsTypeMod: ContentsTypeMod) {
  import opened NativeTypes
  import opened RwLockTokenMod = RwLockToken(contentsTypeMod)
  import opened Atomics
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened LinearCells
  import opened GhostLoc
  import opened GlinearOption
  import opened Options
  import opened Runtime
  import opened Ptrs

  import RwLockMod = RwLock(contentsTypeMod)
  import HandleTypeMod = Handle(contentsTypeMod)

  // We wish that V were a type parameter, but we don't actually have
  // type parameters.
  type V = contentsTypeMod.ContentsType

  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method new_mutex(linear v: V, ghost inv: (V) -> bool)
  returns (linear m: RwLock)
  requires inv(v)
  ensures m.inv == inv
  {
    linear var lcell;
    glinear var lcellContents;
    lcell, lcellContents := new_lcell();
    lcellContents := give_lcell(lcell, lcellContents, v);

    glinear var exclusiveFlagToken, rcs := RwLockTokenMod.perform_Init(lcellContents);
    ghost var loc := exclusiveFlagToken.loc;

    linear var exclusiveFlag := new_atomic(false, exclusiveFlagToken,
        (v, g) => exclusiveFlagInv(v, g, loc, inv, lcell),
        0);

    linear var refCounts: lseq<CachePadded<Atomic<uint8, Token>>>
        := lseq_alloc(RwLockMod.RC_WIDTH_64());
    var j: uint64 := 0;
    while j < 24
    invariant 0 <= j <= RwLockMod.RC_WIDTH_64()
    invariant |refCounts| == RwLockMod.RC_WIDTH
    invariant forall i: int | 0 <= i < j as int ::
        i in refCounts &&
        forall count, token ::
            atomic_inv(refCounts[i].inner, count, token) <==>
            refCountInv(count, token, loc, i)
    invariant forall i: int | j as int <= i < RwLockMod.RC_WIDTH ::
        i !in refCounts
    invariant rcs.loc == loc
    invariant rcs.val == RwLockMod.Rcs(j as int, RwLockMod.RC_WIDTH)
    {
      glinear var rcToken;
      rcToken, rcs := pop_rcs(rcs, j as int, RwLockMod.RC_WIDTH);
      linear var rcAtomic := new_atomic(0, rcToken,
          (v, g) => refCountInv(v, g, loc, j as nat),
          0);

      refCounts := lseq_give(refCounts, j, CachePadded(rcAtomic));

      j := j + 1;
    }

    dispose_anything(rcs);

    m := RwLock(exclusiveFlag, refCounts, lcell, loc, inv);
  }

  /*
   * An ExclusiveGuard is a special ghost object you get when you
   * call `acquire` on a RwLock. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  glinear datatype ExclusiveGuard = ExclusiveGuard(
    glinear exc_obtained_token: Token,
    glinear empty_cell_contents: HandleTypeMod.Handle,
    ghost m: RwLock)
  {
    predicate Inv(expected_lock: RwLock) {
      && exc_obtained_token.loc == m.loc
      && IsExcAcqObtained(exc_obtained_token.val)
      && empty_cell_contents.lcell == m.lcell // empty_cell_contents is talking about m's cell
      && empty_cell_contents.v.None?  // m.cell is empty, ready to be give-n back a value at release time.
      && m == expected_lock
    }
  }

  /*
   * A SharedGuard is for shared access.
   * Use the `borrow_shared` method below to obtain shared access
   * to the data structure stored in the mutex.
   */

  linear datatype SharedGuard = SharedGuard(
    // The shared access can be released on a different thread than the one that acquired it;
    // the guard carries with it the necessary non-ghost thread id that matches the thread_id
    // associated with the ghost shared_obtained_token.
    acquiring_thread_id: uint8,
    glinear shared_obtained_token: Token,
    ghost m: RwLock,
    ghost v: V)
  {
    function StoredContents() : HandleTypeMod.Handle
    {
      LCellContents(m.lcell, Some(v))
    }

    predicate Inv(expected_lock: RwLock)
    {
      && 0 <= acquiring_thread_id as nat < RwLockMod.RC_WIDTH
      && shared_obtained_token.loc == m.loc
      && shared_obtained_token.val.M?
      && shared_obtained_token.val == RwLockMod.SharedAcqHandle(RwLockMod.SharedAcqObtained(
        acquiring_thread_id as nat, StoredContents()))
      && m == expected_lock
    }
  }

  predicate exclusiveFlagInv(v: bool, token: Token, loc: Loc, inv: V -> bool,
      lcell: LinearCell<contentsTypeMod.ContentsType>)
  {
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
  }

  predicate refCountInv(count: uint8, token: Token, loc: Loc, t: nat)
  {
    // Token is a single refcount that matches the protected count
    && token.val == RwLockMod.SharedFlagHandle(t, count as nat)
    && token.loc == loc
  }

  /*
   * RwLock that protects a piece of data with some invariant.
   */

  linear datatype RwLock = RwLock(
    linear exclusiveFlag: Atomic<bool, Token>,    // implements ExclusiveState.exc
    linear refCounts: lseq<CachePadded<Atomic<uint8, Token>>>,   // implements map<ThreadId, nat>
    linear lcell: LinearCell<contentsTypeMod.ContentsType>, // implements the actual value that ExclusiveState.shared_value represents
    ghost loc: Loc,                                // which instance of this lock we're talking about
    ghost inv: V -> bool
  )
  {
    predicate InternalInv()
    {
      && loc.ExtLoc?
      && loc.base_loc == RwLockTokenMod.T.Wrap.singleton_loc()
      && |refCounts| == RwLockMod.RC_WIDTH
      && lseq_full(refCounts)
      && (forall v, token :: atomic_inv(exclusiveFlag, v, token)
            <==> exclusiveFlagInv(v, token, loc, inv, lcell))
      && (forall t, count, token | 0 <= t < RwLockMod.RC_WIDTH
          :: atomic_inv(refCounts[t].inner, count, token)
            <==> refCountInv(count, token, loc, t))
    }

    /*
     * `acquire`
     * Provides the client with the guarantee that the data
     * inside meets the invariant.
     */

    predicate IsPendingHandle(token: RwLockTokenMod.Token, visited: int)
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
    returns (linear v: V, glinear guard: ExclusiveGuard)
    requires InternalInv()
    // ensures InternalInv() -- comes for free because this method is shared! we didn't modify it!
    ensures guard.Inv(this)
    ensures this.inv(v)
    decreases *
    {
      var got_exc := false;
      glinear var pending_handle := RwLockTokenMod.T.get_unit(this.loc);

      while !got_exc
      invariant got_exc ==> IsPendingHandle(pending_handle, 0)
      decreases *
      {
        atomic_block got_exc := execute_atomic_compare_and_set_strong(this.exclusiveFlag, false, true) {
          ghost_acquire g;
          if got_exc {
            RwLockTokenMod.T.dispose(pending_handle);
            g, pending_handle := RwLockTokenMod.perform_ExcBegin(g);
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
        atomic_block var ret_value := execute_atomic_load(lseq_peek(this.refCounts, visited).inner) {
          ghost_acquire token_g; // the token in refCounts[visited]

          if ret_value == 0 {
            // If we find a zero, we advance visited
            pending_handle, token_g := RwLockTokenMod.perform_TakeExcLockCheckRefCount(pending_handle, token_g);
          }
          // else try checking this slot again; maybe a reader left. visited stays where it is.

          ghost_release token_g;
        }
        if ret_value == 0 {
          visited := visited + 1;
        }
      }

      glinear var b':HandleTypeMod.Handle;
      pending_handle, b' := RwLockTokenMod.perform_Withdraw_TakeExcLockFinish(pending_handle);

      v, b' := take_lcell(lcell, b');
      
      assert inv(v);

      guard := ExclusiveGuard(pending_handle, b', this);
    }

    /*
     * `release`
     * The client must ensure that the data meets the invariant.
     */

    shared method release(linear v: V, glinear guard: ExclusiveGuard)
    requires InternalInv()
    requires guard.Inv(this)
    requires this.inv(v)
    {
      glinear var ExclusiveGuard(exc_obtained_token, empty_cell_contents, m) := guard;

      // Store the incoming value into the cell
      glinear var v_cell_contents := give_lcell(lcell, empty_cell_contents, v);

      // Release the lock.
      atomic_block var _ := execute_atomic_store(this.exclusiveFlag, false) {
        ghost_acquire g;
        g := RwLockTokenMod.perform_Deposit_ReleaseExcLock(g, exc_obtained_token, v_cell_contents);
        ghost_release g;
      }
    }

    /*
     * `acquire_shared`
     * Like acquire, but can be held by more than one client at a time.
     * Returns a handle that can be borrowed from
     */

    shared method acquire_shared(thread_id: uint8)
    returns (linear guard: SharedGuard)
    requires InternalInv()
    requires 0 <= thread_id as nat < RwLockMod.RC_WIDTH;
    ensures this.inv(guard.v)
    ensures guard.Inv(this)
    decreases *
    {
      // Use a glOption to exfiltrate a glinear value created inside the loop
      glinear var shared_handle_result := glNone;
      ghost var shared_value;
      while (true)
        //invariant obtained_handle is nice.
        invariant 0 <= thread_id as nat < RwLockMod.RC_WIDTH;
        decreases *
      {
        var exc_acquired: bool;

        // Spin loop until nobody has the exclusive access acquired.
        // Note we don't do anything with handles here, because correctness
        // doesn't (can't!) depend on the value we observe for the
        // exclusiveFlag here.
        atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) { }
        while (exc_acquired)
          decreases *
        {
          SpinLoopHint();
          atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) { }
        }

        // Increment my thread-specific refcount to indicate my enthusiasm to get this shared access.
        glinear var shared_handle;
        atomic_block var orig_count :=
          execute_atomic_fetch_add_uint8(lseq_peek(this.refCounts, thread_id as uint64).inner, 1) {
          ghost_acquire g;
          g, shared_handle := perform_SharedIncCount(g, thread_id as nat);

          // TODO(travis,jonh): need a Count token proving there are fewer than 256 threads participating
          assume wrapped_add_uint8(orig_count, 1) as nat == orig_count as nat + 1;

          ghost_release g;
        }

        // Check if we acquired the shared access (because no exclusive locker got in our way)
        atomic_block exc_acquired := execute_atomic_load(this.exclusiveFlag) {
          ghost_acquire g;
          if (!exc_acquired) {
            g, shared_handle := perform_SharedCheckExc(g, shared_handle, thread_id as nat);
            shared_value := g.val.exclusiveFlag.stored_value;
          }
          ghost_release g;
        }

        if (!exc_acquired)
        {
          // Yay! Any exclusive locker that arrives now will wait behind our incremented refcount.
          dispose_glnone(shared_handle_result);
          shared_handle_result := glSome(shared_handle);
          break;
        }

        // Decrement the refcount and go back to spinlooping
        atomic_block var count_before_decr :=
          execute_atomic_fetch_sub_uint8(lseq_peek(this.refCounts, thread_id as uint64).inner, 1) {
          ghost_acquire g;
          g := perform_SharedDecCountPending(g, shared_handle, thread_id as nat);
          ghost_release g;
        }
      }

      glinear var shared_obtained_handle := unwrap_value(shared_handle_result);
      guard := SharedGuard(thread_id, shared_obtained_handle, this, shared_value.v.value);
    }

    /*
     * `acquire_release`
     */

    shared method release_shared(linear guard: SharedGuard)
    requires InternalInv()
    requires guard.Inv(this)
    {
      linear var SharedGuard(acquiring_thread_id, shared_obtained_token, m, v) := guard;
      atomic_block var count_before_decr :=
        execute_atomic_fetch_sub_uint8(lseq_peek(this.refCounts, acquiring_thread_id as uint64).inner, 1) {
        ghost_acquire g;
        g := perform_SharedDecCountObtained(
          g,
          shared_obtained_token,
          acquiring_thread_id as int,
          LCellContents(lcell, Some(v)));
        ghost_release g;
      }
    }
  }

  method borrow_shared(shared rwlock: RwLock, shared handle: SharedGuard)
  returns (shared v: V)
  requires rwlock.InternalInv()
  requires handle.Inv(rwlock)
  ensures v == handle.v
  {
    gshared var cellContents := RwLockTokenMod.borrow_inner(
        handle.shared_obtained_token,
        handle.acquiring_thread_id as nat,
        handle.StoredContents());

    v := read_lcell(rwlock.lcell, cellContents);
  }
}
