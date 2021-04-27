#![allow(dead_code)]

// Note: this exploration file won't make much sense unless
// you understand the RWLock.dfy example first.
// Also see rwlock_unverified.rs.

// Let's assume we have some basic primitives for manipulating ghost state:

use galvanize::Invariant;
use galvanize::PCM;
use galvanize::PCMExtension;

// A replacement for UnsafeCell (equivalent, except that it's not unsafe
// because we use ghost state to verify its behavior)

use galvanize::VerifiedCell;

// A library for verified atomics using ghost state:

use galvanize::atomic::{AtomicU32, AtomicBool, Ordering};

// Define the extension PCM like in the RWLock.dfy file:

struct CentralState<Base> {
  logical_exc: bool,
  logical_rc: nat,
  held_value: Option<Base>,
}

// Auto-derive the monoidal properties
// (Option and nat are simple 'built in' monoids that allow auto-deriving)

#[derive(PCM)]
struct RWLockProtocol<Base> {
  phys_exc: Option<bool>,
  phys_rc: Option<nat>,
  central: Option<CentralState<Base>>,
  exc_pending_handle: Option<()>,
  exc_taken_handle: Option<()>,
  shared_pending_handles: nat,
  shared_taken_handles: fn (Base) -> nat,
}

impl<Base> RWLockProtocol<Base> {
  fn PhysExcHandle(phys_exc: bool) -> RWLockProtocol<Base> {
    // Easy to imagine some helper macros
    // e.g., UnitalInit fills in the '...' by adding all the
    // other fields with 'unit', set to unit
    // so you don't have to write all the boilerplate like the equivalent
    // commented block, below

    UnitalInit!(RWLockProtocol{ phys_exc: Some(phys_exc), ... })

    /*RWLockProtocol{
      phys_exc: Some(phys_exc),
      phys_rc: None,
      central: None,
      exc_pending_handle: None,
      exc_taken_handle: None,
      shared_pending_handles: 0,
      shared_taken_handles: (|x| -> 0),
    }*/
  }

  fn PhysRcHandle(phys_rc: nat) -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ phys_rc: Some(phys_rc), ... })
  }

  fn CentralHandle(central: CentralState) -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ central: Some(central), ... })
  }

  fn ExcPendingHandle() -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ exc_pending_handle: Some(()), ... })
  }

  fn ExcTakenHandle() -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ exc_taken_handle: Some(()), ... })
  }

  fn SharedPendingHandle() -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ shared_pending_handles: 1, ... })
  }

  fn SharedTakenHandle(b: Base) -> RWLockProtocol<Base> {
    UnitalInit!(RWLockProtocol{ 
      shared_taken_handles: (|x| -> (if x == b { 1 } else { 0 })),
      ...
    })
  }
}

// I want to somehow create a trait that ties Base and RWLockProtocol<Base>
// together. Not sure if this is possible in Rust ???
impl PCMExtension for (Base, RWLockProtocol<Base>) {
  // Proof code for the invariants, transitions from the RWLock.dfy example
  // all go here.
  fn invariant(m: RWLockProtocol<Base>) -> bool { ... }
  fn interp(m: RWLockProtocol<Base>) -> Base { ... }

  #[internal_transition]
  fn acquire_exc_pending_step(
    m: RWLockProtocol<Base>,
    m': RWLockProtocol<Base>)
  {
       m == PhysExc(false)
    && m' == PhysExc(true) · ExcPendingHandle()
  }

  // ... all the other transitions from RWLock.dfy go here
  // as well as proofs about invariant-preservation and so on
}

struct RWLock<T> {
  cell: VerifiedCell<T>,

  // VerifiedCellValue<T> is the type of the ghost-state that gives you
  // permission to access VerifiedCell<T>.
  // RWLockProtocol<VerifiedCellValue<T>>, then, is a ghost state for
  // the RWLockProtocol that manages access to VerifiedCell<T>.
  // Finally, GhostTokenStore<...> allows atomic access to a piece of said ghost state
  ghost central_token: GhostTokenStore<RWLockProtocol<VerifiedCellValue<T>>>

  // Atomics store ghost state as well
  exc: AtomicBool<RWLockProtocol<VerifiedCellValue<T>>>,
  rc: AtomicU32<RWLockProtocol<VerifiedCellValue<T>>>,
}


impl<T> RWLock<T> {
  ghost fn central_inv(t: &RWLockProtocol) {
    t.central.is_some()
  }

  // Invariants that tie the ghost state to the actual values stored in the Atomics

  ghost fn exc_inv(b: bool, t: &RWLockProtocol) {
    t == PhysExcHandle(b)
  }

  ghost fn shared_inv(n: nat, t: &RWLockProtocol) {
    t == PhysSharedHandle(n)
  }

  ghost fn invariant(&self) {
    // We have several tokens floating around - make sure they all refer
    // to the same instance of the protocol. Also make sure they correspond
    // to the VerifiedCell instance they are supposed to be managing
       self.central_token.loc.base == self.cell.loc
    && self.exc.loc == self.central_token.loc
    && self.rc.loc == self.central_token.loc

    // Tie the Atomics and the Invariant to the invariants defined above
    && self.central_token.inv == central_inv
    && self.exc.inv == exc_inv
    && self.rc.inv == rc_inv
  }

  pub fn new(t: T) -> RWLock<T> {
    // The 'VerifiedCell' library would let us create a 'cell token' which represents
    // permission to access the contents of the VerifiedCell. So for example,
    // if we have exclusive access to the cell token, we can get a &mut borrow from
    // the VerifiedCell. If we have shared access to the cell token, we can get a
    // shared &borrow from the VerifiedCell.

    // Keep in mind the token is "ghost".

    // cell: VerifiedCell<T>
    // token: Token<VerifiedCellValue<T>>

    let (cell, token) = VerifiedCell::new(t);

    // Instantiate an RWLockProtocol to manage access to the 'cell token'.

    // Again, I'm imagining some cool syntax that makes this less cumbersome.
    // This 'let token ... from ...' syntax would let you both
    //  (i) create some RWLockProtocol-state from the CellToken-state and
    //  (ii) split it into three parts for us
    // with a lot of cumbersome repeated boilerplate

    GhostManipulate!(
      let token phys_exc_token = PhysExcHandle(false);
      let token phys_rc_handle = PhysRcHandle(0);
      let token central_token = CentralHandle(CentralState{
            logical_exc: false,
            phys_rc: 0,
            held_value: Some(token.value()),
          });
      from PCMExtensionCreate(token)
    );

    // Build the object.

    return RWLock{
      cell: VerifiedCell::new(t),
      central_token: GhostTokenStore::new(central_token, central_inv),
      exc: AtomicBool::new(false, phys_exc_token, exc_inv),
      rc: AtomicU32::new(0, phys_rc_token, rc_inv),
    };
  }

  pub fn acquire_exclusive(&self, fun: fn(&mut T) -> ()) {
    ghost let pending_handle;

    loop {
      // Here, I'm imagining some special syntax for convenient access to the ghost
      // state of the atomic. The idea is this:
      // When you perform the compare_exchange, we are doing some transition on the
      // physical staet `old_b -> new_b` (e.g., on success, we end up doing a transition
      // false -> true). Inside the 'atomic' block we can execute ghost code that manipulates
      // the ghost state (and returns it at the end). We have to make sure that the invariants
      // are maintained.

      let res = atomic!(self.exc.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst) acquire (exc_token, old_b, new_b) {
        if res.is_okay() {
          exc_token, pending_handle := RWLockProtocol::acquire_exc_pending(exc_token);
        } else {
          // do nothing
        }
        release exc_token;
      });
      
      if res.is_okay() {
        break;
      }
    }

    // At this point we've obtained an ExcPendingHandle token.
    // Now for the second phase of the 'acquire' step.
    // (acquire_exc_finish_step)

    ghost let cell_token;
    ghost let taken_handle;

    loop {
      let r = atomic!(self.rc.load(Ordering::SeqCst) acquire (rc_token) {
        if rc == 0 {
          atomic!(self.central_token.open() acquire (central_token) {
            rc_token, central_token, cell_token, taken_handle = RWLockProtocol::transition_exc_finish(rc_token, central_token, pending_handle);
            release central_token;
          });
        }
        release rc_token;
      });

      if r == 0 {
        break;
      }
    }

    // This step lets us obtain the CellToken! Remember, we originally put the
    // Cell token "into the RWLockProtocol world". Here, we've now "extracted"
    // it from that world and we can manipulate it normally. Since we own the CellToken,
    // we can get &mut access to the contents of the VerifiedCell.

    let borrow = &mut *self.t.get_mut(cell_token);
    fun(&mut borrow);

    // borrow expires, we get cell_token back?
    // this part is a little awkward

    // Do the release step (i.e., put the CellToken back into the RWLockProtocol world)
    let res = atomic!(self.exc.store(false, Ordering::SeqCst) acquire(exc_token) {
      atomic self.central_token.open() acquire (central_token) {
        exc_token, central_token = RWLockProtocol::release_exc(exc_token, central_token, cell_token, taken_handle);
        release central_token;
      }
      release exc_token;
    });
  }

  pub fn acquire_shared(&self, fun: fn(& T) -> ()) {
    // Process for acquiring shared access is pretty similar at first.

    let shared_handle;

    loop {
      loop {
        let r = self.exc.load(Ordering::Relaxed);
        if !r { break; }
      }

      atomic!(self.rc.fetch_add(1, Ordering::SeqCst) {
        // ... (acquire_shared_pending_step)
      });

      let already_taken = atomic!(self.exc.load(Ordering::SeqCst) {
        if !already_taken {
          // ... (acquire_shared_finish)
        } else {
        }
      });

      if !already_taken {
        break;
      } else {
        // abort and try again
        atomic!(self.rc.fetch_sub(1, Ordering::SeqCst) {
          // ...
        });
      }
    }

    // The main difference here is that we get a 'shared borrow' of the cell_token
    // rather than a 'mut borrow'.
    let cell_token = & RWLockProtocol::borrow(shared_handle);

    // With that 'shared borrow' we can get a 'shared borrow' of the object in the
    // VerifiedCell.
    let borrow = self.cell.get_borrow(cell_token);

    fun(borrow);

    atomic!(self.rc.fetch_sub(1, Ordering::SeqCst) {
      // ...
    });
  }
}
