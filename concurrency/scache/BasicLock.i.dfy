include "../framework/Atomic.s.dfy"
include "../framework//GlinearOption.i.dfy"

module BasicLockImpl {
  import opened GlinearOption
  import opened Atomics
  import opened Ptrs

  type AtomicLock<!G(!new)> = Atomic<bool, glOption<G>>

  predicate lock_inv<G>(v: bool, g: glOption<G>, fn: G -> bool)
  {
    && (v == true  ==> g.glNone?)
    && (v == false ==> g.glSome? && fn(g.value))
  }

  linear datatype pre_BasicLock<!G(!new)> = BasicLock(linear a: AtomicLock<G>, ghost inv: G -> bool)
  {
    predicate wf() {
      forall v: bool, g: glOption<G> ::
          atomic_inv(a, v, g) <==> lock_inv(v, g, this.inv)
    }
  }

  type BasicLock<!G(!new)> = bl : pre_BasicLock<G> | bl.wf()
    witness *

  /*
   * Acquire if possible; don't block.
   */

  method try_acquire<G(!new)>(shared l: BasicLock<G>)
  returns (success: bool, glinear g: glOption<G>)
  ensures success <==> g.glSome?
  ensures g.glSome? ==> l.inv(g.value)
  {
    atomic_block success := execute_atomic_compare_and_set_strong(
        l.a, false, true)
    {
      ghost_acquire lock_g;
      if success {
        g := lock_g;
        lock_g := glNone;
      } else {
        g := glNone;
      }
      ghost_release lock_g;
    }
  }

  method release<G(!new)>(shared l: BasicLock<G>, glinear g: G)
  requires l.inv(g)
  {
    atomic_block var _ := execute_atomic_store(l.a, false) {
      ghost_acquire old_g;
      dispose_anything(old_g);
      glinear var x := glSome(g);
      ghost_release x;
    }
  }

  method new_basic_lock<G(!new)>(glinear g: G, ghost inv: G -> bool)
  returns (linear l: BasicLock<G>)
  requires inv(g)
  ensures l.inv == inv
  {
    linear var at := new_atomic(false, glSome(g), (v, g) => lock_inv(v, g, inv), 0);
    l := BasicLock(at, inv);
  }
}
