include "../framework/Atomic.s.dfy"
include "../framework//GlinearOption.i.dfy"

module BasicLockImpl {
  import opened GlinearOption
  import opened Atomics

  type AtomicLock<!G(!new)> = Atomic<bool, glOption<G>>

  predicate lock_inv<G>(v: bool, g: glOption<G>, fn: G -> bool)
  {
    && (v == true  ==> g.glNone?)
    && (v == false ==> g.glSome? && fn(g.value))
  }

  datatype pre_BasicLock<!G(!new)> = BasicLock(a: AtomicLock<G>, ghost inv: G -> bool)
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

  method try_acquire<G(!new)>(l: BasicLock<G>)
  returns (glinear g: glOption<G>)
  ensures g.glSome? ==> l.inv(g.value)

  method release<G(!new)>(l: BasicLock<G>, glinear g: G)
  requires l.inv(g)
}
