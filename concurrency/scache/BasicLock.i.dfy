include "../framework/Atomic.s.dfy"
include "../framework//GlinearOption.i.dfy"

module BasicLockImpl {
  import opened GlinearOption
  import opened Atomics

  type AtomicLock<G(!new,==)> = Atomic<bool, glOption<G>>

  predicate lock_inv<G>(v: bool, g: glOption<G>, fn: G -> bool)
  {
    && (v == true  ==> g.glNone?)
    && (v == false ==> g.glSome? && fn(g.value))
  }

  datatype BasicLock<G(!new)> = BasicLock(a: AtomicLock<G>)
  {
    predicate inv(fn: G -> bool) {
      forall v: bool, g: glOption<G> ::
          atomic_inv(a, v, g) <==> lock_inv(v, g, fn)
    }
  }

  /*
   * Acquire if possible; don't block.
   */
  method try_acquire<G(!new)>(l: BasicLock<G>, ghost inv: G -> bool)
  returns (linear g: glOption<G>)
  requires l.inv(inv)
  ensures g.glSome? ==> inv(g.value)

  method release<G(!new)>(l: BasicLock<G>, ghost inv: G -> bool, g: G)
  ensures l.inv(inv)
  ensures inv(g)
}
