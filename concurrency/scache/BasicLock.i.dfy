// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Atomic.s.dfy"
include "../../lib/Base/LinearOption.i.dfy"

module BasicLockImpl {
  import opened LinearOption
  import opened AtomicSpec

  type AtomicLock<G(!new,==)> = Atomic<bool, lOption<G>>

  predicate lock_inv<G>(v: bool, g: lOption<G>, fn: G -> bool)
  {
    && (v == true  ==> g.lNone?)
    && (v == false ==> g.lSome? && fn(g.value))
  }

  datatype BasicLock<G(!new,==)> = BasicLock(a: AtomicLock<G>)
  {
    predicate inv(fn: G -> bool) {
      forall v: bool, g: lOption<G> ::
          atomic_inv(a, v, g) <==> lock_inv(v, g, fn)
    }
  }

  /*
   * Acquire if possible; don't block.
   */
  method try_acquire<G>(l: BasicLock<G>, ghost inv: G -> bool)
  returns (linear g: lOption<G>)
  requires l.inv(inv)
  ensures g.lSome? ==> inv(g.value)

  method release<G>(l: BasicLock<G>, ghost inv: G -> bool, g: G)
  ensures l.inv(inv)
  ensures inv(g)
}
