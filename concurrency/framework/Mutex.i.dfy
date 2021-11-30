// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Atomic.s.dfy"
include "Cells.s.dfy"

module {:extern "Mutexes"} Mutexes {
  import opened GlinearOption
  import opened LinearCells
  import opened Atomics
  import opened Ptrs

  /*
   * Mutex that protects a piece of data with some invariant.
   */

  predicate AtInv<V(!new)>(v: bool, g: glOption<LCellContents<V>>, cell: LinearCell<V>,
      inv: (V) -> bool)
  {
    && (v ==> g.glNone?)
    && (!v ==> g.glSome?
        && g.value.lcell == cell
        && g.value.v.Some?
        && inv(g.value.v.value)
    )
  }

  linear datatype Mutex<!V(!new)> = Mutex(
      linear at: Atomic<bool, glOption<LCellContents<V>>>,
      linear cell: LinearCell<V>,
      ghost inv: (V) -> bool
  )
  {
    predicate WF() {
      forall v, g :: atomic_inv(at, v, g) <==> AtInv(v, g, cell, inv)
    }

    /*
     * `acquire`
     * Note that there is no deadlock prevention.
     */

    shared method {:extern} acquire()
    returns (linear v: V, glinear handle: MutexHandle<V>)
    requires this.WF()
    ensures this.inv(v)
    ensures handle.m == this
    decreases *
    {
      glinear var go : glOption<LCellContents<V>> := glNone;
      var done := false;
      while !done
      invariant !done ==> go.glNone?
      invariant done ==> go.glSome?
      invariant done ==> go.value.lcell == cell
      invariant done ==> go.value.v.Some?
      invariant done ==> inv(go.value.v.value)
      decreases *
      {
        atomic_block done := execute_atomic_compare_and_set_strong(at, false, true)
        {
          ghost_acquire g;
          if done {
            glinear var x := g;
            g := go;
            go := x;
          }
          ghost_release g;
        }
      }

      glinear var go0;
      v, go0 := take_lcell(cell, unwrap_value(go));
      handle := MutexHandle(this, go0);
    }

    /*
     * `release`
     */

    shared method {:extern} release(linear v: V, glinear handle: MutexHandle<V>)
    requires this.WF()
    requires this.inv(v)
    requires handle.m == this
    requires handle.WF()
    {
      glinear var MutexHandle(m, cc) := handle;
      cc := give_lcell(cell, cc, v);
      atomic_block var _ := execute_atomic_store(at, false)
      {
        ghost_acquire g;
        dispose_anything(g);
        g := glSome(cc);
        assert AtInv(false, g, cell, inv);
        ghost_release g;
      }
    }
  }

  /*
   * Constructor for a new mutex.
   * Parameters:
   *  v: Initial value to store in the mutex.
   *     In general, V might be a datatype that contains both
   *     physical and ghost state.
   *  inv: Predicate over V that must hold for any value stored
   *     behind this mutex.
   */

  method {:extern} new_mutex<V(!new)>(linear v: V, ghost inv: (V) -> bool)
  returns (linear m: Mutex<V>)
  requires inv(v)
  ensures m.inv == inv
  ensures m.WF()
  {
    linear var lcell;
    glinear var cellContents;
    lcell, cellContents := new_lcell();
    cellContents := give_lcell(lcell, cellContents, v);
    linear var at := new_atomic(false, glSome(cellContents), (v, g) => AtInv(v, g, lcell, inv), 0);
    m := Mutex(at, lcell, inv);
  }

  /*
   * A MutexHandle is a special ghost object you get when you
   * call `acquire` on a Mutex. Its only purpose is that it
   * allows you to call `release` again later.
   * This requirement allows us to enforce that no client
   * calls a `release` without previously calling `acquire`.
   */

  glinear datatype MutexHandle<!V(!new)> = MutexHandle(
      ghost m: Mutex<V>,
      glinear contents: LCellContents<V>)
  {
    predicate WF() {
      && contents.lcell == m.cell
      && contents.v.None?
    }
  }
}
