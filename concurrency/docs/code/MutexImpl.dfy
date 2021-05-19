include "Ptrs.s.dfy"
include "Atomic.s.dfy"

module Mutexes {
  import opened Ptrs
  import opened Atomics

  glinear datatype glOption<V> = Some(glinear value: V) | None

  predicate ainv<V>(store: Ptr, inv: (V) -> bool, v_exc: bool, g: glOption<PointsTo<V>>)
  {
    && (!v_exc ==> (g.Some? && g.value.ptr == store && inv(g.value.v)))
    && (v_exc ==> g.None?)
  }

  datatype Mutex<!V(!new)> = Mutex(
      exc_bit: Atomic<bool, glOption<PointsTo<V>>>,
      store: Ptr,
      ghost inv: (V) -> bool)
  {
    predicate well_formed() {
      forall v_exc, g :: atomic_inv(exc_bit, v_exc, g) <==>
          ainv(store, inv, v_exc, g)
    }
  }

  method {:extern} new_mutex<V(!new)>(v: V, ghost inv: (V) -> bool)
  returns (m: Mutex)
  requires inv(v)
  ensures m.inv == inv
  {
    var store;
    glinear var points_to;
    store, points_to := alloc(v);
    var atomic_cell := new_atomic(false, Some(points_to), (v, g) => ainv(store, inv, v, g), {});
    m := Mutex(atomic_cell, store, inv);
  }

  type MutexHandle<V> = PointsTo<V>

  predicate is_handle_for<V(!new)>(handle: MutexHandle<V>, m: Mutex<V>)
  {
    handle.ptr == m.store
  }

  /*
   * `acquire`
   * Provides the client with the guarantee that the data
   * inside meets the invariant.
   */

  method acquire<V(!new)>(m: Mutex<V>)
  returns (v: V, glinear handle: MutexHandle<V>)
  decreases *
  requires m.well_formed()
  ensures m.inv(v)
  ensures is_handle_for(handle, m)
  {
    var success := false;

    glinear var handle_opt: glOption<PointsTo<V>> := None;
    
    while !success
    invariant !success ==> handle_opt == None
    invariant success ==> handle_opt.Some?
          && handle_opt.value.ptr == m.store
          && m.inv(handle_opt.value.v)
    decreases *
    {
      atomic_block success := execute_atomic_compare_and_set_strong(m.exc_bit, false, true) {
        ghost_acquire g;

        if success {
          glinear var tmp := handle_opt;
          handle_opt := g;
          g := tmp;
        }

        ghost_release g;
      }
    }

    glinear var Some(handle_out) := handle_opt;
    handle := handle_out;

    v := m.store.read(handle);
  }

  /*
   * `release`
   * The client must ensure that the data meets the invariant.
   */

  method {:extern} release<V(!new)>(m: Mutex<V>, v: V, glinear handle: MutexHandle<V>)
  requires m.well_formed()
  requires m.inv(v)
  requires is_handle_for(handle, m)
  {
    glinear var handle' := handle;
    m.store.write(inout handle', v);

    atomic_block var _ := execute_atomic_store(m.exc_bit, false) {
      ghost_acquire g;

      glinear match g {
        case None => { /* we must be in this case */ }
        case Some(internal_ptr) => {
          points_to_exclusive(inout handle', inout internal_ptr);
          assert false;
          consume_if_false(internal_ptr);
        }
      }

      g := Some(handle');
      assert ainv(m.store, m.inv, false, g);
      ghost_release g;
    }
  }
}
