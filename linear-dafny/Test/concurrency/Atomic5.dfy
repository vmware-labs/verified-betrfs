// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Atomics {
  type Atomic(==)<G>
  {
    function namespace() : nat
  }

  method execute_atomic_add<G>(shared a: Atomic<G>)
  returns (
      ret_value: int,
      ghost orig_value: int,
      ghost new_value: int,
      glinear g: G)

  method execute_atomic_noop<G>(gshared a: Atomic<G>)
  returns (
      ghost ret_value: int,
      ghost orig_value: int,
      ghost new_value: int,
      glinear g: G)

  glinear method finish_atomic<G>(ghost a: Atomic<G>, ghost new_value: int, glinear g': G)
}

module Stuff {
  import opened Atomics

  method okay(shared a1: Atomic<int>, gshared a2: Atomic<int>, gshared a3: Atomic<int>)
  {
    atomic_block var ret := execute_atomic_add(a1) {
      ghost_acquire g;

      ghost var t := old_value;
      ghost var s := new_value;
      ghost var r := ret;
      glinear var g_heh := g;

      atomic_block var j1 := execute_atomic_noop(a2) {
        ghost_acquire g1;

        atomic_block var j2 := execute_atomic_noop(a3) {
          ghost_acquire g2;
          ghost_release g2;
        }

        ghost_release g1;
      }

      ghost_release g_heh;
    }
  }

  method okay2(shared a1: Atomic<int>, gshared a2: Atomic<int>, gshared a3: Atomic<int>)
  {
    atomic_block var ret := execute_atomic_add(a1) {
      ghost_acquire g;

      ghost var t := old_value;
      ghost var s := new_value;
      ghost var r := ret;
      glinear var g_heh := g;

      atomic_block var j1 := execute_atomic_noop(a2) {
        ghost_acquire g1;

        atomic_block var j2 := execute_atomic_noop(a3) {
          ghost_acquire g2;
          ghost_release g2;
        }

        ghost_release g1;
      }

      ghost_release g_heh;
    }

    atomic_block var ret2 := execute_atomic_add(a1) {
      ghost_acquire ga;

      ghost var u := old_value;
      ghost var x := new_value;
      ghost var y := ret;
      glinear var z_heh := ga;

      atomic_block var j1 := execute_atomic_noop(a2) {
        ghost_acquire g1a;

        atomic_block var j2 := execute_atomic_noop(a3) {
          ghost_acquire g2a;
          ghost_release g2a;
        }

        ghost_release g1a;
      }

      ghost_release z_heh;
    }
  }

}
