// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Atomics {
  type Atomic(==)<G>
  {
    function namespace() : nat
  }

  method execute_atomic_add<G>(a: Atomic<G>)
  returns (
      ret_value: int,
      ghost orig_value: int,
      ghost new_value: int,
      glinear g: G)

  method execute_atomic_noop<G>(a: Atomic<G>)
  returns (
      ret_value: int,
      ghost orig_value: int,
      ghost new_value: int,
      glinear g: G)

  glinear method finish_atomic<G>(ghost a: Atomic<G>, ghost new_value: int, glinear g': G)

  method bad(a1: Atomic<int>, a2: Atomic<int>, a3: Atomic<int>)
  {
    var ret1;
    ghost var b1, c1;
    glinear var d1;

    var ret2;
    ghost var b2, c2;
    glinear var d2;

    ret1, b1, c1, d1 := execute_atomic_add(a1);
    ret2, b2, c2, d2 := execute_atomic_noop(a2); // ERROR
    finish_atomic(a2, c2, d2);
    finish_atomic(a1, c1, d1);
  }

  method okay(a1: Atomic<int>, a2: Atomic<int>, a3: Atomic<int>)
  {
    var ret1;
    ghost var b1, c1;
    glinear var d1;

    var ret2;
    ghost var b2, c2;
    glinear var d2;

    var ret3;
    ghost var b3, c3;
    glinear var d3;

    ret1, b1, c1, d1 := execute_atomic_add(a1);
    assert a1.namespace() != a2.namespace();
    ret2, b2, c2, d2 := execute_atomic_noop(a2);
    assert a1.namespace() != a3.namespace();
    assert a2.namespace() != a3.namespace();
    ret3, b3, c3, d3 := execute_atomic_noop(a3);
    finish_atomic(a3, c3, d3);
    finish_atomic(a2, c2, d2);
    finish_atomic(a1, c1, d1);
  }

  method bad2(a1: Atomic<int>, a2: Atomic<int>, a3: Atomic<int>)
  {
    var ret1;
    ghost var b1, c1;
    glinear var d1;

    var ret2;
    ghost var b2, c2;
    glinear var d2;

    var ret3;
    ghost var b3, c3;
    glinear var d3;

    ret1, b1, c1, d1 := execute_atomic_add(a1);
    assert a1.namespace() != a2.namespace();
    ret2, b2, c2, d2 := execute_atomic_noop(a2);
    assert a1.namespace() != a3.namespace();
    assert a2.namespace() != a2.namespace(); // ERROR
    ret3, b3, c3, d3 := execute_atomic_noop(a3);
    finish_atomic(a3, c3, d3);
    finish_atomic(a2, c2, d2);
    finish_atomic(a1, c1, d1);
  }


}
