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

  method execute_atomic_noop<G>(ghost a: Atomic<G>)
  returns (
      ghost ret_value: int,
      ghost orig_value: int,
      ghost new_value: int,
      glinear g: G)

  glinear method finish_atomic<G>(ghost a: Atomic<G>, ghost new_value: int, glinear g': G)
}

module Stuff {
  import opened Atomics

  method okay(shared a1: Atomic<int>, shared a2: Atomic<int>, shared a3: Atomic<int>)
  returns (x: int)
  {
    var moo := 5;

    atomic_block var ret := execute_atomic_add(a1) {
      ghost_acquire g;

      var t := 7;
      var s := 9;

      if ret == 5 {
        glinear var x;
        x := g;
        g := x;
      }

      ghost_release g;
    }

    x := moo;
  }

  glinear datatype glOption<V> = Some(glinear v: V) | None

  glinear method inout_method<V>(glinear inout x: V)
  glinear method inout_method2<V>(glinear inout x: glOption<V>)

  glinear method dispose_t<V>(glinear x: V)

  glinear method get_some_object()
  returns (glinear o: glOption<int>)

  method okay2(shared a1: Atomic<glOption<int>>)
  {
    glinear var x := get_some_object(); 
    inout_method(inout x);
    dispose_t(x);

    atomic_block var ret := execute_atomic_add(a1) {
      ghost_acquire g;

      inout_method(inout g);

      glinear match g {
        case None => { }
        case Some(t) => {
          inout_method(inout t);
          dispose_t(t);
        }
      }

      g := get_some_object();

      ghost_release g;
    }
  }

  glinear datatype Foo = Foo(glinear x: int, ghost z: int)

  method okay3(shared a1: Atomic<glOption<int>>, glinear foo: Foo)
  returns (glinear x: int)
  {
    atomic_block var ret := execute_atomic_add(a1) {
      ghost_acquire g;

      glinear var Foo(x', z') := foo;
      x := x';

      ghost_release g;
    }
  }

}
