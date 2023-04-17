// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Mutexes {
  type {:extern "Mutex"} Mutex<V>
  {
    predicate {:extern} inv(v: V)

    method {:extern} acquire()
    returns (linear v: V, glinear handle: MutexHandle<V>)
    ensures this.inv(v)
    ensures handle.m == this

    method {:extern} release(linear v: V, glinear handle: MutexHandle<V>)
    requires this.inv(v)
    requires handle.m == this
  }

  method {:extern} new_mutex<V>(linear v: V, ghost inv: (V) -> bool)
  returns (m: Mutex)
  requires inv(v)
  ensures m.inv == inv

  datatype MutexHandle<V> = MutexHandle(m: Mutex<V>)
}

module Client {
  import opened Mutexes

  linear datatype Value = Value(
    x: int,
    glinear gx: int)

  method doStuff(m: Mutex<Value>, glinear new_gx: int, glinear new_gx2: int)
  returns (glinear old_gx: int)
  requires new_gx == 5
  requires m.inv == ((t: Value) => t.x == t.gx)
  {
    linear var v;
    glinear var handle;

    v, handle := m.acquire();

    linear var Value(x, gx) := v;

    old_gx := gx;

    m.release(Value(5, new_gx), handle);

    m.release(Value(5, new_gx2), handle); // ERROR
  }
}
