// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Ptrs {
  // Non-atomic memory

  datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
  datatype PointsToArray<V> = PointsToArray(ghost ptr: Ptr, ghost s: seq<V>)

  type {:extern} Ptr(!new,==)

  method {:extern} write<V>(p: Ptr, glinear inout d: PointsTo<V>, v: V)
  requires old_d.ptr == p
  ensures d.ptr == p
  ensures d.v == v

  method {:extern} read<V>(p: Ptr, gshared d: PointsTo<V>)
  returns (v: V)
  requires d.ptr == p
  ensures v == d.v

  method {:extern} index_write<V>(p: Ptr, glinear inout d: PointsToArray, i: int, v: V)
  requires old_d.ptr == p
  requires 0 <= i < |old_d.s|
  ensures d == old_d.(s := old_d.s[i := v])

  method {:extern} index_read<V>(p: Ptr, gshared d: PointsToArray<V>, i: int)
  returns (v: V)
  requires d.ptr == p
  requires 0 <= i < |d.s|
  ensures v == d.s[i]

  const {:extern} nullptr : Ptr

  method test(p: Ptr, glinear inout d: PointsToArray<int>)
  requires old_d.ptr == p
  requires old_d.s == [1, 2]
  {
    index_write(p, inout d, 0, 5);
    assert d.s == [5, 2];
    assert d.s == [4, 2]; // ERROR
  }

  method test2(p: Ptr, glinear inout d: PointsToArray<int>)
  requires old_d.ptr == p
  requires old_d.s == [1, 2]
  {
    index_write(p, inout d, 6, 5); // ERROR (precondition)
  }
}

module Ptrs2 {
  // Non-atomic memory

  datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
  datatype PointsToArray<V> = PointsToArray(ghost ptr: Ptr, ghost s: seq<V>)

  type {:extern} Ptr(!new,==)
  {
    method {:extern} write<V>(glinear inout d: PointsTo<V>, v: V)
    requires old_d.ptr == this
    ensures d.ptr == this
    ensures d.v == v

    method {:extern} read<V>(gshared d: PointsTo<V>)
    returns (v: V)
    requires d.ptr == this
    ensures v == d.v

    method {:extern} index_write<V>(glinear inout d: PointsToArray, i: int, v: V)
    requires old_d.ptr == this
    requires 0 <= i < |old_d.s|
    ensures d == old_d.(s := old_d.s[i := v])

    method {:extern} index_read<V>(gshared d: PointsToArray<V>, i: int)
    returns (v: V)
    requires d.ptr == this
    requires 0 <= i < |d.s|
    ensures v == d.s[i]
  }

  const {:extern} nullptr : Ptr

  method test(p: Ptr, glinear inout d: PointsToArray<int>)
  requires old_d.ptr == p
  requires old_d.s == [1, 2]
  {
    p.index_write(inout d, 0, 5);
    assert d.s == [5, 2];
    assert d.s == [4, 2]; // ERROR
  }

  method test2(p: Ptr, glinear inout d: PointsToArray<int>)
  requires old_d.ptr == p
  requires old_d.s == [1, 2]
  {
    p.index_write(inout d, 6, 5); // ERROR (precondition)
  }

}
