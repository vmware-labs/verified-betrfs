module Ptrs {
  // Non-atomic memory

  datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
  datatype PointsToArray<V> = PointsToArray(ghost ptr: Ptr, ghost s: seq<V>)

  method {:extern} alloc<V>(v: V)
  returns (ptr: Ptr, glinear d: PointsTo<V>)
  ensures d == PointsTo(ptr, v)

  type {:extern} Ptr(!new,==)
  {
    // Ptr methods (ptr is the `this` parameter)

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

    method {:extern} free<V>(glinear d: PointsTo<V>)
    requires d.ptr == this
  }

  const {:extern} nullptr : Ptr

  glinear method {:extern} points_to_exclusive<V, W>(
      glinear inout p: PointsTo<V>,
      glinear inout q: PointsTo<W>)
  ensures p.ptr != q.ptr
  ensures p == old_p && q == old_q

  glinear method {:extern} consume_if_false<V>(glinear v: V)
  requires false
}
