module Ptrs {
  // Non-atomic memory

  datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
  datatype PointsToLinear<V> =
    | PointsToLinear(ghost ptr: Ptr, ghost v: V)
    | PointsToEmpty(ghost ptr: Ptr)
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

    method {:extern} write_linear<V>(glinear inout d: PointsToLinear<V>, linear v: V)
    requires old_d.PointsToEmpty?
    requires old_d.ptr == this
    ensures d.PointsToLinear? && d.ptr == this && d.v == v

    method {:extern} read_linear<V>(glinear inout d: PointsToLinear<V>)
    returns (linear v: V)
    requires old_d.PointsToLinear?
    requires old_d.ptr == this
    ensures v == old_d.v
    ensures d.PointsToEmpty? && d.ptr == this

    method {:extern} read_shared<V>(gshared d: PointsToLinear<V>)
    returns (shared v: V)
    requires d.PointsToLinear?
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

  method {:extern} alloc<V>(v: V)
  returns (ptr: Ptr, glinear d: PointsTo<V>)
  ensures d == PointsTo(ptr, v)

  method {:extern} alloc_linear<V>(linear v: V)
  returns (ptr: Ptr, glinear d: PointsToLinear<V>)
  ensures d == PointsToLinear(ptr, v)

  glinear method {:extern} dispose_anything<V>(glinear v: V) // TODO better file for this
}
