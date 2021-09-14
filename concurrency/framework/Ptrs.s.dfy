include "../../lib/Lang/NativeTypes.s.dfy"
include "GlinearOption.i.dfy"
include "GlinearSeq.s.dfy"

module {:extern "Ptrs"} Ptrs {
  import opened NativeTypes
  import opened GlinearOption
  import opened GlinearSeq

  // Non-atomic data-race-free memory

  datatype PointsTo<V> = PointsTo(ghost ptr: Ptr, ghost v: V)
  datatype PointsToLinear<V> =
    | PointsToLinear(ghost ptr: Ptr, ghost v: V)
    | PointsToEmpty(ghost ptr: Ptr)
  datatype PointsToArray<V> = PointsToArray(ghost ptr: Ptr, ghost s: seq<V>)

  type {:extern "struct"} Ptr(!new, ==, 00)
  {
    function {:extern} as_nat() : nat

    predicate aligned(n: nat)
    {
      n >= 1 && as_nat() % n == 0
    }

    /*
    // allocation ranges from base .. base + size * length
    // ptr = base + size * idx
    function {:extern} base() : nat
    function {:extern} size() : nat
    function {:extern} length() : nat
    function {:extern} idx() : nat ensures 0 <= idx() < size()

    function method {:extern} add(k: int64) : (p: Ptr)
    requires k % size() == 0
    requires 0 <= idx() + (k / size()) < size()
    ensures p.base() == base()
    ensures p.size() == size()
    ensures p.length() == length()
    ensures p.idx() == idx() + (k / size())

    function method {:extern} diff(ptr: Ptr) : (d: uint64)
    requires ptr.base() == base()
    requires ptr.size() == size()
    requires idx() >= ptr.idx()
    ensures d == (idx() - ptr.idx()) * size()

    predicate aligned(n: nat) {
      (base() + size() * idx()) % n == 0
    }

    function method {:extern} ptr_eq
    */

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

  const {:extern "null_ptr"} nullptr : Ptr

  method {:extern} alloc<V>(v: V)
  returns (ptr: Ptr, glinear d: PointsTo<V>)
  ensures d == PointsTo(ptr, v)

  method {:extern} alloc_linear<V>(linear v: V)
  returns (ptr: Ptr, glinear d: PointsToLinear<V>)
  ensures d == PointsToLinear(ptr, v)

  method {:extern} alloc_array_aligned<V>(len: uint64, init_value: V, alignment: uint64)
  returns (ptr: Ptr, glinear d: PointsToArray<V>)
  requires alignment == 4096 // XXX(travis): should probably be "a power of 2" or something
  ensures ptr.aligned(alignment as nat)
  ensures d == PointsToArray(ptr, seq(len, (i) => init_value))

  function method {:extern} ptr_diff(ptr1: Ptr, ptr2: Ptr) : (i: uint64)
  requires ptr1.as_nat() >= ptr2.as_nat()
  ensures i as nat == ptr1.as_nat() - ptr2.as_nat()

  function method {:extern} ptr_add(ptr1: Ptr, i: uint64) : (ptr2: Ptr)
  requires ptr1.as_nat() + i as int < 0x1_0000_0000_0000_0000
  ensures ptr2.as_nat() == ptr1.as_nat() + i as nat

  function method {:extern} sizeof<V>() : uint64

  glinear method {:extern} array_to_individual<V>(glinear pta: PointsToArray<V>)
  returns (glinear s: glseq<PointsTo<V>>)
  ensures s.len() == |pta.s|
  ensures forall i | 0 <= i < |pta.s| ::
      && s.has(i)
      && s.get(i).ptr.as_nat() == pta.ptr.as_nat() + i * sizeof<V>() as nat
      && s.get(i).v == pta.s[i]

  glinear method {:extern} dispose_anything<V>(glinear v: V) // TODO better file for this
}
