include "../../lib/Lang/NativeTypes.s.dfy"

module AtomicSpec {
  type {:extern} Atomic<V, G>

  predicate {:extern} atomic_inv<V, G>(atomic: Atomic<V, G>, v: V, g: G)

  method {:extern} new_atomic<V, G>(v: V, g: G,
      inv: (V, G) -> bool)
  returns (a: Atomic<V, G>)
  requires inv(v, g)
  ensures forall v1, g1 :: atomic_inv(a, v1, g1) <==> inv(v1, g1)

  // TODO haven't found a good way to specify this right now, missing
  // language support to do the things I'd really like.
  // See the usages of this method for the unenforced jank.
  method {:extern} compare_and_set<V, G>(
      a: Atomic<V, G>,
      v1: V,
      v2: V)
  returns (did_set: bool)

  method {:extern} atomic_read<V, G>(a: Atomic<V, G>)
  returns (v: V)

  method {:extern} atomic_write<V, G>(a: Atomic<V, G>, v: V)

  import opened NativeTypes

  function method bit_or(a: uint8, b: uint8): uint8 {
    ((a as bv8) | (b as bv8)) as uint8
  }

  function method bit_and(a: uint8, b: uint8): uint8 {
    ((a as bv8) & (b as bv8)) as uint8
  }

  function method bit_xor(a: uint8, b: uint8): uint8 {
    ((a as bv8) ^ (b as bv8)) as uint8
  }

  method {:extern} fetch_or<G>(
      a: Atomic<uint8, G>,
      v: uint8) 
  returns (orig_value: uint8)

  method {:extern} fetch_and<G>(
      a: Atomic<uint8, G>,
      v: uint8) 
  returns (orig_value: uint8)

  method {:extern} fetch_xor<G>(
      a: Atomic<uint8, G>,
      v: uint8) 
  returns (orig_value: uint8)

  method {:extern} fetch_add_uint32<G>(
      a: Atomic<uint32, G>,
      v: uint32)
  returns (orig_value: uint32)

  method {:extern} fetch_add_uint8<G>(
      a: Atomic<uint8, G>,
      v: uint8)
  returns (orig_value: uint8)

  method {:extern} fetch_sub_uint8<G>(
      a: Atomic<uint8, G>,
      v: uint8)
  returns (orig_value: uint8)
}
