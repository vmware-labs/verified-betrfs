// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

module {:extern "Atomics"} Atomics {
  newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x1_0000_0000_0000_0000
  newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
  newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
  newtype{:nativeType "byte"} uint8 = i:int | 0 <= i < 0x100

  type Atomic<V, G>

  predicate {:extern} atomic_inv<V, G>(atomic: Atomic<V, G>, v: V, g: G)

  method {:extern} new_atomic<V, G>(
      v: V,
      glinear g: G,
      ghost inv: (V, G) -> bool)
  returns (a: Atomic<V, G>)
  requires inv(v, g)
  ensures forall v1, g1 :: atomic_inv(a, v1, g1) <==> inv(v1, g1)

  glinear method {:extern} finish_atomic<V, G>(
      ghost a: Atomic<V, G>,
      ghost new_value: V,
      glinear g: G)
  requires atomic_inv(a, new_value, g)

  /*
   * Compare and set
   *
   * Note: the 'weak' version has nothing to do with 'weak memory models'.
   * It's still a sequentially-consistent operation. The difference is that
   * the 'strong' version always succeeds when the found value == the expected value
   * Whereas the 'weak' verison may fail in that case.
   * (Naturally, neither version will ever succeed when the
   * found value != the expected value)
   */

  method {:extern} execute_atomic_compare_and_set_strong<V, G>(
      a: Atomic<V, G>,
      v1: V,
      v2: V)
  returns (
      ret_value: bool,
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures ret_value ==> orig_value == v1 && new_value == v2
  ensures !ret_value ==> orig_value != v1 && new_value == orig_value
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_compare_and_set_weak<V, G>(
      a: Atomic<V, G>,
      v1: V,
      v2: V)
  returns (
      ret_value: bool,
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures ret_value ==> orig_value == v1 && new_value == v2
  ensures !ret_value ==> new_value == orig_value
  ensures atomic_inv(a, orig_value, g)

  /*
   * Load and store
   */

  method {:extern} execute_atomic_load<V, G>(a: Atomic<V, G>)
  returns (
      ret_value: V,
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == orig_value
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_store<V, G>(a: Atomic<V, G>, v: V)
  returns (
      ghost ret_value: (),
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures new_value == v
  ensures atomic_inv(a, orig_value, g)

  /*
   * uint8 arithmetic and bit operations
   */

  function method bit_or_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) | (b as bv8)) as uint8
  }

  function method bit_and_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) & (b as bv8)) as uint8
  }

  function method bit_xor_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) ^ (b as bv8)) as uint8
  }

  function wrapped_add_uint8(a: uint8, b: uint8): uint8 {
    if a as int + b as int < 0x1_00 then
      a + b
    else
      (a as int + b as int - 0x1_00) as uint8
  }

  function wrapped_sub_uint8(a: uint8, b: uint8): uint8 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_00) as uint8
  }

  method {:extern} execute_atomic_fetch_or_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_or_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_and_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_and_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_xor_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_xor_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_add_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_add_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_sub_uint8<G>(
      a: Atomic<uint8, G>,
      operand: uint8) 
  returns (
      ret_value: uint8,
      ghost orig_value: uint8,
      ghost new_value: uint8,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint8(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  /*
   * uint16 arithmetic and bit operations
   */

  function method bit_or_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) | (b as bv16)) as uint16
  }

  function method bit_and_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) & (b as bv16)) as uint16
  }

  function method bit_xor_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) ^ (b as bv16)) as uint16
  }

  function wrapped_add_uint16(a: uint16, b: uint16): uint16 {
    if a as int + b as int < 0x1_0000 then
      a + b
    else
      (a as int + b as int - 0x1_0000) as uint16
  }

  function wrapped_sub_uint16(a: uint16, b: uint16): uint16 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_0000) as uint16
  }

  method {:extern} execute_atomic_fetch_or_uint16<G>(
      a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_or_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_and_uint16<G>(
      a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_and_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_xor_uint16<G>(
      a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_xor_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_add_uint16<G>(
      a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_add_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_sub_uint16<G>(
      a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  /*
   * uint32 arithmetic and bit operations
   */

  function method bit_or_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) | (b as bv32)) as uint32
  }

  function method bit_and_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) & (b as bv32)) as uint32
  }

  function method bit_xor_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) ^ (b as bv32)) as uint32
  }

  function wrapped_add_uint32(a: uint32, b: uint32): uint32 {
    if a as int + b as int < 0x1_0000_0000 then
      a + b
    else
      (a as int + b as int - 0x1_0000_0000) as uint32
  }

  function wrapped_sub_uint32(a: uint32, b: uint32): uint32 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_0000_0000) as uint32
  }

  method {:extern} execute_atomic_fetch_or_uint32<G>(
      a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_or_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_and_uint32<G>(
      a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_and_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_xor_uint32<G>(
      a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_xor_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_add_uint32<G>(
      a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_add_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_sub_uint32<G>(
      a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  /*
   * uint64 arithmetic and bit operations
   */

  function method bit_or_uint64(a: uint64, b: uint64): uint64 {
    ((a as bv64) | (b as bv64)) as uint64
  }

  function method bit_and_uint64(a: uint64, b: uint64): uint64 {
    ((a as bv64) & (b as bv64)) as uint64
  }

  function method bit_xor_uint64(a: uint64, b: uint64): uint64 {
    ((a as bv64) ^ (b as bv64)) as uint64
  }

  function wrapped_add_uint64(a: uint64, b: uint64): uint64 {
    if a as int + b as int < 0x1_0000_0000_0000_0000 then
      a + b
    else
      (a as int + b as int - 0x1_0000_0000_0000_0000) as uint64
  }

  function wrapped_sub_uint64(a: uint64, b: uint64): uint64 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_0000_0000_0000_0000) as uint64
  }

  method {:extern} execute_atomic_fetch_or_uint64<G>(
      a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_or_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_and_uint64<G>(
      a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_and_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_xor_uint64<G>(
      a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_xor_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_add_uint64<G>(
      a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_add_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_fetch_sub_uint64<G>(
      a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  /*
   * No-op. Access the internal state without modifying the physical state.
   * May modify ghost state.
   * No observable non-ghost effects.
   */

  method {:extern} execute_atomic_noop<V, G>(
      a: Atomic<V, G>)
  returns (
      ghost ret_value: (),
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures orig_value == new_value
  ensures atomic_inv(a, orig_value, g)
}
