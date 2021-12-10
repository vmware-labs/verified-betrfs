// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "Ptrs.s.dfy"

module {:extern "Atomics"} Atomics {
  import opened NativeTypes
  import opened BitOps
  import opened Ptrs
  import opened Options

  /*
     The 'Atomics' feature has several odd requirements which are integrated into Dafny
     via some hacks. The best way to use atomics is with the `atomic_block` syntax.
     This syntax is another hack on top of the previous hacks, but it serves to hide
     the unpleasantness from the user.
    
     The syntax looks like this:
    
     atomic_block var x := execute_atomic_fetch_add_uint8(atomic, 5) {
         ghost_acquire g;
         // ...
         ghost_release g;
     }

     A few things to note:

      * An atomic of type Atomic<V, G> means that the atomic stores a physical
        value V (which must be a type that fits in an 8-byte word)
        along with glinear value G (which can be anything).
        Every atomic variable `a` has an invariant relation between V and G,
        given by the predicate `atomic_inv(a, v, g)`.

      * Below, the execute_atomic_ methods all appear to return 4 arguments.
        However the `atomic_block` syntax deals with the latter 3 specially;
        only the first one is stored into the var `x` declared above.

      * The glinear variable `g` is declared on the `ghost_acquire` line.
        `g` has the type of `G` for an atomic of type `Atomic<V, G>`.

      * `ghost_release g` releases `g` (it doesn't have to be the same variable).
        i.e., it makes `g` unavailable after the block.

      * Within the atomic_block, there are two special ghost variables you can use:
        `old_value` and `new_value`. These both have the type of V.
        The relationship between old_value, new_value, and the return_value is
        dependent on the type of atomic update being performed. For example,
        in the fetch_add call above, we would have:

            new_value == old_value + 5 && return_value == old_value

      * At the line `ghost_acquire`, we have the assumption that inv(g, old_value)
        holds. at the line `ghost_release`, we must prove the condition that
        inv(g, new_value) holds. Thus, the user of the ghost block is responsible
        for performing some ghost-linear updates to ensure the invariant
        still holds. These updates may interact with glinear objects declared
        outside the atomic_block.

      * For something like compare_exchange, you'll probably want to use a conditional
        inside the atomic_block; one case for where the change happens and
        one where it doesn't.
    */

  type {:extern "predefined"} Atomic(!new,00)<!V, !G>
  {
    function {:extern} namespace() : nat
  }

  predicate {:extern} atomic_inv<V, G>(atomic: Atomic<V, G>, v: V, g: G)

  type GhostAtomic<!G> = Atomic<(), G>

  method {:extern} new_atomic<V, G>(
      v: V,
      glinear g: G,
      ghost inv: (V, G) -> bool,
      ghost namespace: nat)
  returns (linear a: Atomic<V, G>)
  requires inv(v, g)
  ensures forall v1, g1 :: atomic_inv(a, v1, g1) <==> inv(v1, g1)
  ensures a.namespace() == namespace

  // Note: this is intentionally not marked as 'glinear method' due to the logic
  // that the Dafny checker uses to atomic operations are not re-entrant.
  method {:extern} new_ghost_atomic<G>(
      glinear g: G,
      ghost inv: (G) -> bool,
      ghost namespace: nat)
  returns (glinear a: GhostAtomic<G>)
  requires inv(g)
  ensures forall v, g1 :: atomic_inv(a, v, g1) <==> inv(g1)
  ensures a.namespace() == namespace

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
      shared a: Atomic<V, G>,
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
      shared a: Atomic<V, G>,
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

  method {:extern} execute_atomic_load<V, G>(shared a: Atomic<V, G>)
  returns (
      ret_value: V,
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == orig_value
  ensures atomic_inv(a, orig_value, g)

  method {:extern} execute_atomic_store<V, G>(shared a: Atomic<V, G>, v: V)
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
      shared a: Atomic<uint8, G>,
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
      shared a: Atomic<uint8, G>,
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
      shared a: Atomic<uint8, G>,
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
      shared a: Atomic<uint8, G>,
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
      shared a: Atomic<uint8, G>,
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

/*
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
      shared a: Atomic<uint16, G>,
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
      shared a: Atomic<uint16, G>,
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
      shared a: Atomic<uint16, G>,
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
      shared a: Atomic<uint16, G>,
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
      shared a: Atomic<uint16, G>,
      operand: uint16) 
  returns (
      ret_value: uint16,
      ghost orig_value: uint16,
      ghost new_value: uint16,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint16(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  */

  /*
   * uint32 arithmetic and bit operations
   */

  function wrapped_add_uint32(a: uint32, b: uint32): uint32 {
    if a as int + b as int < 0x1_0000_0000 then
      a + b
    else
      (a as int + b as int - 0x1_0000_0000) as uint32
  }

  /*

  function wrapped_sub_uint32(a: uint32, b: uint32): uint32 {
    if a as int - b as int >= 0 then
      a - b
    else
      (a as int - b as int + 0x1_0000_0000) as uint32
  }

  method {:extern} execute_atomic_fetch_or_uint32<G>(
      shared a: Atomic<uint32, G>,
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
      shared a: Atomic<uint32, G>,
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
      shared a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == bit_xor_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)
  */

  method {:extern} execute_atomic_fetch_add_uint32<G>(
      shared a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_add_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)

  /*

  method {:extern} execute_atomic_fetch_sub_uint32<G>(
      shared a: Atomic<uint32, G>,
      operand: uint32) 
  returns (
      ret_value: uint32,
      ghost orig_value: uint32,
      ghost new_value: uint32,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint32(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)
  */

  /*
   * uint64 arithmetic and bit operations
   */

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

/*
  method {:extern} execute_atomic_fetch_or_uint64<G>(
      shared a: Atomic<uint64, G>,
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
      shared a: Atomic<uint64, G>,
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
      shared a: Atomic<uint64, G>,
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
      shared a: Atomic<uint64, G>,
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
      shared a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == wrapped_sub_uint64(orig_value, operand)
  ensures atomic_inv(a, orig_value, g)
  */

  /*
  method {:extern} execute_atomic_fetch_max_uint64<G>(
      shared a: Atomic<uint64, G>,
      operand: uint64) 
  returns (
      ret_value: uint64,
      ghost orig_value: uint64,
      ghost new_value: uint64,
      glinear g: G)
  ensures ret_value == orig_value
  ensures new_value == (if operand > orig_value then operand else orig_value)
  ensures atomic_inv(a, orig_value, g)
  */

  /*
   * No-op. Access the internal state without modifying the physical state.
   * May modify ghost state.
   * No observable non-ghost effects.
   */

  // Note: this is intentionally not marked as 'glinear method' due to the logic
  // that the Dafny checker uses to atomic operations are not re-entrant.
  method {:extern} execute_atomic_noop<V, G>(
      gshared a: Atomic<V, G>)
  returns (
      ghost ret_value: (),
      ghost orig_value: V,
      ghost new_value: V,
      glinear g: G)
  ensures orig_value == new_value
  ensures atomic_inv(a, orig_value, g)
}

module BitOps {
  import opened NativeTypes

  function method bit_or_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) | (b as bv8)) as uint8
  }

  function method bit_and_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) & (b as bv8)) as uint8
  }

  function method bit_xor_uint8(a: uint8, b: uint8): uint8 {
    ((a as bv8) ^ (b as bv8)) as uint8
  }

/*
  function method bit_or_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) | (b as bv16)) as uint16
  }

  function method bit_and_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) & (b as bv16)) as uint16
  }

  function method bit_xor_uint16(a: uint16, b: uint16): uint16 {
    ((a as bv16) ^ (b as bv16)) as uint16
  }

  function method bit_or_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) | (b as bv32)) as uint32
  }

  function method bit_and_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) & (b as bv32)) as uint32
  }

  function method bit_xor_uint32(a: uint32, b: uint32): uint32 {
    ((a as bv32) ^ (b as bv32)) as uint32
  }
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
}
