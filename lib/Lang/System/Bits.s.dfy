// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../NativeTypes.s.dfy"

// Provides access to hardware functions for bit manipulation,
// including 128-bit registers.

module Bits_s {
  import opened NativeTypes

  type Bits = seq<bool>

  function bits_of_int(n: nat, len: nat) : (p : Bits)
  ensures |p| == len
  {
    if len == 0 then
      []
    else
      [n % 2 == 1] + bits_of_int(n / 2, len-1)
  }

  function {:opaque} zeroes(l: nat) : (p: Bits)
  ensures |p| == l
  ensures forall i | 0 <= i < |p| :: !p[i]
  {
    if l == 0 then [] else zeroes(l-1) + [false]
  }

  function {:opaque} ones(l: nat) : (p: Bits)
  ensures |p| == l
  ensures forall i | 0 <= i < |p| :: p[i]
  {
    if l == 0 then [] else ones(l-1) + [true]
  }

  //// Hardware instruction specs

  function mm_cvtepu32_epi64(a: seq<bool>) : (b: seq<bool>)
  requires |a| == 128
  {
    a[0..32] + zeroes(32) + a[32..64] + zeroes(32)
  }

  // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_cvtepu32_epi64&expand=1288,1288,1565
  function method {:extern "Bits__s_Compile", "intrinsic_mm_cvtepu32_epi64"} intrinsic_mm_cvtepu32_epi64(a: uint128)
  : (b: uint128)
  ensures bits_of_int(b as int, 128)
      == mm_cvtepu32_epi64(bits_of_int(a as int, 128))

  // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_loadu_si128&expand=1288,1288,1565,3416
  function method {:extern "Bits__s_Compile", "intrinsic_mm_loadu_si128"} intrinsic_mm_loadu_si128(a: seq<uint64>, idx: uint32)
  : (b: uint128)
  requires 0 <= idx as int < |a| - 1
  ensures bits_of_int(b as int, 128)
      == bits_of_int(a[idx as int    ] as int, 64)
       + bits_of_int(a[idx as int + 1] as int, 64)

  function method {:extern "Bits__s_Compile", "intrinsic_mm_cvtsi64_si128"} intrinsic_mm_cvtsi64_si128(a: uint64)
  : (c: uint128)
  ensures bits_of_int(c as int, 128)
      == bits_of_int(a as int, 64) + zeroes(64)

  function method {:extern "Bits__s_Compile", "intrinsic_mm_cvtsi128_si64"} intrinsic_mm_cvtsi128_si64(a: uint128)
  : (c: uint64)
  ensures bits_of_int(c as int, 64) == bits_of_int(a as int, 128)[0..64]
}
