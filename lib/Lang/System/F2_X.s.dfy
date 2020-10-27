include "../NativeTypes.s.dfy"
include "Bits.s.dfy"

// Provides access to hardware functions for mod 2 polynomial
// multiplication and division.

module F2_X_s {
  import opened NativeTypes
  import opened Bits_s

  function {:opaque} reverse(s: Bits) : (s' : Bits)
  ensures |s'| == |s|
  ensures forall i | 0 <= i < |s'| :: s'[i] == s[|s| - 1 - i]
  {
    if |s| == 0 then []
    else reverse(s[1..]) + [s[0]]
  }

  function bool_xor(a: bool, b: bool) : (c: bool)
  {
    (a && !b) || (!a && b)
  }

  function {:opaque} xor(p: Bits, q: Bits) : (r : Bits)
  requires |p| == |q|
  ensures |r| == |p|
  ensures forall i | 0 <= i < |r| :: r[i] == bool_xor(p[i], q[i])
  {
    if |p| == 0 then
      []
    else
     xor(p[..|p|-1], q[..|q|-1]) + [bool_xor(p[|p|-1], q[|q|-1])]
  }

  function extend(p: Bits, l: nat) : (p' : Bits)
  requires l >= |p|
  {
    p + zeroes(l-|p|)
  }

  function bits_get(p: Bits, i: nat) : bool
  {
    i < |p| && p[i]
  }

  function mul_F2_X_digit_partial(p: Bits, q: Bits, i: nat, j: nat) : bool
  requires j <= i+1
  decreases i + 1 - j
  {
    if j == i+1 then
      false
    else
      bool_xor(
        (bits_get(p, j) && bits_get(q, i-j)),
        mul_F2_X_digit_partial(p, q, i, j+1)
      )
  }

  function mul_F2_X_digit(p: Bits, q: Bits, i: nat) : bool
  {
    mul_F2_X_digit_partial(p, q, i, 0)
  }

  function {:opaque} mul_F2_X(p: Bits, q: Bits) : (r : Bits)
  ensures |r| == |p| + |q|
  ensures forall i | 0 <= i < |r| :: r[i] == mul_F2_X_digit(p, q, i)
  {
    seq(|p| + |q|, i requires 0 <= i => mul_F2_X_digit(p, q, i))
  }

  function shift(p: Bits, t: nat) : (r: Bits)
  {
    zeroes(t) + p
  }

  function mod_F2_X(p: Bits, q: Bits) : (r : Bits)
  requires |q| > 0
  ensures |r| == |q| - 1
  decreases |p|
  {
    if |p| <= |q| - 1 then
      p + zeroes(|q| - 1 - |p|)
    else (
      if p[|p|-1] then
        mod_F2_X(xor(p, shift(q, |p|-|q|))[..|p|-1], q)
      else
        mod_F2_X(p[..|p|-1], q)
    )
  }

  function mm_crc32_u8(acc: Bits, b: Bits) : Bits
  requires |acc| == 32
  requires |b| == 8
  {
    // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_crc32_u8
    reverse(mod_F2_X(
      xor(shift(reverse(b), 32), shift(reverse(acc), 8)),
      bits_of_int(0x1_1EDC_6F41, 33)
    ))
  }

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_crc32_u8"} intrinsic_mm_crc32_u8(acc: uint32, b: uint8)
  : (acc': uint32)
  ensures bits_of_int(acc' as int, 32) ==
    mm_crc32_u8(
      bits_of_int(acc as int, 32),
      bits_of_int(b as int, 8)
    )

  function mm_crc32_u16(acc: Bits, b: Bits) : Bits
  requires |acc| == 32
  requires |b| == 16
  {
    // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_crc32_u16&expand=1286
    reverse(mod_F2_X(
      xor(shift(reverse(b), 32), shift(reverse(acc), 16)),
      bits_of_int(0x1_1EDC_6F41, 33)
    ))
  }

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_crc32_u16"} intrinsic_mm_crc32_u16(acc: uint32, b: uint16)
  : (acc': uint32)
  ensures bits_of_int(acc' as int, 32) ==
    mm_crc32_u16(
      bits_of_int(acc as int, 32),
      bits_of_int(b as int, 16)
    )

  function mm_crc32_u32(acc: Bits, b: Bits) : Bits
  requires |acc| == 32
  requires |b| == 32
  {
    // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_crc32_u32&expand=1287
    reverse(mod_F2_X(
      xor(shift(reverse(b), 32), shift(reverse(acc), 32)),
      bits_of_int(0x1_1EDC_6F41, 33)
    ))
  }

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_crc32_u32"} intrinsic_mm_crc32_u32(acc: uint32, b: uint32)
  : (acc': uint32)
  ensures bits_of_int(acc' as int, 32) ==
    mm_crc32_u32(
      bits_of_int(acc as int, 32),
      bits_of_int(b as int, 32)
    )

  function mm_crc32_u64(acc: Bits, b: Bits) : Bits
  requires |acc| == 32
  requires |b| == 64
  {
    // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=crc32_u64&expand=1288,1288
    reverse(mod_F2_X(
      xor(shift(reverse(b), 32), shift(reverse(acc), 64)),
      bits_of_int(0x1_1EDC_6F41, 33)
    ))
  }

  // This instruction is weird, 64-bit input and output (upper 32 bits are ignored)
  function method {:extern "F2__X__s_Compile", "intrinsic_mm_crc32_u64"} intrinsic_mm_crc32_u64(acc: uint64, b: uint64)
  : (acc': uint64)
  ensures 0 <= acc' < 0x1_0000_0000
  ensures bits_of_int(acc' as int, 32) ==
    mm_crc32_u64(
      bits_of_int(acc as int, 32),
      bits_of_int(b as int, 64)
    )

  // https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=_mm_clmulepi64_si128&expand=1288,1288,1565,3416,1568,682

  function mm_clmulepi64_si128_0(a: Bits, b: Bits) : (c: Bits)
  requires |a| == 128
  requires |b| == 128
  {
    var tmp1 := a[0..64];
    var tmp2 := b[0..64];
    mul_F2_X(tmp1, tmp2)
  }

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_clmulepi64_si128_0"} intrinsic_mm_clmulepi64_si128_0(a: uint128, b: uint128)
  : (c: uint128)
  ensures bits_of_int(c as int, 128)
      == mm_clmulepi64_si128_0(
          bits_of_int(a as int, 128),
          bits_of_int(b as int, 128))

  function mm_clmulepi64_si128_16(a: Bits, b: Bits) : (c: Bits)
  requires |a| == 128
  requires |b| == 128
  {
    var tmp1 := a[0..64];
    var tmp2 := b[64..128];
    mul_F2_X(tmp1, tmp2)
  }

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_clmulepi64_si128_16"} intrinsic_mm_clmulepi64_si128_16(a: uint128, b: uint128)
  : (c: uint128)
  ensures bits_of_int(c as int, 128)
      == mm_clmulepi64_si128_16(
          bits_of_int(a as int, 128),
          bits_of_int(b as int, 128))

  function method {:extern "F2__X__s_Compile", "intrinsic_mm_xor_si128"} intrinsic_mm_xor_si128(a: uint128, b: uint128)
  : (c: uint128)
  ensures bits_of_int(c as int, 128)
      == xor(bits_of_int(a as int, 128), bits_of_int(b as int, 128))

  function method {:extern"F2__X__s_Compile", "bitxor32"} bitxor32(a: uint32, b: uint32) : (c : uint32)
  ensures bits_of_int(c as int, 32)
      == xor(bits_of_int(a as int, 32), bits_of_int(b as int, 32))

  function method {:extern"F2__X__s_Compile", "bitxor64"} bitxor64(a: uint64, b: uint64) : (c : uint64)
  ensures bits_of_int(c as int, 64)
      == xor(bits_of_int(a as int, 64), bits_of_int(b as int, 64))
}
