include "CRC32C.s.dfy"
include "CRC32Lemmas.i.dfy"
include "CRC32Lut.i.dfy"
include "CRC32LutLemma.i.dfy"
include "CRC32C.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Lang/System/NativeArrays.s.dfy"
include "BitLemmas.i.dfy"

// Implementation of CRC32-C, using the 
// using the _mm_crc32_u64 intrinsic, pipelined and proven
// correct using fancy polynomial math.
//
// See https://github.com/komrad36/CRC for a more detailed explanation.

module CRC32_C_Impl {
  export Spec provides compute_crc32c_padded, NativeTypes, A
  export extends Spec

  import opened NativeTypes
  import opened NativePackedInts
  import opened Bits_s
  import opened F2_X_s
  import opened CRC32_C_Lemmas
  import opened CRC32_C_Lut
  import opened CRC32_C_Lut_Lemma
  import A = CRC32_C
  import opened CRC32_C`Internal
  import opened BitLemmas
  import NativeArrays

  function method {:opaque} alignment(idx: uint32) : (res : uint32)
  {
    var t := idx % 8;
    if t == 0 then 0 else 8 - t
  }

  lemma lemma_n_div_24_optimization(n: nat)
  ensures n < 256*24 ==> (n*2731)/65536 == n/24
  {
  }

  lemma split128(a: Bits, b: Bits, c: Bits)
  requires |a| == 128
  requires |b| == 64
  requires |c| == 64
  requires a == b + c
  ensures a[0..64] == b
  ensures a[64..128] == c
  {
  }

  function iterated_intrinsic(data: seq<byte>, idx: int, prev: uint64, z: nat, n: nat) : uint64
  requires 2 <= n <= 256
  requires 1 <= z <= n
  requires 0 <= idx - 8*n
  requires idx <= |data|
  decreases 256 - z
  {
    if z == n then
      prev
    else
      intrinsic_mm_crc32_u64(
        iterated_intrinsic(data, idx, prev, z+1, n),
        unpack_LittleEndian_Uint64(data[idx - 8*z - 8 .. idx - 8*z])
      )
  }

  lemma advanced_of_iterated_intrinsic(
      data: seq<byte>, prev0: uint64, idx0: int, idx: int, prev: uint64, z: nat, n: nat, next: uint64)
  requires 2 <= n <= 256
  requires 1 <= z <= n
  requires 0 <= idx - 8*n
  requires idx <= |data|
  requires 0 <= idx0 <= |data|
  requires next == iterated_intrinsic(data, idx, prev, z, n)
  requires 0 <= prev0 < 0x1_0000_0000
  requires 0 <= prev < 0x1_0000_0000
  requires 0 <= idx0 <= idx - (8 * n)
  requires advances_bytes(data, idx0, prev0 as uint32, idx - (8 * n), prev as uint32)
  ensures 0 <= next < 0x1_0000_0000
  ensures  advances_bytes(data, idx0, prev0 as uint32, idx - (8 * z), next as uint32)
  decreases 256 - z
  {
    if z == n {
    } else {
      var crc := iterated_intrinsic(data, idx, prev, z+1, n);
      advanced_of_iterated_intrinsic(data, prev0, idx0, idx, prev, z+1, n, crc);
      advances_bytes_u64(data, idx - (8*z) as int - 8, crc as uint32, next as uint32);
      advances_bytes_transitive(data,
        idx0 as int, prev0 as uint32,
        idx - (8*z) as int - 8, crc as uint32,
        idx - (8*z) as int, next as uint32);
    }
  }

  method {:fuel mm_crc32_u64,0}
    compute_crc32_main(data: seq<byte>, idx0: uint32, len0: uint32, prev: uint32)
  returns (res: uint32)
  requires 0 <= idx0
  requires idx0 as int + len0 as int <= |data|
  requires |data| < 0x1_0000_0000
  ensures advances_bytes(data, idx0 as int, prev, idx0 as int + len0 as int, res)
  {
    var len := len0;

    var pA: uint64 := idx0 as uint64;

    var crcA: uint64 := prev as uint64;
    var toAlign := alignment(idx0);

    advances_bytes_refl(data, idx0 as int, crcA as uint32);

    while toAlign != 0 && len != 0
    invariant idx0 as int <= pA as int <= idx0 as int + len0 as int
    invariant pA as int + len as int == idx0 as int + len0 as int
    invariant 0 <= crcA < 0x1_0000_0000
    invariant advances_bytes(data, idx0 as int, prev, pA as int, crcA as uint32)
    {
      var x := intrinsic_mm_crc32_u8(crcA as uint32, data[pA]);

      advances_bytes_u8(data, pA as int, crcA as uint32, x);
      advances_bytes_transitive(data, idx0 as int,
          prev, pA as int, crcA as uint32, pA as int + 1, x);

      crcA := x as uint64;

      len := len - 1;
      toAlign := toAlign - 1;
      pA := pA + 1;
    }

    while len >= 144
    invariant idx0 as int <= pA as int <= idx0 as int + len0 as int
    invariant pA as int + len as int == idx0 as int + len0 as int
    invariant 0 <= crcA < 0x1_0000_0000
    invariant advances_bytes(data, idx0 as int, prev, pA as int, crcA as uint32)
    {
      var n: uint32 := if len < 256*24 then (len * 2731) / 65536 else 256;
      lemma_n_div_24_optimization(n as int);

      pA := pA + (8*n) as uint64;
      var pB: uint64 := pA + (8*n) as uint64;
      var pC: uint64 := pB + (8*n) as uint64;

      var crcB: uint64 := 0;
      var crcC: uint64 := 0;

      ghost var old_crcA := crcA;

      // We really should unroll this loop for maximal efficiency
      // but it stresses Dafny too much.
      var z := n;
      while z >= 2
      invariant 1 <= z <= n
      invariant 0 <= crcA < 0x1_0000_0000
      invariant 0 <= crcB < 0x1_0000_0000
      invariant 0 <= crcC < 0x1_0000_0000
      invariant crcA == iterated_intrinsic(data, pA as int, old_crcA, z as int, n as int)
      invariant crcB == iterated_intrinsic(data, pB as int, 0,        z as int, n as int)
      invariant crcC == iterated_intrinsic(data, pC as int, 0,        z as int, n as int)
      {
        /////// A
        var a := Unpack_LittleEndian_Uint64(data, pA - (8*z) as uint64);
        crcA := intrinsic_mm_crc32_u64(crcA, a);

        /////// B
        var b := Unpack_LittleEndian_Uint64(data, pB - (8*z) as uint64);
        crcB := intrinsic_mm_crc32_u64(crcB, b);

        /////// C
        var c := Unpack_LittleEndian_Uint64(data, pC - (8*z) as uint64);
        crcC := intrinsic_mm_crc32_u64(crcC, c);

        z := z - 1;
      }

      /*var t := n / 8;
      var r := n % 8;
      assert n == 8*t + r;

      if (r > 0) {
        if (r > 1) {
          if (r > 2) {
            if (r > 3) {
              if (r > 4) {
                if (r > 5) {
                  if (r > 6) {
                    var a := Unpack_LittleEndian_Uint64(data, pA - (8*z) as uint64);
                    crcA := intrinsic_mm_crc32_u64(crcA, a);
                    var b := Unpack_LittleEndian_Uint64(data, pB - (8*z) as uint64);
                    crcB := intrinsic_mm_crc32_u64(crcB, b);
                    var c := Unpack_LittleEndian_Uint64(data, pC - (8*z) as uint64);
                    crcC := intrinsic_mm_crc32_u64(crcC, c);
                  }

                  assert crcA == iterated_intrinsic(data, pA as int, old_crcA, 8*t as int + 6, n as int);
                  assert crcB == iterated_intrinsic(data, pB as int, 0,        8*t as int + 6, n as int);
                  assert crcC == iterated_intrinsic(data, pC as int, 0,        8*t as int + 6, n as int);
                }
              }
            }
          }
        }
      }*/

      assert crcA == iterated_intrinsic(data, pA as int, old_crcA, 1, n as int);
      assert crcB == iterated_intrinsic(data, pB as int, 0,        1, n as int);
      assert crcC == iterated_intrinsic(data, pC as int, 0,        1, n as int);

      //assert z == 1;

      advances_bytes_refl(data, pA as int, 0);
      advances_bytes_refl(data, pB as int, 0);
      advanced_of_iterated_intrinsic(data, prev as uint64, idx0 as int, pA as int, old_crcA, 1, n as nat, crcA);
      advanced_of_iterated_intrinsic(data, 0, pA as int, pB as int, 0, 1, n as int, crcB);
      advanced_of_iterated_intrinsic(data, 0, pB as int, pC as int, 0, 1, n as int, crcC);

      var a := Unpack_LittleEndian_Uint64(data, pA - 8);
      var new_crcA := intrinsic_mm_crc32_u64(crcA, a);
      advances_bytes_u64(data, pA as int - 8 as int, crcA as uint32, new_crcA as uint32);
      advances_bytes_transitive(data, idx0 as int,
          prev, pA as int - 8 as int, crcA as uint32, pA as int, new_crcA as uint32);
      crcA := new_crcA;

      var b := Unpack_LittleEndian_Uint64(data, pB - 8);
      var new_crcB := intrinsic_mm_crc32_u64(crcB, b);
      advances_bytes_u64(data, pB as int - 8 as int, crcB as uint32, new_crcB as uint32);
      advances_bytes_transitive(data, pA as int, 0,
          pB as int - 8 as int, crcB as uint32, pB as int, new_crcB as uint32);
      crcB := new_crcB;

      lut_entries(n as nat);

      var x := intrinsic_mm_loadu_si128(lut, n-1);
      var vK := intrinsic_mm_cvtepu32_epi64(x);

      assert bits_of_int(vK as int, 128) ==
          pow_mod_crc(2 * 64 * n as int) + zeroes(32) +
          pow_mod_crc(    64 * n as int) + zeroes(32);

      var d := intrinsic_mm_cvtsi64_si128(crcA);
      var vA := intrinsic_mm_clmulepi64_si128_0(d, vK);
      var e := intrinsic_mm_cvtsi64_si128(crcB);
      var vB := intrinsic_mm_clmulepi64_si128_16(e, vK);
      var g := intrinsic_mm_xor_si128(vA, vB);
      var f := intrinsic_mm_cvtsi128_si64(g);

      calc {
        bits_of_int(f as int, 64);
        {
          assert bits_of_int(d as int, 128) == bits_of_int(crcA as int, 64) + zeroes(64);
          assert bits_of_int(e as int, 128) == bits_of_int(crcB as int, 64) + zeroes(64);

          assert bits_of_int(d as int, 128)[0..64] == bits_of_int(crcA as int, 64);
          assert bits_of_int(e as int, 128)[0..64] == bits_of_int(crcB as int, 64);
          split128(bits_of_int(vK as int, 128), 
              pow_mod_crc(2 * 64 * n as int) + zeroes(32),
              pow_mod_crc(    64 * n as int) + zeroes(32));
          assert bits_of_int(vK as int, 128)[0..64] ==
              pow_mod_crc(2 * 64 * n as int) + zeroes(32);
          assert bits_of_int(vK as int, 128)[64..128] ==
              pow_mod_crc(    64 * n as int) + zeroes(32);

          assert bits_of_int(vA as int, 128) == mul_F2_X(bits_of_int(crcA as int, 64), pow_mod_crc(2 * 64 * n as int) + zeroes(32));
          assert bits_of_int(vB as int, 128) == mul_F2_X(bits_of_int(crcB as int, 64), pow_mod_crc(    64 * n as int) + zeroes(32));
        }
        xor(
            mul_F2_X(bits_of_int(crcA as int, 64), pow_mod_crc(2 * 64 * n as int) + zeroes(32)),
            mul_F2_X(bits_of_int(crcB as int, 64), pow_mod_crc(    64 * n as int) + zeroes(32))
        )[0..64];
        {
          bits_64_eq_bits_32_plus_zeros(crcA);
          bits_64_eq_bits_32_plus_zeros(crcB);
        }
        xor(
            mul_F2_X(bits_of_int(crcA as int, 32) + zeroes(32), pow_mod_crc(2 * 64 * n as int) + zeroes(32)),
            mul_F2_X(bits_of_int(crcB as int, 32) + zeroes(32), pow_mod_crc(    64 * n as int) + zeroes(32))
        )[0..64];
        {
          xor_slice(
            mul_F2_X(bits_of_int(crcA as int, 32) + zeroes(32), pow_mod_crc(2 * 64 * n as int) + zeroes(32)),
            mul_F2_X(bits_of_int(crcB as int, 32) + zeroes(32), pow_mod_crc(    64 * n as int) + zeroes(32)),
            0, 64);
        }
        xor(
            mul_F2_X(bits_of_int(crcA as int, 32) + zeroes(32), pow_mod_crc(2 * 64 * n as int) + zeroes(32))[0..64],
            mul_F2_X(bits_of_int(crcB as int, 32) + zeroes(32), pow_mod_crc(    64 * n as int) + zeroes(32))[0..64]
        );
        {
          mul_F2_X_ignore_trailing_zeroes(
            bits_of_int(crcA as int, 32), pow_mod_crc(2 * 64 * n as int), 32, 32);
          mul_F2_X_ignore_trailing_zeroes(
            bits_of_int(crcB as int, 32), pow_mod_crc(    64 * n as int), 32, 32);
        }
        xor(
            mul_F2_X(bits_of_int(crcA as int, 32), pow_mod_crc(2 * 64 * n as int)),
            mul_F2_X(bits_of_int(crcB as int, 32), pow_mod_crc(    64 * n as int))
        );
      }

      var c := Unpack_LittleEndian_Uint64(data, pC - 8);
      var new_crcA' := intrinsic_mm_crc32_u64(crcC, bitxor64(f, c));

      calc {
        bits_of_int(new_crcA' as int, 32);
        mm_crc32_u64(
          bits_of_int(crcC as int, 32),
          xor(
            bits_of_int(f as int, 64),
            bits_of_int(unpack_LittleEndian_Uint64(data[pC - 8..pC]) as int, 64)
          )
        );
        mm_crc32_u64(
          bits_of_int(crcC as int, 32),
          xor(
            xor(
                mul_F2_X(bits_of_int(crcA as int, 32), pow_mod_crc(2 * 64 * n as int)),
                mul_F2_X(bits_of_int(crcB as int, 32), pow_mod_crc(    64 * n as int))
            ),
            bits_of_int(unpack_LittleEndian_Uint64(data[pC - 8..pC]) as int, 64)
          )
        );
      }

      advances_bytes_combine3(data, idx0 as int, pC as int, n as int,
          prev, crcA as uint32, crcB as uint32, crcC as uint32, new_crcA' as uint32);

      crcA := new_crcA';

      len := len - 24 * n;
      pA := pC;
    }

    while len >= 8
    invariant idx0 as int <= pA as int <= idx0 as int + len0 as int
    invariant pA as int + len as int == idx0 as int + len0 as int
    invariant 0 <= crcA < 0x1_0000_0000
    invariant advances_bytes(data, idx0 as int, prev, pA as int, crcA as uint32)
    {
      var a := Unpack_LittleEndian_Uint64(data, pA);
      var new_crcA := intrinsic_mm_crc32_u64(crcA, a);

      advances_bytes_u64(data, pA as int, crcA as uint32, new_crcA as uint32);
      advances_bytes_transitive(data, idx0 as int,
          prev, pA as int, crcA as uint32, pA as int + 8, new_crcA as uint32);

      crcA := new_crcA;
      len := len - 8;
      pA := pA + 8;
    }

    while len != 0
    invariant idx0 as int <= pA as int <= idx0 as int + len0 as int
    invariant pA as int + len as int == idx0 as int + len0 as int
    invariant 0 <= crcA < 0x1_0000_0000
    invariant advances_bytes(data, idx0 as int, prev, pA as int, crcA as uint32)
    {
      var x := intrinsic_mm_crc32_u8(crcA as uint32, data[pA]);

      advances_bytes_u8(data, pA as int, crcA as uint32, x);
      advances_bytes_transitive(data, idx0 as int,
          prev, pA as int, crcA as uint32, pA as int + 1, x);

      crcA := x as uint64;
      len := len - 1;
      pA := pA + 1;
    }

    return crcA as uint32;
  }

  method compute_crc32c_padded(data: seq<byte>)
  returns (checksum: seq<byte>)
  requires |data| < 0x1_0000_0000
  ensures checksum == A.crc32_c_padded(data)
  {
    var s := compute_crc32_main(data, 0, |data| as uint32, 0xffffffff);
    var t := bitxor32(s, 0xffffffff);

    var ar := NativeArrays.newArrayFill(32, 0);
    Pack_LittleEndian_Uint32_into_Array(t, ar, 0);

    final_comp(data, s, 0, |data|, ar[0..4]);
    assert data[0..|data|] == data;

    calc {
      ar[..];
      ar[0..4] + ar[4..32];
      {
        assert ar[0..4] == crc32_c(data);
        assert ar[4..32] == seq(28, i => 0);
      }
      crc32_c(data) + seq(28, i => 0);
    }

    return ar[..];
  }
}
