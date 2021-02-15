include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/F2_X.s.dfy"
//include "CRC32LutPowers.i.dfy"
include "CRC32LutLemma.i.dfy"
//include "CRC32LutBitUnrolling.i.dfy"
include "CRC32Lemmas.i.dfy"
include "../Lang/LinearSequence.s.dfy"

module CRC32_C_Lut {
  export Spec provides lut, lut_entries, NativeTypes, Bits_s, F2_X_s, CRC32_C_Lut_Lemma
  export extends Spec

  import opened NativeTypes
  import opened F2_X_s
  import opened Bits_s
  import opened CRC32_C_Lut_Lemma
  import opened F2_X_Lemmas
  import opened CRC32_C_Lemmas
  import opened LinearSequence_s
  import Math

  function method {:opaque} shift1(p: uint32) : (p' : uint32)
  //requires bits_of_int(n, 32) == pow_mod_crc(p)
  //ensures bits_of_int(n + 1, 32) == pow_mod_crc(p')
  {
    if p % 2 == 0 then
      p / 2
    else
      bitxor32(p / 2, 0x82F6_3b78)
  }

  lemma reverse_p()
  ensures reverse(poly())
      == [true] + bits_of_int(0x82F6_3b78, 32)
  {
    var a := reverse(poly());
    var b := [true] + bits_of_int(0x82F6_3b78, 32);
    assert a[0] == b[0]; assert a[1] == b[1]; assert a[2] == b[2];
    assert a[3] == b[3]; assert a[4] == b[4]; assert a[5] == b[5];
    assert a[6] == b[6]; assert a[7] == b[7]; assert a[8] == b[8];
    assert a[9] == b[9]; assert a[10] == b[10]; assert a[11] == b[11];
    assert a[12] == b[12]; assert a[13] == b[13]; assert a[14] == b[14];
    assert a[15] == b[15]; assert a[16] == b[16]; assert a[17] == b[17];
    assert a[18] == b[18]; assert a[19] == b[19]; assert a[20] == b[20];
    assert a[21] == b[21]; assert a[22] == b[22]; assert a[23] == b[23];
    assert a[24] == b[24]; assert a[25] == b[25]; assert a[26] == b[26];
    assert a[27] == b[27]; assert a[28] == b[28]; assert a[29] == b[29];
    assert a[30] == b[30]; assert a[31] == b[31]; assert a[32] == b[32];
  }

  lemma shift1_pow(n: nat, p: uint32)
  requires n >= 33
  requires bits_of_int(p as nat, 32) == pow_mod_crc(n)
  ensures bits_of_int(shift1(p) as nat, 32) == pow_mod_crc(n + 1)
  {
    var y := reverse(bits_of_int(p as nat, 32));
    var x := reverse(bits_of_int(shift1(p) as nat, 32));

    if p % 2 == 0 {
      calc {
        mod_F2_X(zeroes(n-32) + [true], bits_of_int(0x1_1EDC_6F41, 33));
        mod(zeroes(n-32) + [true]);
        { mod_mul_exp_add(n-33, 1); }
        mod(mul_F2_X(exp(n-33), exp(1)));
        { mod_mul_mod_left(exp(n-33), exp(1)); }
        mod(mul_F2_X(mod(exp(n-33)), exp(1)));
        {
          assert exp(n-33) == zeroes(n-33) + [true];
          assert exp(1) == [false, true];
        }
        mod(mul_F2_X(mod(zeroes(n-33) + [true]), [false, true]));
        {
          reverse_reverse(mod(zeroes(n-33) + [true]));
        }
        mod(mul_F2_X(y, [false, true]));
        { assert [false, true] == zeroes(1) + [true]; }
        mod(mul_F2_X(y, zeroes(1) + [true]));
        { mul_singleton(y, 1); }
        mod(zeroes(1) + y + [false]);
        { assert zeroes(1) == [false]; }
        mod([false] + y + [false]);
        { mod_ignores_trailing_zeroes([false] + y, 1); }
        mod([false] + y);
        {
          calc {
            reverse([false] + y);
            reverse(y) + [false];
            bits_of_int(p as nat, 32) + [false];
            { 
              assert bits_of_int(p as nat, 32)
                  == [p as nat % 2 == 1] + bits_of_int(p as nat / 2, 31);
            }
            [false] + bits_of_int(p as nat / 2, 31) + [false];
            {
              Math.lemma_2toX32();
              extend_bits_of_int(p as nat / 2, 31);
            }
            [false] + bits_of_int(p as nat / 2, 32);
            { reveal_shift1(); }
            [false] + bits_of_int(shift1(p) as nat, 32);
            [false] + reverse(x);
            reverse(x + [false]);
          }
          calc {
            [false] + y;
            { reverse_reverse([false] + y); }
            reverse(reverse([false] + y));
            reverse(reverse(x + [false]));
            { reverse_reverse(x + [false]); }
            x + [false];
          }
        }
        mod(x + [false]);
        { mod_ignores_trailing_zeroes(x, 1); }
        mod(x);
        { assert |x| == 32; }
        x;
      }
    } else {
      var y1 := [false] + y;
      calc {
        mod_F2_X(zeroes(n-32) + [true], bits_of_int(0x1_1EDC_6F41, 33));
        mod(zeroes(n-32) + [true]);
        { mod_mul_exp_add(n-33, 1); }
        mod(mul_F2_X(exp(n-33), exp(1)));
        { mod_mul_mod_left(exp(n-33), exp(1)); }
        mod(mul_F2_X(mod(exp(n-33)), exp(1)));
        {
          assert exp(n-33) == zeroes(n-33) + [true];
          assert exp(1) == [false, true];
        }
        mod(mul_F2_X(mod(zeroes(n-33) + [true]), [false, true]));
        {
          reverse_reverse(mod(zeroes(n-33) + [true]));
        }
        mod(mul_F2_X(y, [false, true]));
        { assert [false, true] == zeroes(1) + [true]; }
        mod(mul_F2_X(y, zeroes(1) + [true]));
        { mul_singleton(y, 1); }
        mod(zeroes(1) + y + [false]);
        { assert zeroes(1) == [false]; }
        mod([false] + y + [false]);
        { mod_ignores_trailing_zeroes([false] + y, 1); }
        mod([false] + y);
        mod(y1);
        mod_F2_X(xor(y1, shift(poly(), 0))[..32], poly());
        xor(y1, shift(poly(), 0))[..32];
        { assert shift(poly(), 0) == poly(); }
        xor(y1, poly())[..32];
        {
          calc {
            xor(y1, poly());
            xor([false] + y, poly());
            {
              calc {
                reverse(xor([false] + y, poly()));
                xor(reverse([false] + y), reverse(poly()));
                xor(reverse(y) + [false], reverse(poly()));
                {
                  calc {
                    reverse(y) + [false];
                    bits_of_int(p as nat, 32) + [false];
                    [true] + bits_of_int(p as nat / 2, 31) + [false];
                    {
                      Math.lemma_2toX32();
                      extend_bits_of_int(p as nat / 2, 31);
                    }
                    [true] + bits_of_int(p as nat / 2, 32);
                  }
                }
                xor(
                  [true] + bits_of_int(p as nat / 2, 32),
                  reverse(poly())
                );
                { reverse_p(); }
                xor(
                  [true] + bits_of_int(p as nat / 2, 32),
                  [true] + bits_of_int(0x82F6_3b78, 32)
                );
                [false] + xor(bits_of_int(p as nat / 2, 32), bits_of_int(0x82F6_3b78, 32));
                { reveal_shift1(); }
                [false] + bits_of_int(shift1(p) as nat, 32);
                [false] + reverse(x);
                reverse(x + [false]);
              }
              calc {
                xor([false] + y, poly());
                { reverse_reverse(xor([false] + y, poly())); }
                reverse(reverse(xor([false] + y, poly())));
                reverse(reverse(x + [false]));
                { reverse_reverse(x + [false]); }
                x + [false];
              }
            }
            x + [false];
          }
        }
        x;
      }
    }

    //reverse_reverse(bits_of_int(shift1(p) as nat, 32));
  }

  lemma pow0()
  ensures bits_of_int(0x8000_0000, 32) == pow_mod_crc(33)
  {
  }

  function method compute_pow_mod_crc(
      n: uint64, p: uint32,
      n': uint64) : (p': uint32)
  requires n >= 33
  requires bits_of_int(p as int, 32) == pow_mod_crc(n as nat)
  requires n <= n'
  ensures bits_of_int(p' as int, 32) == pow_mod_crc(n' as nat)
  decreases n' - n
  {
    if n == n' then
      p
    else (
      shift1_pow(n as nat, p);
      compute_pow_mod_crc(n+1, shift1(p), n')
    )
  }

  function method compute_all_pow_mod_crc_iter(
      linear results: seq<uint32>,
      i: uint64) : (linear results': seq<uint32>)
  requires |results| == 512
  requires 1 <= i <= 512
  requires forall j:nat | 0 <= j < i as nat ::
      bits_of_int(results[j] as nat, 32) == pow_mod_crc(64*(j+1))
  ensures |results'| == 512
  ensures forall j:nat | 0 <= j < 512 ::
      bits_of_int(results'[j] as nat, 32) == pow_mod_crc(64*(j+1))
  decreases 512 - i
  {
    if i == 512 then (
      results
    ) else (
      var prev := seq_get(results, i-1);
      var n := compute_pow_mod_crc(64 * i, prev, 64 * (i + 1));
      compute_all_pow_mod_crc_iter(seq_set(results, i, n), i+1)
    )
  }

  function method compute_all_pow_mod_crc() : (linear results': seq<uint32>)
  ensures |results'| == 512
  ensures forall j:nat | 0 <= j < 512 ::
      bits_of_int(results'[j] as nat, 32) == pow_mod_crc(64*(j+1))
  {
    linear var results := seq_alloc(512, 0);
    pow0();
    var first := compute_pow_mod_crc(33, 0x8000_0000, 64);
    compute_all_pow_mod_crc_iter(seq_set(results, 0, first), 1)
  }

  function method {:opaque} combine(a: uint32, b: uint32) : (c: uint64)
  ensures bits_of_int(c as nat, 64) == bits_of_int(a as nat, 32) + bits_of_int(b as nat, 32)
  {
    lemma_bits_of_int_64_split((b as int) * 0x1_0000_0000 + a as int);
    (b as uint64) * 0x1_0000_0000 + (a as uint64)
  }

  function method compute_lut_iter(
      linear pmc: seq<uint32>,
      linear lut: seq<uint64>,
      i: uint64) : (linear lut': seq<uint64>)
  requires |pmc| == 512
  requires forall j:nat | 0 <= j < 512 ::
      bits_of_int(pmc[j] as nat, 32) == pow_mod_crc(64*(j+1))
  requires |lut| == 257
  requires 1 <= i <= 257
  requires forall j:nat | 1 <= j < i as nat ::
      bits_of_int(lut[j-1] as int, 64) == pow_mod_crc(2*64*j) + pow_mod_crc(64*j)
  ensures |lut'| == 257
  ensures forall j:nat | 1 <= j <= 256 ::
      bits_of_int(lut'[j-1] as int, 64) == pow_mod_crc(2*64*j) + pow_mod_crc(64*j)
  decreases 257 - i
  {
    if i == 257 then (
      var _ := seq_free(pmc);
      lut
    ) else (
      var v := combine(seq_get(pmc, 2*i-1), seq_get(pmc, i-1));
      linear var l := seq_set(lut, i-1, v);
      compute_lut_iter(pmc, l, i+1)
    )
  }

  function method compute_lut() : seq<uint64>
  {
    linear var pmc := compute_all_pow_mod_crc();
    linear var lut := compute_lut_iter(pmc, seq_alloc(257, 0), 1);
    seq_unleash(lut)
  }

  const lut: seq<uint64> := compute_lut();

  lemma {:fuel bits_of_int,0} {:fuel pow_mod_crc,0} lut_entries(n: nat)
  requires 1 <= n <= 256
  ensures |lut| == 257
  ensures bits_of_int(lut[n-1] as int, 64) == pow_mod_crc(2*64*n) + pow_mod_crc(64*n)
  {
  }
}
