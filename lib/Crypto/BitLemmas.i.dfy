include "../Lang/System/Bits.s.dfy"
include "../Lang/System/F2_X.s.dfy"
include "CRC32C.s.dfy"
include "../Marshalling/Math.i.dfy"
include "../Lang/System/PackedInts.s.dfy"

module BitLemmas {
  import opened Bits_s
  import opened F2_X_s
  import opened CRC32_C`Internal
  import opened NativeTypes
  import opened NativePackedInts
  import opened Math

  lemma bits_X_eq_bits_Y_plus_zeros(n: nat, x: nat, y: nat)
  requires 0 <= n < Math.power2(x)
  requires x <= y
  ensures bits_of_int(n, y) == bits_of_int(n, x) + zeroes(y-x)
  {
    Math.reveal_power2();
    if y == x {
    } else {
      if x == 0 {
      } else {
        bits_X_eq_bits_Y_plus_zeros(n/2, x-1, y-1);
      }
    }
  }

  lemma bits_64_eq_bits_32_plus_zeros(n: uint64)
  requires 0 <= n < 0x1_0000_0000
  ensures bits_of_int(n as int, 64) == bits_of_int(n as int, 32) + zeroes(32)
  {
    Math.lemma_2toX();
    bits_X_eq_bits_Y_plus_zeros(n as int, 32, 64);
  }

  lemma mul_F2_X_digit_partial_ignores_zeroes(a: Bits, b: Bits, a': Bits, b': Bits, i: nat, j: nat)
  requires forall k | 0 <= k :: bits_get(a, k) == bits_get(a', k)
  requires forall k | 0 <= k :: bits_get(b, k) == bits_get(b', k)
  requires j <= i+1
  ensures mul_F2_X_digit_partial(a, b, i, j) == mul_F2_X_digit_partial(a', b', i, j)
  decreases i + 1 - j
  {
  }

  lemma mul_F2_X_digit_ignores_zeroes(a: Bits, b: Bits, a': Bits, b': Bits, i: nat)
  requires forall k | 0 <= k :: bits_get(a, k) == bits_get(a', k)
  requires forall k | 0 <= k :: bits_get(b, k) == bits_get(b', k)
  ensures mul_F2_X_digit(a, b, i) == mul_F2_X_digit(a', b', i)
  {
    mul_F2_X_digit_partial_ignores_zeroes(a, b, a', b', i, 0);
  }

  lemma mul_F2_X_ignore_trailing_zeroes(a: Bits, b: Bits, n: nat, m: nat)
  ensures mul_F2_X(a + zeroes(n), b + zeroes(m))[0..|a|+|b|]
      == mul_F2_X(a, b)
  {
    var x := mul_F2_X(a + zeroes(n), b + zeroes(m))[0..|a|+|b|];
    var y := mul_F2_X(a, b);
    assert |x| == |y|;
    forall i | 0 <= i < |x|
    ensures x[i] == y[i]
    {
      calc {
        x[i];
        mul_F2_X_digit(a + zeroes(n), b + zeroes(m), i);
        {
          mul_F2_X_digit_ignores_zeroes(a, b, a + zeroes(n), b + zeroes(m), i);
        }
        mul_F2_X_digit(a, b, i);
        y[i];
      }
    }
  }

  lemma mod_F2_X_ignore_trailing_zeroes(p: Bits, q: Bits, n: nat)
  requires |q| > 0
  requires |p| >= |q| - 1
  ensures mod_F2_X(p + zeroes(n), q)
      == mod_F2_X(p, q)


  lemma xor_slice(a: Bits, b: Bits, i: int, j: int)
  requires 0 <= i <= j <= |a| == |b|
  ensures xor(a,b)[i..j] == xor(a[i..j], b[i..j])
  {
  }

  function int_of_bits(s: Bits) : int
  {
    if |s| == 0 then
      0
    else
      (if s[0] then 1 else 0) + 2 * int_of_bits(s[1..])
  }

  lemma int_of_bits_split(a: Bits, b: Bits)
  ensures int_of_bits(a+b)
      == int_of_bits(a) + power2(|a|) * int_of_bits(b)
  {
    if |a| == 0 {
      calc {
        int_of_bits(a+b);
        { assert a + b == b; }
        int_of_bits(b);
        { assert power2(0) == 1 by { reveal_power2(); } }
        power2(|a|) * int_of_bits(b);
        int_of_bits(a) + power2(|a|) * int_of_bits(b);
      }
    } else {
      calc {
        int_of_bits(a+b);
        { assert (a+b)[1..] == a[1..] + b; }
        (if a[0] then 1 else 0) + 2 * int_of_bits(a[1..] + b);
        {
          int_of_bits_split(a[1..], b);
        }
        (if a[0] then 1 else 0) + 2 * (int_of_bits(a[1..]) + (power2(|a|-1) * int_of_bits(b)));
        int_of_bits(a) + 2 * (power2(|a|-1) * int_of_bits(b));
        { assert power2(|a|) == 2 * power2(|a|-1) by { reveal_power2(); } }
        int_of_bits(a) + power2(|a|) * int_of_bits(b);
      }
    }
  }

  lemma byte_of_bits_eq_int_of_bits(m: seq<bool>)
  requires |m| == 8
  ensures byte_of_bits(m) as int == int_of_bits(m)
  {
    calc {
      int_of_bits(m);
      (if m[0] then 1 else 0) + 2 * int_of_bits(m[1..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          4 * int_of_bits(m[2..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          8 * int_of_bits(m[3..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          16 * int_of_bits(m[4..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          (if m[4] then 16 else 0) +
          32 * int_of_bits(m[5..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          (if m[4] then 16 else 0) +
          (if m[5] then 32 else 0) +
          64 * int_of_bits(m[6..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          (if m[4] then 16 else 0) +
          (if m[5] then 32 else 0) +
          (if m[6] then 64 else 0) +
          128 * int_of_bits(m[7..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          (if m[4] then 16 else 0) +
          (if m[5] then 32 else 0) +
          (if m[6] then 64 else 0) +
          (if m[7] then 128 else 0) +
          256 * int_of_bits(m[8..]);
      (if m[0] then 1 else 0) +
          (if m[1] then 2 else 0) +
          (if m[2] then 4 else 0) +
          (if m[3] then 8 else 0) +
          (if m[4] then 16 else 0) +
          (if m[5] then 32 else 0) +
          (if m[6] then 64 else 0) +
          (if m[7] then 128 else 0);
      byte_of_bits(m) as int;
    }
  }

  lemma unpack_LittleEndian_Uint32_byte_of_bits(m: seq<bool>)
  requires |m| == 32
  ensures unpack_LittleEndian_Uint32([
        byte_of_bits(m[0..8]),
        byte_of_bits(m[8..16]),
        byte_of_bits(m[16..24]),
        byte_of_bits(m[24..32])
      ]) as int == int_of_bits(m)
  {
    calc {
      unpack_LittleEndian_Uint32([
        byte_of_bits(m[0..8]),
        byte_of_bits(m[8..16]),
        byte_of_bits(m[16..24]),
        byte_of_bits(m[24..32])
      ]) as int;
      {
        reveal_unpack_LittleEndian_Uint32();
      }
      byte_of_bits(m[0..8]) as int
        + byte_of_bits(m[8..16]) as int * 0x1_00
        + byte_of_bits(m[16..24]) as int * 0x1_00_00
        + byte_of_bits(m[24..32]) as int * 0x1_00_00_00;
      {
        byte_of_bits_eq_int_of_bits(m[0..8]);
        byte_of_bits_eq_int_of_bits(m[8..16]);
        byte_of_bits_eq_int_of_bits(m[16..24]);
        byte_of_bits_eq_int_of_bits(m[24..32]);
      }
      int_of_bits(m[0..8])
        + int_of_bits(m[8..16]) * 0x1_00
        + int_of_bits(m[16..24]) * 0x1_00_00
        + int_of_bits(m[24..32]) * 0x1_00_00_00;
      {
        lemma_2toX();
        int_of_bits_split(m[0..8], m[8..16]);
        assert m[0..8] + m[8..16] == m[0..16];
      }
      int_of_bits(m[0..16])
        + int_of_bits(m[16..24]) * 0x1_00_00
        + int_of_bits(m[24..32]) * 0x1_00_00_00;
      {
        lemma_2toX();
        int_of_bits_split(m[0..16], m[16..24]);
        assert m[0..16] + m[16..24] == m[0..24];
      }
      int_of_bits(m[0..24])
        + int_of_bits(m[24..32]) * 0x1_00_00_00;
      {
        lemma_2toX();
        int_of_bits_split(m[0..24], m[24..32]);
        assert m[0..24] + m[24..32] == m;
      }
      int_of_bits(m);
    }
  }

  lemma int_of_bits_bits_of_int(s: int, n: nat)
  requires 0 <= s < power2(n)
  ensures int_of_bits(bits_of_int(s as int, n)) == s
  {
    if n == 0 {
      assert power2(0) == 1 by { reveal_power2(); }
      assert s == 0;
    } else {
      calc {
        int_of_bits(bits_of_int(s, n));
        int_of_bits([s % 2 == 1] + bits_of_int(s / 2, n-1));
        (if s % 2 == 1 then 1 else 0) + 2 * int_of_bits(bits_of_int(s / 2, n-1));
        {
          assert power2(n) == power2(n-1) * 2 by { reveal_power2(); }
          int_of_bits_bits_of_int(s / 2, n-1);
        }
        (if s % 2 == 1 then 1 else 0) + 2 * (s/2);
        {
          var t := s % 2;
          assert 0 <= t < 2;
          if t == 0 { assert (if s % 2 == 1 then 1 else 0) == s % 2; }
          if t == 1 { assert (if s % 2 == 1 then 1 else 0) == s % 2; }
          assert (if s % 2 == 1 then 1 else 0) == s % 2;
        }
        (s % 2) + 2 * (s/2);
        s;
      }
    }
  }

  lemma eq_from_unpack_LittleEndian_Uint32_eq(s: seq<byte>, t: seq<byte>)
  requires |s| == 4
  requires |t| == 4
  requires unpack_LittleEndian_Uint32(s)
      == unpack_LittleEndian_Uint32(t)
  ensures s == t
  {
    reveal_unpack_LittleEndian_Uint32();
    assert s[0] == t[0];
    assert s[1] == t[1];
    assert s[2] == t[2];
    assert s[3] == t[3];
    assert s == t;
  }

  lemma unpacked_bits(t: seq<byte>, s: uint32, m: Bits)
  requires |t| == 4
  requires |m| == 32
  requires m == bits_of_int(s as int, 32)
  requires unpack_LittleEndian_Uint32(t) == s
  ensures [
        byte_of_bits(m[0..8]),
        byte_of_bits(m[8..16]),
        byte_of_bits(m[16..24]),
        byte_of_bits(m[24..32])
      ] == t
  {
    calc {
      unpack_LittleEndian_Uint32([
        byte_of_bits(m[0..8]),
        byte_of_bits(m[8..16]),
        byte_of_bits(m[16..24]),
        byte_of_bits(m[24..32])
      ]) as int;
      {
        unpack_LittleEndian_Uint32_byte_of_bits(m);
      }
      int_of_bits(m);
      int_of_bits(bits_of_int(s as int, 32));
      {
        lemma_2toX();
        int_of_bits_bits_of_int(s as int, 32);
      }
      s as int;
      unpack_LittleEndian_Uint32(t) as int;
    }

    eq_from_unpack_LittleEndian_Uint32_eq([
        byte_of_bits(m[0..8]),
        byte_of_bits(m[8..16]),
        byte_of_bits(m[16..24]),
        byte_of_bits(m[24..32])
      ], t);
  }
}
