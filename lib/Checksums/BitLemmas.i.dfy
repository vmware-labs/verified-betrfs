include "../Lang/System/Bits.s.dfy"
include "../Lang/System/F2_X.s.dfy"
include "CRC32C.s.dfy"
include "../Marshalling/Math.i.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "Nonlinear.i.dfy"
include "MathLemmas.i.dfy"

module BitLemmas {
  import opened Bits_s
  import opened F2_X_s
  import opened CRC32_C`Internal
  import opened NativeTypes
  import opened NativePackedInts
  import opened Math
  import NonlinearLemmas
  import MathLemmas

  lemma bits_of_int_0(x: nat)
  ensures bits_of_int(0, x) == zeroes(x)
  {
    if x > 0 {
      calc {
        bits_of_int(0, x);
        [0 % 2 == 1] + bits_of_int(0 / 2, x-1);
        [false] + bits_of_int(0, x-1);
        { bits_of_int_0(x-1); }
        zeroes(x);
      }
    } else {
      calc {
        bits_of_int(0, 0);
        [];
        zeroes(0);
      }
    }
  }

  lemma bits_X_eq_bits_Y_plus_zeros(n: nat, x: nat, y: nat)
  requires 0 <= n < Math.power2(x)
  requires x <= y
  ensures bits_of_int(n, y) == bits_of_int(n, x) + zeroes(y-x)
  {
    Math.reveal_power2();
    if y == x {
    } else {
      if x == 0 {
        calc {
          bits_of_int(n, y);
          {
            assert n == 0; bits_of_int_0(y);
          }
          zeroes(y-x);
          bits_of_int(n, x) + zeroes(y-x);
        }
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
  {
    if n == 0 {
      assert p + zeroes(n) == p;
    } else {
      calc {
        mod_F2_X(p + zeroes(n), q);
        {
          assert (p + zeroes(n))[..|p| + n - 1] == p + zeroes(n-1);
        }
        mod_F2_X(p + zeroes(n-1), q);
        {
          mod_F2_X_ignore_trailing_zeroes(p, q, n-1);
        }
        mod_F2_X(p, q);
      }
    }
  }

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
        { NonlinearLemmas.mul_assoc(2, power2(|a|-1), int_of_bits(b)); }
        int_of_bits(a) + (2 * power2(|a|-1)) * int_of_bits(b);
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
  decreases n
  {
    if n == 0 {
      assert power2(0) == 1 by { reveal_power2(); }
      assert s == 0;
    } else {
      calc {
        int_of_bits(bits_of_int(s, n));
        { assert s / 2 >= 0; }
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

  /*lemma bits_of_int_unpack32(s: seq<byte>)
  requires |s| == 8
  ensures bits_of_int(unpack_LittleEndian_Uint32(s) as int, 64)
       == bits_of_bytes(s);*/

  lemma lemma_bits_of_int_split(x: int, a: int, b: int)
  requires a >= 0
  requires b >= 0
  requires 0 <= x < power2(a + b)
  ensures x % power2(a) >= 0
  ensures x / power2(a) >= 0
  ensures bits_of_int(x, a + b)
      == bits_of_int(x % power2(a), a)
       + bits_of_int(x / power2(a), b)
  {
    NonlinearLemmas.div_ge_0(x, power2(a));
    NonlinearLemmas.mod_ge_0(x, power2(a));
    if a == 0 {
      calc {
        bits_of_int(x, a + b);
        bits_of_int(x, b);
        {
          assert power2(0) == 1 by { reveal_power2(); }
          assert x / power2(a) == x;
        }
        bits_of_int(x / power2(a), b);
        [] + bits_of_int(x / power2(a), b);
        {
          calc {
            bits_of_int(x % power2(a), a);
            [];
          }
        }
        bits_of_int(x % power2(a), a) + bits_of_int(x / power2(a), b);
      }
    } else {
      assert x / power2(a) >= 0;
      calc {
        bits_of_int(x, a + b);
        [x % 2 == 1] + bits_of_int(x/2, a + b - 1);
        {
          assert x / 2 < power2(a - 1 + b) by { reveal_power2(); }
          lemma_bits_of_int_split(x/2, a - 1, b);
        }
        [x % 2 == 1] + (bits_of_int((x/2) % power2(a-1), a-1) + bits_of_int((x/2) / power2(a-1), b));
        {
          calc {
            bits_of_int((x/2) / power2(a-1), b);
            {
              calc {
                (x/2) / power2(a-1);
                { lemma_div_denominator(x, 2, power2(a-1)); }
                x / (2 * power2(a-1));
                {
                  assert power2(a) == 2 * power2(a-1) by { reveal_power2(); }
                }
                x / power2(a);
              }
            }
            bits_of_int(x / power2(a), b);
          }
        }
        [x % 2 == 1] + (bits_of_int((x/2) % power2(a-1), a-1) + bits_of_int(x / power2(a), b));
        ([x % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1)) + bits_of_int(x / power2(a), b);
        {
          calc {
            [x % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1);
            {
              calc {
                (x % power2(a)) % 2;
                {
                  assert power2(a) == power2(a-1) * 2 by { reveal_power2(); }
                }
                (x % (power2(a-1) * 2)) % 2;
                {
                  MathLemmas.mod_mod(x, power2(a-1), 2);
                }
                x % 2;
              }
            }
            [(x % power2(a)) % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1);
            {
              calc {
                (x/2) % power2(a-1);
                {
                  MathLemmas.div_mod(x, power2(a-1), 2);
                }
                (x % (power2(a-1) * 2)) / 2;
                {
                  assert (power2(a-1) * 2) == power2(a) by {reveal_power2();}
                }
                (x % power2(a)) / 2;
              }
            }
            [(x % power2(a)) % 2 == 1] + bits_of_int((x % power2(a)) / 2, a-1);
            bits_of_int(x % power2(a), a);
          }
        }
        bits_of_int(x % power2(a), a) + bits_of_int(x / power2(a), b);
      } 
    }
  }

  lemma lemma_bits_of_int_64_split(x: int)
  requires 0 <= x < 0x1_0000_0000_0000_0000
  ensures bits_of_int(x, 64)
      == bits_of_int(x % 0x1_0000_0000, 32)
       + bits_of_int(x / 0x1_0000_0000, 32)
  {
    lemma_2toX();
    lemma_bits_of_int_split(x, 32, 32);
  }

  lemma bits_of_int_0_1()
  ensures bits_of_int(0,1) == [false]
  {
  }

  lemma {:fuel bits_of_int,0} extend_bits_of_int(x: nat, a: nat)
  requires 0 <= x < power2(a)
  ensures bits_of_int(x, a + 1) == bits_of_int(x, a) + [false]
  {
    calc {
      bits_of_int(x, a + 1);
      {
        assert x < power2(a + 1) by { reveal_power2(); }
        lemma_bits_of_int_split(x, a, 1);
      }
      bits_of_int(x % power2(a), a) + bits_of_int(x / power2(a), 1);
      {
        NonlinearLemmas.a_mod_b_eq_a(x, power2(a));
        assert x % power2(a) == x;
      }
      bits_of_int(x, a) + bits_of_int(x / power2(a), 1);
      {
        NonlinearLemmas.div_eq_0(x, power2(a));
        assert x / power2(a) == 0;
      }
      bits_of_int(x, a) + bits_of_int(0, 1);
      {
        bits_of_int_0_1();
      }
      bits_of_int(x, a) + [false];
    }
  }


  lemma bits_of_int_combine(x: nat, a: nat, y: nat, b: nat)
  requires 0 <= x < power2(a)
  requires 0 <= y < power2(b)
  requires power2(a) * y >= 0
  ensures bits_of_int(x, a) + bits_of_int(y, b)
      == bits_of_int(x + power2(a) * y, a + b)
  {
    calc {
      (x + power2(a) * y) / power2(a);
      (power2(a) * y + x) / power2(a);
      { lemma_div_multiples_vanish_fancy(y, x, power2(a)); }
      y;
    }

    calc {
      (x + power2(a) * y) % power2(a);
      { NonlinearLemmas.div_mul_plus_mod(x + power2(a) * y, power2(a)); }
      (x + power2(a) * y) - ( ((x + power2(a) * y) / power2(a)) ) * power2(a);
      (x + power2(a) * y) - y * power2(a);
      { NonlinearLemmas.mul_comm(y, power2(a)); }
      x;
    }

    calc {
      bits_of_int(x, a) + bits_of_int(y, b);
      {
      }
      bits_of_int((x + power2(a) * y) % power2(a), a)
        + bits_of_int(y, b);
      {
      }
      bits_of_int((x + power2(a) * y) % power2(a), a)
        + bits_of_int((x + power2(a) * y) / power2(a), b);
      {
        calc {
          x + power2(a) * y; <
          { NonlinearLemmas.mul_le_right(power2(a), y, power2(b) - 1); }
          power2(a) + power2(a) * (power2(b) - 1);
          { NonlinearLemmas.distributive_left_sub(power2(a), power2(b), 1); }
          power2(a) + power2(a) * power2(b) - power2(a) * 1;
          power2(a) * power2(b);
          { lemma_power2_adds(a, b); }
          power2(a + b);
        }
        lemma_bits_of_int_split(x + power2(a) * y, a, b);
      }
      bits_of_int(x + power2(a) * y, a + b);
    }
  }

  lemma {:fuel bits_of_int,0} bits_of_int_unpack64(s: seq<byte>)
  requires |s| == 8
  ensures bits_of_int(unpack_LittleEndian_Uint64(s) as int, 64)
       == bits_of_bytes(s);
  {
    lemma_2toX();
    assert power2(40) == 0x100_0000_0000 by { reveal_power2(); }
    assert power2(48) == 0x10000_0000_0000 by { reveal_power2(); }
    assert power2(56) == 0x100_0000_0000_0000 by { reveal_power2(); }
    calc {
      bits_of_bytes(s);
      bits_of_bytes(s[0..7]) + bits_of_int(s[7] as int, 8);
      { assert s[0..7][0..6] == s[0..6]; }
      bits_of_bytes(s[0..6]) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..6][0..5] == s[0..5]; }
      bits_of_bytes(s[0..5]) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..5][0..4] == s[0..4]; }
      bits_of_bytes(s[0..4]) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..4][0..3] == s[0..3]; }
      bits_of_bytes(s[0..3]) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..3][0..2] == s[0..2]; }
      bits_of_bytes(s[0..2]) + bits_of_int(s[2] as int, 8) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..2][0..1] == s[0..1]; }
      bits_of_bytes(s[0..1]) + bits_of_int(s[1] as int, 8) + bits_of_int(s[2] as int, 8) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert s[0..1][0..0] == []; }
      bits_of_bytes([]) + bits_of_int(s[0] as int, 8) + bits_of_int(s[1] as int, 8) + bits_of_int(s[2] as int, 8) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      { assert bits_of_bytes([]) == []; }

      bits_of_int(s[0] as int, 8) + bits_of_int(s[1] as int, 8) + bits_of_int(s[2] as int, 8) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int, 8, s[1] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int, 16) + bits_of_int(s[2] as int, 8) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int, 16, s[2] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int, 24) + bits_of_int(s[3] as int, 8) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int, 24, s[3] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int, 32) + bits_of_int(s[4] as int, 8) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int, 32, s[4] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int, 40) + bits_of_int(s[5] as int, 8) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int, 40, s[5] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int + 0x100_00_00_00_00 * s[5] as int, 48) + bits_of_int(s[6] as int, 8) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int + 0x100_00_00_00_00 * s[5] as int, 48, s[6] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int + 0x100_00_00_00_00 * s[5] as int + 0x100_00_00_00_00_00 * s[6] as int, 56) + bits_of_int(s[7] as int, 8);
      {
        bits_of_int_combine(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int + 0x100_00_00_00_00 * s[5] as int + 0x100_00_00_00_00_00 * s[6] as int, 56, s[7] as int, 8);
      }
      bits_of_int(s[0] as int + 0x100 * s[1] as int + 0x100_00 * s[2] as int + 0x100_00_00 * s[3] as int + 0x100_00_00_00 * s[4] as int + 0x100_00_00_00_00 * s[5] as int + 0x100_00_00_00_00_00 * s[6] as int + 0x100_00_00_00_00_00_00 * s[7] as int, 64);
      { reveal_unpack_LittleEndian_Uint64(); }
      bits_of_int(unpack_LittleEndian_Uint64(s) as int, 64);
    }
  }
}
