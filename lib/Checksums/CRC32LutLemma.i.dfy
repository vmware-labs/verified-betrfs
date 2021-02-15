include "../Lang/System/F2_X.s.dfy"
include "F2_X_Lemmas.i.dfy"
include "../Marshalling/Math.i.dfy"
include "CRC32PowDef.i.dfy"

module CRC32_C_Lut_Lemma {
  import opened Bits_s
  import opened F2_X_s
  import opened NativeTypes
  import opened Math
  import opened F2_X_Lemmas
  import opened CRC32PowDef

  function pow_mod_crc(n: nat) : seq<bool>
  requires n >= 33
  {
    reverse(mod_F2_X(zeroes(n-33) + [true], bits_of_int(0x1_1EDC_6F41, 33)))
  }

  lemma mod_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures (x % (a * b)) % b == x % b
  {
    var t := x % (a * b);
    var q := x / (a * b);
    assert x == q * (a * b) + t;

    var s := t % b;
    var r := t / b;
    assert t == r * b + s;

    calc {
      x % b;
      x - (x / b) * b;
      calc {
        x / b;
        {
          assert x == (q * a + r) * b + s by {
            calc {
              x;
              q * (a * b) + (r * b + s);
              q * (a * b) + r * b + s;
              { assert q * (a * b) == (q * a) * b; }
              (q * a) * b + r * b + s;
              { assert (q * a + r) * b == (q * a) * b + r * b; }
              (q * a + r) * b + s;
            }
          }
        }
        ((q * a + r) * b + s) / b;
        (s + (q * a + r) * b) / b;
        (s + b * (q * a + r)) / b;
        {
          lemma_add_mul_div(s, q*a + r, b);
        }
        (q * a + r) + s / b;
      }
      x - ((q * a + r) + s / b) * b;
      x - ((q * a + r) * b + (s / b) * b);
      (q * (a * b) + r * b + s) - ((q * a + r) * b + (s / b) * b);
      {
        assert s > -(b as int);
        assert s < b;
        assert s / b == 0;
      }
      (q * (a * b) + r * b + s) - ((q * a + r) * b);
      s; 
    }
  }

  lemma div_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures (x / b) % a == (x % (a * b)) / b
  {
    var q := x / b;
    var r := x % b;
    assert x == b*q + r;

    var t := q / a;
    var s := q % a;
    assert q == a*t + s;

    var u := x / (a * b);
    var p := x % (a * b);
    assert x == (a * b) * u + p;

    var v := p / b;
    var w := p % b;
    assert p == b * v + w;

    assert x
        == b*q + r
        == b*(a*t + s) + r;
    assert x
        == (a * b) * u + p
        == (a * b) * u + b * v + w;

    calc {
      0;
      x - x;
      (b*(a*t + s) + r) - ((a * b) * u + b * v + w);
      {
        lemma_div_denominator(x, b, a);
        assert u == t;
      }
      (b*(a*t + s) + r) - ((a * b) * t + b * v + w);
      b * (s - v) + (r - w);
    }

    assert b * (s - v) > -(b as int);
    assert b * (s - v) < b;
    bounded_mul_eq_0(s - v, b);

    assert s == v;
  }

  lemma lemma_bits_of_int_split(x: int, a: int, b: int)
  requires a >= 0
  requires b >= 0
  requires 0 <= x < power2(a + b)
  ensures bits_of_int(x, a + b)
      == bits_of_int(x % power2(a), a)
       + bits_of_int(x / power2(a), b)
  {
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
                  mod_mod(x, power2(a-1), 2);
                }
                x % 2;
              }
            }
            [(x % power2(a)) % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1);
            {
              calc {
                (x/2) % power2(a-1);
                {
                  div_mod(x, power2(a-1), 2);
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
        assert x % power2(a) == x;
      }
      bits_of_int(x, a) + bits_of_int(x / power2(a), 1);
      {
        assert x / power2(a) == 0;
      }
      bits_of_int(x, a) + bits_of_int(0, 1);
      {
        bits_of_int_0_1();
      }
      bits_of_int(x, a) + [false];
    }
  }
}
