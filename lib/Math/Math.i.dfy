// Based on IronFleet's math library.
// I pulled out only the functions we need for the marshalling code,
// and in a few cases rewrote the proof from scratch to avoid pulling in
// a lot of dependencies.

// This file should verify with /noNLarith

include "Nonlinear.i.dfy"

module Math {
  import opened NonlinearLemmas

  function {:opaque} power2(exp: nat) : nat
      ensures power2(exp) > 0;
  {
      if (exp==0) then
          1
      else
          2*power2(exp-1)
  }

  lemma lemma_2toX()
      ensures power2(8) ==  256;
      ensures power2(16) == 65536;
      ensures power2(19) == 524288;
      ensures power2(24) == 16777216;
      ensures power2(32) == 4294967296;
      ensures power2(60) == 1152921504606846976;
      ensures power2(64) == 18446744073709551616;
  {
    reveal_power2();
  }

  lemma lemma_power2_adds(e1:nat, e2:nat)
      decreases e2;
      ensures power2(e1 + e2) == power2(e1) * power2(e2);
  {
    reveal_power2();
    if (e2 == 0) {
      assert power2(e2) == 1;
    } else {
      lemma_power2_adds(e1, e2-1);
      NonlinearLemmas.mul_assoc(power2(e1), 2, power2(e2 - 1));
      NonlinearLemmas.mul_comm(power2(e1), 2);
      NonlinearLemmas.mul_assoc(2, power2(e1), power2(e2 - 1));
    }
  }

  lemma lemma_2toX32()
      ensures power2(0) == 0x1;
      ensures power2(1) == 0x2;
      ensures power2(2) == 0x4;
      ensures power2(3) == 0x8;
      ensures power2(4) == 0x10;
      ensures power2(5) == 0x20;
      ensures power2(6) == 0x40;
      ensures power2(7) == 0x80;
      ensures power2(8) == 0x100;
      ensures power2(9) == 0x200;
      ensures power2(10) == 0x400;
      ensures power2(11) == 0x800;
      ensures power2(12) == 0x1000;
      ensures power2(13) == 0x2000;
      ensures power2(14) == 0x4000;
      ensures power2(15) == 0x8000;
      ensures power2(16) == 0x10000;
      ensures power2(17) == 0x20000;
      ensures power2(18) == 0x40000;
      ensures power2(19) == 0x80000;
      ensures power2(20) == 0x100000;
      ensures power2(21) == 0x200000;
      ensures power2(22) == 0x400000;
      ensures power2(23) == 0x800000;
      ensures power2(24) == 0x1000000;
      ensures power2(25) == 0x2000000;
      ensures power2(26) == 0x4000000;
      ensures power2(27) == 0x8000000;
      ensures power2(28) == 0x10000000;
      ensures power2(29) == 0x20000000;
      ensures power2(30) == 0x40000000;
      ensures power2(31) == 0x80000000;
      ensures power2(32) == 0x100000000;
  {
    reveal_power2();
  }

  lemma bounded_mul_eq_0(x: int, m: int)
  requires -m < m*x < m
  ensures x == 0
  {
    if (x >= 1) { mul_le_right(m, 1, x); }
    if (x <= -1) { mul_le_right(m, x, -1); }
  }

  // This is often used as part of the axiomatic definition of division
  // in a lot of formalizations of mathematics. Oddly, it isn't built-in to dafny
  // and we have to prove it in sort of a roundabout way.
  lemma lemma_div_ind(x: int, d: int)
  requires d > 0
  ensures x / d + 1 == (x + d) / d
  {
    mul_comm(d, (x / d + 1));
    distributive_right(x/d, 1, d);
    div_mul_plus_mod(x, d);
    //assert d * (x / d + 1)
    //    == (x/d)*d + d
    //    == x - (x % d) + d;

    div_mul_plus_mod(x + d, d);
    //assert d * ((x + d) / d)
    //    == (x + d) - ((x + d) % d);

    //assert 0 <= x % d < d;
    //assert 0 <= (x + d) % d < d;

    //assert d * (x / d + 1) - d * ((x + d) / d)
    //    == ((x + d) % d) - (x % d);

    //assert -d < d * (x / d + 1) - d * ((x + d) / d) < d;
    distributive_left_sub(d, x/d + 1, (x+d)/d);
    //assert -d < d * ((x / d + 1) - ((x + d) / d)) < d;
    bounded_mul_eq_0((x / d + 1) - ((x + d) / d), d);
  }

  lemma lemma_add_mul_div(a: int, b: int, d: int)
  requires d > 0
  ensures (a + b*d) / d == a/d + b
  decreases if b > 0 then b else -b
  {
    if (b == 0) {
    } else if (b > 0) {
      lemma_add_mul_div(a, b-1, d);
      lemma_div_ind(a + (b-1)*d, d);
      distributive_right_sub(b, 1, d);
    } else {
      lemma_add_mul_div(a, b+1, d);
      lemma_div_ind(a + b*d, d);
      distributive_right(b, 1, d);
    }
  }

  lemma lemma_div_multiples_vanish_fancy(x:int, b:int, d:int)
      requires 0<d;
      requires 0<=b<d;
      ensures (d*x + b)/d == x;
      decreases if x > 0 then x else -x
  {
    if (x == 0) {
      div_eq_0(b, d);
    } else if (x > 0) {
      lemma_div_multiples_vanish_fancy(x-1, b, d);
      lemma_div_ind(d*(x-1) + b, d);
      distributive_left_sub(d, x, 1);
    } else {
      lemma_div_multiples_vanish_fancy(x+1, b, d);
      lemma_div_ind(d*x + b, d);
      distributive_left(d, x, 1);
    }
  }

  lemma lemma_div_by_multiple(b:int, d:int)
      requires 0 < d;
      ensures  (b*d) / d == b;
  {   
      lemma_div_multiples_vanish_fancy(b, 0, d);
  }

  lemma lemma_mul_invert(a: nat, b: nat, c: nat)
  requires 0 < b
  requires a == b * c
  ensures a / b == c
  {
    mul_comm(b, c);
    lemma_div_by_multiple(c, b);
  }

  lemma lemma_mod_multiples_basic(x:int, m:int)
      requires m > 0;
      ensures  (x * m) % m == 0;
  {
    div_mul_plus_mod(x*m, m);
    //assert (x*m)%m == x*m - ((x*m)/m)*m;
    lemma_div_by_multiple(x, m);
    //assert (x*m)/m == x;
    //assert x*m - ((x*m)/m)*m == x*m - x*m
    //    == 0;
  }

  lemma lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
      requires x < y;
      requires y == m * z;
      requires z > 0;
      ensures x / z < y / z;
      decreases y - x
  {
    if (x / z >= y / z) {
      mul_le_right(z, y/z, x/z);
      mul_comm(x/z, z);
      mul_comm(y/z, z);
      assert (x/z) * z >= (y/z) * z;
      div_mul_plus_mod(x, z);
      div_mul_plus_mod(y, z);
      assert x - (x%z) >= y - (y%z);
      lemma_mod_multiples_basic(m, z);
      assert x - (x%z) >= y;
      mod_ge_0(x, z);
      assert x >= y;
      assert false;
    }
  }

  lemma lemma_power2_div_is_sub(x:int, y:int)
      requires 0 <= x <= y;
      ensures power2(y - x) == power2(y) / power2(x)
        >= 0;
  {
    calc {
        power2(y) / power2(x);
        { lemma_power2_adds(y-x, x); }
        (power2(y-x)*power2(x)) / power2(x);
        { lemma_div_by_multiple(power2(y-x), power2(x)); }
        power2(y-x);
    }
  }

  lemma lemma_div_denominator(x:int,c:nat,d:nat)
      requires 0 <= x;
      requires 0<c;
      requires 0<d;
      ensures c * d != 0;
      ensures (x/c)/d == x / (c*d);
  {
    mul_gt_0(c, d);
    if (x < c*d) {
      div_eq_0(x, c*d);
      //assert x/(c*d) == 0;
      lemma_div_by_multiple_is_strongly_ordered(x, c*d, d, c);
      lemma_div_by_multiple(d, c);
      //assert (c*d) / c == d;
      //assert x/c < d;
      div_ge_0(x, c);
      div_eq_0(x/c, d);
      //assert (x/c)/d == 0;
    } else {
      //calc {
      //  (x / c) / d;
      //  ((x - c*d + c*d) / c) / d;
      //  {
          lemma_add_mul_div(x-c*d, d, c);
          mul_comm(c, d);
      //  }
      //  ((x - c*d) / c + d) / d;
      //  {
          lemma_div_ind((x - c*d) / c, d);
      //  }
      //  ((x - c*d) / c) / d + 1;
      //  {
          lemma_div_denominator(x - c*d, c, d);
      //  }
      //  ((x - c*d) / (c*d)) + 1;
      //  {
          lemma_div_ind(x - c*d, c*d);
      //  }
      //  x / (c*d);
      //}
    }
  }
}
