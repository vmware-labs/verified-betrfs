// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "Nonlinear.i.dfy"
include "../Marshalling/Math.i.dfy"

// More complicated math lemmas. This file is meant to be run with `/noNLarith`.
// Call into NonlinearLemmas for basic nonlinear facts rather than relying on Z3.
// TODO combine with other math lib?

module MathLemmas {
  import NonlinearLemmas
  import opened Math

  lemma mod_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures a * b > 0
  ensures (x % (a * b)) % b == x % b
  {
    NonlinearLemmas.mul_gt_0(a, b);
    var t := x % (a * b);
    var q := x / (a * b);
    NonlinearLemmas.div_mul_plus_mod(x, a * b);
    assert x == q * (a * b) + t;

    var s := t % b;
    var r := t / b;
    NonlinearLemmas.div_mul_plus_mod(t, b);
    assert t == r * b + s;

    calc {
      x % b;
      { NonlinearLemmas.div_mul_plus_mod(x, b); }
      x - (x / b) * b;
      calc {
        x / b;
        {
          assert x == (q * a + r) * b + s by {
            calc {
              x;
              q * (a * b) + (r * b + s);
              q * (a * b) + r * b + s;
              { NonlinearLemmas.mul_assoc(q, a, b); }
              (q * a) * b + r * b + s;
              { NonlinearLemmas.distributive_right(q*a, r, b); }
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
      { NonlinearLemmas.distributive_right(q * a + r, s / b, b); }
      x - ((q * a + r) * b + (s / b) * b);
      (q * (a * b) + r * b + s) - ((q * a + r) * b + (s / b) * b);
      {
        assert s > -(b as int);
        assert s < b;
        NonlinearLemmas.div_eq_0(s, b);
        assert s / b == 0;
      }
      (q * (a * b) + r * b + s) - ((q * a + r) * b);
      {
        NonlinearLemmas.distributive_right(q * a, r, b);
        NonlinearLemmas.mul_assoc(q, a, b);
      }
      s; 
    }
  }

  lemma div_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures a * b > 0
  ensures (x / b) % a == (x % (a * b)) / b
  {
    NonlinearLemmas.mul_gt_0(a, b);
    var q := x / b;
    var r := x % b;
    NonlinearLemmas.div_mul_plus_mod(x, b);
    NonlinearLemmas.mul_comm(b, q);
    assert x == b*q + r;

    var t := q / a;
    var s := q % a;
    NonlinearLemmas.div_mul_plus_mod(q, a);
    NonlinearLemmas.mul_comm(a, t);
    assert q == a*t + s;

    var u := x / (a * b);
    var p := x % (a * b);
    NonlinearLemmas.div_mul_plus_mod(x, a * b);
    NonlinearLemmas.mul_comm(a * b, u);
    assert x == (a * b) * u + p;

    var v := p / b;
    var w := p % b;
    NonlinearLemmas.div_mul_plus_mod(p, b);
    NonlinearLemmas.mul_comm(b, v);
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
        NonlinearLemmas.mul_comm(a, b);
        assert u == t;
      }
      (b*(a*t + s) + r) - ((a * b) * t + b * v + w);
      { NonlinearLemmas.distributive_left(b, a*t, s); }
      b*(a*t) + b*s + r - (a * b) * t - b * v - w;
      {
        NonlinearLemmas.mul_assoc(b, a, t);
        NonlinearLemmas.mul_comm(a, b);
      }
      b*s - b*v + r - w;
      { NonlinearLemmas.distributive_left_sub(b, s, v); }
      b * (s - v) + (r - w);
    }

    assert b * (s - v) > -(b as int);
    assert b * (s - v) < b;
    bounded_mul_eq_0(s - v, b);

    assert s == v;
  }
}
