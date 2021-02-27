// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

// This file is meant to be run with nonlinear-arithmetic enabled in z3.
// It only exports really basic lemmas (commutativity, associativity, etc.)
// so that these facts can be used by files that use /noNLarith

module NonlinearLemmas {
  lemma mul_assoc(a: int, b: int, c: int)
  ensures (a * b) * c == a * (b * c)
  {
  }

  lemma mul_comm(a: int, b: int)
  ensures a * b == b * a
  {
  }

  lemma mul_gt_0(a: int, b: int)
  requires a > 0
  requires b > 0
  ensures a*b > 0
  {
  }

  lemma div_mul_plus_mod(a: int, b: int)
  requires b > 0
  ensures (a / b) * b + (a % b) == a
  {
  }

  lemma distributive_right(a: int, b: int, c: int)
  ensures (a + b) * c == a*c + b*c
  {
  }

  lemma distributive_left(a: int, b: int, c: int)
  ensures a * (b + c) == a*b + a*c
  {
  }

  lemma distributive_left_sub(a: int, b: int, c: int)
  ensures a * (b - c) == a*b - a*c
  {
  }

  lemma div_eq_0(a: int, b: int)
  requires b > 0
  requires 0 <= a < b
  ensures a / b == 0
  {
  }

  lemma div_ge_0(a: int, b: int)
  requires a >= 0
  requires b > 0
  ensures a / b >= 0
  {
  }

  lemma mod_ge_0(a: int, b: int)
  requires b > 0
  ensures a % b >= 0
  {
  }

  lemma a_mod_b_eq_a(a: int, b: int)
  requires 0 <= a < b
  ensures a % b == a
  {
  }

  lemma mul_le_right(a: int, b: int, c: int)
  requires 0 <= a
  requires b <= c
  ensures a*b <= a*c
  {
  }

}
