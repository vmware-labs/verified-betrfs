// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Rational.s.dfy"

module FracLogic {
  import opened Rationals

  linear datatype Frac<V> = Frac(linear v: V, r: PositiveRational)

  function method {:extern} borrow<V>(ghost shared frac: Frac<V>) : (ghost shared v : V)
  ensures v == frac.v

  function method {:extern} unwrap<V>(ghost linear frac: Frac<V>) : (ghost linear v: V)
  requires frac.r == one()
  ensures v == frac.v

  function method {:extern} wrap<V>(ghost linear v: V) : (ghost linear frac : Frac<V>)
  ensures frac == Frac(v, one())

  ghost method {:extern} frac_split<V>(
      ghost linear f: Frac<V>,
      ghost r: PositiveRational)
  returns (linear a: Frac<V>, linear b: Frac<V>)
  requires Rationals.lt(r, f.r)
  ensures a == Frac(f.v, r)
  ensures b == Frac(f.v, Rationals.minus(f.r, r))

  ghost method {:extern} frac_join<V>(
      ghost linear f: Frac<V>,
      ghost linear g: Frac<V>)
  returns (ghost linear a: Frac<V>)
  requires f.v == g.v
  ensures a.v == f.v
  ensures a.r == Rationals.add(f.r, g.r)
}
