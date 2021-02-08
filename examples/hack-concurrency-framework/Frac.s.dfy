include "Rational.s.dfy"

module FracLogic {
  import opened Rationals

  linear datatype Frac<V> = Frac(linear v: V, r: PositiveRational)

  function method {:extern} borrow<V>(shared frac: Frac<V>) : (shared v : V)
  ensures v == frac.v

  function method {:extern} unwrap<V>(linear frac: Frac<V>) : (linear v: V)
  requires frac.r == one()
  ensures v == frac.v

  function method {:extern} wrap<V>(linear v: V) : (linear frac : Frac<V>)
  ensures frac == Frac(v, one())

  method {:extern} frac_split<V>(
      linear f: Frac<V>,
      r: PositiveRational)
  returns (linear a: Frac<V>, linear b: Frac<V>)
  requires Rationals.lt(r, f.r)
  ensures a == Frac(f.v, r)
  ensures b == Frac(f.v, Rationals.minus(f.r, r))

  method {:extern} frac_join<V>(
      linear f: Frac<V>,
      linear g: Frac<V>)
  returns (linear a: Frac<V>)
  requires f.v == g.v
  ensures a.v == f.v
  ensures a.r == Rationals.add(f.r, g.r)
}
