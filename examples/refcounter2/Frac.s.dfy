include "Rational.s.dfy"

module FracLogic {
  import opened Rationals

  linear datatype Frac<V> = Frac(linear v: V, r: PositiveRational)

  function method {:extern} borrow<V>(shared frac: Frac<V>) : (shared v : V)
  ensures v == frac.v

  function method {:extern} exc<V>(linear frac: Frac<V>) : (linear v: V)
  requires frac.r == one()
  ensures v == frac.v

  function method {:extern} wrap<V>(linear v: V) : (linear frac : Frac<V>)
  ensures frac == Frac(v, one())

  function method {:extern} frac_split<V>(
      linear f: Frac<V>,
      ghost r: PositiveRational)
    : (linear res: (Frac<V>, Frac<V>))
  requires Rationals.lt(r, f.r)
  ensures res.0 == Frac(f.v, r)
  ensures res.1 == Frac(f.v, Rationals.minus(f.r, r))

}
