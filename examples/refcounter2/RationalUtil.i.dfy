include "Rational.s.dfy"

module RationalUtil {
  import opened Rationals

  lemma in_between(lower: PositiveRational, upper: PositiveRational)
  returns (mid: PositiveRational)
  requires lt(lower, upper)
  ensures lt(lower, mid)
  ensures lt(mid, upper)

  lemma get_smaller(upper: PositiveRational)
  returns (mid: PositiveRational)
  ensures lt(mid, upper)

  function of_nat(n: nat) : PositiveRational
  requires n > 0
}
