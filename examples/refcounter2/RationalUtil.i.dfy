module RationalUtil {
  lemma in_between(lower: PositiveRational, upper: PositiveRational)
  returns (mid: PositiveRational)
  requires lt(lower, upper)
  ensures lt(lower, mid)
  ensures lt(mid, upper)
}
