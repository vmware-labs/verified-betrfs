module Rationals {
  export Spec provides PositiveNat, add, lt, minus, one
      reveals PositiveRational
  export extends Spec

  type PositiveNat = n: int | n > 0 witness 1

  datatype PositiveRational = PositiveRational(num: PositiveNat, denom: PositiveNat)

  function gcd(a: nat, b: nat) : (res: nat)
  decreases a + b
  ensures a != 0 ==> res != 0 && res <= a
  ensures b != 0 ==> res != 0 && res <= b
  {
    if a == 0 then b
    else if b == 0 then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
  }

  function add(a: PositiveRational, b: PositiveRational) : PositiveRational
  {
    var x := a.num * b.denom + b.num * a.denom;
    var y := a.denom * b.denom;
    var g := gcd(x, y);
    PositiveRational(x / g, y / g)
  }

  predicate lt(a: PositiveRational, b: PositiveRational)
  {
    exists c :: add(a, c) == b
  }

  function minus(a: PositiveRational, b: PositiveRational) : PositiveRational
  requires lt(b, a)

  function one() : PositiveRational
  {
    PositiveRational(1, 1)
  }
}
