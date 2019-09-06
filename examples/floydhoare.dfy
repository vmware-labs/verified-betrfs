predicate Divides(v: int, d: int)
{
  exists k: nat :: k * d == v
}

method GCD(a: int, b: nat) returns (result: int)
requires a >= 0 && b >= 0
ensures Divides(a, result) && Divides(b, result)
ensures forall d: nat | Divides(a, d) && Divides(b, d) :: d <= result
decreases b
{
  if b == 0 {
    result := a;
  } else {
    result := GCD(b, a % b);
  }
  assume false;
}

method Main()
{
  var x := 42;
  var y := 182;

  var z := GCD(x, y);

  assert x % z == 1;
}
