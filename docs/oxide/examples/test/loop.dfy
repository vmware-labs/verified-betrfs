linear datatype A = A(v: int)
linear datatype B = B(linear a: A)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

method linearExample(linear b: B, c: int) returns (linear b': B)
ensures b'.a.v == b.a.v + c
{
  linear var B(A(v)) := b;
  b' := B(A(v + c));
}

method inoutExample(linear inout b: B)
ensures b.a.v == old_b.a.v + 5
{
  var i: int := 5;
  while i > 0
  invariant b.a.v + i == old_b.a.v + 5
  {
    var newV := b.a.v + 1;
    Assign(inout b.a.v, newV);
    i := i - 1;
  }
}

method main() {
  linear var b := B(A(32));

  ghost var b0 := b;

  b := linearExample(b, 8);

  assert b.a.v == b0.a.v + 8;

  inoutExample(inout b);

  assert b.a.v == b0.a.v + 8 + 5;

  linear var B(A(_)) := b;
}
