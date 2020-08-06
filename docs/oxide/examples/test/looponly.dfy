linear datatype A = A(v: int)
linear datatype B = B(linear a: A)

method inoutExample(linear inout b: B, count: nat)
ensures b.a.v == old_b.a.v + count
{
  var i: nat := count;
  while i > 0
  invariant b.a.v + i == old_b.a.v + count
  {
    inout b.a.v := b.a.v + 1;
    i := i - 1;
  }
}

method {:extern} inoutExample2(linear inout b: B)
returns (count: int)
ensures b.a.v == 0
ensures count == old_b.a.v
{
  count := b.a.v;
  inout b.a.v := 0;
}

method main() {
  linear var b := B(A(32));

  ghost var b0 := b;

  inoutExample(inout b, 5);

  assert b.a.v == b0.a.v + 5;

  var count := inoutExample2(inout b);

  assert count == b0.a.v + 5;

  linear var B(A(_)) := b;
}
