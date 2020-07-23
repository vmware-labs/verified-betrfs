linear datatype A = A(v: int, ghost v2: int)
linear datatype B = B(linear a: A)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

ghost method {:extern} AssignGhost<V>(inout v: V, newV: V)
ensures v == newV

method test(linear inout b: B)
ensures b.a.v == old_b.a.v + 5
{
  var i: int := 5;
  while i > 0
  invariant b.a.v + i == old_b.a.v + 5
  {
    var newV := b.a.v + 1;
    Assign(inout b.a.v, newV); // inout b.a.v := b.a.v + 1;
    AssignGhost(ghost inout b.a.v2, newV);
    i := i - 1;
  }
}
