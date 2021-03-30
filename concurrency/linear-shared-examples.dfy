// 'ghost linear' and 'ghost shared' follow essentially the same rules as 'linear' and 'shared'

method m(ghost linear x: int)
returns (ghost linear x': int)
{
  x' := x;
}

method m_shared(ghost shared x: int)
returns (ghost shared x': int, ghost shared y': int)
{
  x' := x;
  y' := x;
}

method m_borrow_fail(ghost linear x: int)
returns (ghost shared x': int, ghost shared y': int)
{
  // you can't pass a 'ghost linear' in here, would violate borrow rules
  x', y' := m_shared(x); // ERROR
}

function method m_funcmethod(ghost linear x: int)
  : (ghost linear x': int)
{
  x
}

datatype T = T(x: int)
linear datatype LT = LT(x: int)

method test(ghost linear x: int, ghost shared y: int)
{
  // These are okay: 'ghost linear' and
  // 'ghost shared' can be converted to normal 'ghost'.
  ghost var a := x;
  ghost var b := y;

  ghost linear c := a; // ERROR
  ghost shared d := a; // ERROR

  // T(5) is "normal" ghost, so this doesn't work
  ghost linear e := T(5); // ERROR
  ghost shared f := T(5); // ERROR

  // LT is a 'linear datatype' so these are ok
  ghost linear g := LT(5);
  ghost shared h := LT(5);

  // this is just proof code, so everything is ok
  assert g == T(5);
}
