// 'ghost linear' and 'shared token' follow essentially the same rules as 'linear' and 'shared'

// token => 'ghost linear'
// shared token => 'shared token'

method m(token x: int)
returns (token x': int)
{
  x' := x;
}

method m_shared(shared token x: int)
returns (shared token x': int, shared token y': int)
{
  x' := x;
  y' := x;
}

method m_borrow_fail(token x: int)
returns (shared token x': int, shared token y': int)
{
  // you can't pass a 'token' in here, would violate borrow rules
  x', y' := m_shared(x); // ERROR
}

function method m_funcmethod(token x: int)
  : (token x': int)
{
  x
}

datatype T = T(x: int)
linear datatype LT = LT(x: int)

method test(token x: int, shared token y: int)
{
  // These are okay: 'token' and
  // 'shared token' can be converted to normal 'ghost'.
  ghost var a := x;
  ghost var b := y;

  token var c := a; // ERROR
  shared token var d := a; // ERROR

  // T(5) is "normal" ghost, so this doesn't work
  token var e := T(5); // ERROR
  shared token var f := T(5); // ERROR

  // LT is a 'linear datatype' so these are ok
  token var g := LT(5);
  shared token var h := LT(5);

  // this is just proof code, so everything is ok
  assert g == T(5);
}
