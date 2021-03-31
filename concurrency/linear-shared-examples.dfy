// 'ghost linear' and 'ghost shared' follow essentially the same rules as 'linear' and 'shared'

// ghost linear => 'ghost linear'
// ghost shared => 'ghost shared'

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

  ghost linear var c := a; // ERROR
  ghost shared var d := a; // ERROR

  // T(5) is "normal" ghost, so this doesn't work
  ghost linear var e := T(5); // ERROR
  ghost shared var f := T(5); // ERROR

  // LT is a 'linear datatype' so these are ok
  ghost linear var g := LT(5);
  ghost shared var h := LT(5);

  // this is just proof code, so everything is ok
  assert g == T(5);
}

/// ghost methods

// ghost method can take 'ghost linear' as argument
ghost method gm(ghost linear x: LT, ghost shared y: LT)

// If 'ghost method' takes a (normal) linear argument, we could automatically
// interpret it as 'ghost linear'. Or we could have it be an error, it doesn't
// really matter.
ghost method gm2(linear x: LT, shared y: LT)

// This should be an error - passing linear data to a lemma is meaningless.
lemma l(ghost linear x: LT) // ERROR

// twostate lemmas are completely out of scope, they're only useful
// in a heap world anyway.
twolemma lemma l(ghost linear x: LT) // ERROR
