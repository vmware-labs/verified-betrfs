// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

function method F1(linear x_in:int):linear int
{
    x_in
}

function method F2(linear x_in:int):(linear x:int)
{
    F1(x_in)
}

function method F3(shared x_in:int, shared y_in:int):shared int
{
    x_in
}

function method F4(shared x_in:int):(shared x:int)
{
    F3(x_in, x_in)
}

method M1(linear x_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M2(linear x_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := M1(x_in);
}

method N1(linear x_in:int, linear y_in:int) returns(linear x:int, linear y:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
    y := y_in;
}

method N2(linear x_in:int, linear y_in:int) returns(linear x:int, linear y:int)
    ensures x == x_in
{
    x, y := N1(x_in, y_in);
}

method S0(linear l_in:int, shared s_in:int) returns(linear l:int)
{
  l := l_in;
}

method S1(linear l_in:int, shared s_in:int) returns(linear l:int, shared s1:int, shared s2:int)
{
  l := S0(l_in, s_in);
  s1 := s_in;
  s2 := s_in;
}

method S2(linear x_in:int, linear y_in:int) returns(linear x:int, linear y:int)
{
  x := S0(x_in, y_in);
  y := y_in;
}

method V0(linear l_in:int, shared s_in:int) returns(linear l:int, shared s:int)
{
  shared var s0 := s_in;
  linear var l0 := l_in;
  s := s0;
  l := l0;
}

method V1(linear l_in:int, shared s_in:int) returns(linear l:int, shared s:int)
{
  shared var s0 := s_in;
  linear var l0:int;
  l0 := l_in;
  s := s0;
  l := l0;
}

method V2(linear l_in:int, shared s_in:int) returns(linear l:int, shared s:int)
{
  shared var s0 := s_in;
  {
    linear var l0:int;
    l0 := l_in;
    s := s0;
    l := l0;
  }
}

method V3(linear l_in:int, shared s_in:int) returns(linear l:int, shared s:int)
{
  shared var s0 := s_in;
  linear var l0:int;
  s := s0;
  l := l_in;
}

method Alloc() returns(linear x:int)
method Free(linear x:int)
method Loop1()
  decreases *
{
  linear var y := Alloc();
  while true
    decreases *
  {
    if true {
      break;
    }
    linear var x := Alloc();
    if true {
      Free(x);
      break;
    }
    Free(x);
  }
  Free(y);
}

// ---------- fails ------------------------------------

function method F1_a(x_in:int):linear int
{
    x_in
}

function method F1_b(linear x_in:int):int
{
    x_in
}

function method F1_c(linear x_in:int, linear y_in:int):linear int
{
    x_in
}

function method F1_d(linear x_in:int, linear y_in:int):linear int
{
    x_in + y_in
}

function method F1_e():linear int
{
    7
}

function method F2_a(linear x_in:int):(linear x:int)
{
    F1_c(x_in, x_in)
}

function method F2_b(linear x_in:int):(linear x:int)
{
    F1_e()
}

function method F3_a(shared x_in:int, shared y_in:int):shared int
{
    7
}

function method F3_b(shared x_in:int, shared y_in:int):int
{
    x_in
}

function method F3_c(x_in:int, shared y_in:int):shared int
{
    x_in
}

method M1_a(x_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_b(linear x_in:int) returns(x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_c(linear x_in:int, linear y_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_d(linear x_in:int) returns(linear x:int, linear y:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_e() returns(linear x:int)
{
}

method M2_a(linear x_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := M1_c(x_in, x_in);
}

method M2_b(linear x_in:int) returns(linear x:int)
    ensures x == x_in
{
    x := M1_e();
}

method S1_a(linear l_in:int, shared s_in:int) returns(shared s1:int, shared s2:int)
{
  s1 := l_in;
  s2 := s_in;
}

method S1_b(shared s_in:int) returns(linear l:int, shared s1:int, shared s2:int)
{
  l := s_in;
  s1 := s_in;
  s2 := s_in;
}

method S2_a(linear x_in:int, linear y_in:int) returns(linear x:int, linear y:int, shared s1:int, shared s2:int)
{
  x, s1, s2 := S1(x_in, y_in);
  y := y_in;
}

method V0_a(linear l_in:int, shared s_in:int) returns(shared s:int)
{
  shared var s0 := s_in;
  {linear var l0 := l_in;}
  s := s0;
}

method V0_b(linear l_in:int, shared s_in:int) returns(shared s:int)
{
  shared var s0 := s_in;
  linear var l0 := l_in;
  s := s0;
}

method V1_a(shared s_in:int) returns(linear l:int, shared s:int)
{
  shared var s0 := s_in;
  linear var l0:int;
  s := s0;
  l := l0;
}

method Lambda0(linear x:int)
{
  var f := (i:int) => x;
}

method Lambda1(shared x:int)
{
  var f := (i:int) => x;
}

method Loop2()
  decreases *
{
  while true
    decreases *
  {
    if true {
      break;
    }
    linear var x := Alloc();
    if true {
      break;
    }
    Free(x);
  }
}

method Loop3()
  decreases *
{
  linear var y := Alloc();
  while true
    decreases *
  {
    if true {
      break;
    }
    linear var x := Alloc();
    if true {
      Free(x);
      Free(y);
      break;
    }
    Free(x);
  }
  Free(y);
}

// We guarantee that the value returned by a caller_must_be_pure is limited
// to a scope where no currently allocated objects can be modified.
// (i.e. the scope is limited to a function method
// or a borrowing in a call to a method with no modifies clause.)
function method{:caller_must_be_pure} NoMod():shared int

method Mod1()
{
  shared var _ := NoMod(); // caller_must_be_pure function can't be called from method
}

function method Mod2():shared int
{
  NoMod() // can't return shared value
}

method Mod3(shared s:int)

method Mod4(shared s:int) returns(shared q:int)

method Mod5(shared s:int)
  modifies {}

method Mod6()
{
  shared var q := Mod4(NoMod()); // can't borrow caller_must_be_pure when calling method that returns shared
}

method Mod7()
{
  Mod5(NoMod()); // can't borrow caller_must_be_pure when calling method with modifies clause
}

method Mod8()
{
  Mod3(NoMod()); // ok
  shared var s := NoMod(); // can't directly call caller_must_be_pure from method (only allowed when borrowing in method call)
}
