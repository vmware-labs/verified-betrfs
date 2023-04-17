// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

function method F1(glinear x_in:int):glinear int
{
    x_in
}

function method F2(glinear x_in:int):(glinear x:int)
{
    F1(x_in)
}

function method F3(gshared x_in:int, gshared y_in:int):gshared int
{
    x_in
}

function method F4(gshared x_in:int):(gshared x:int)
{
    F3(x_in, x_in)
}

method M1(glinear x_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M2(glinear x_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := M1(x_in);
}

method N1(glinear x_in:int, glinear y_in:int) returns(glinear x:int, glinear y:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
    y := y_in;
}

method N2(glinear x_in:int, glinear y_in:int) returns(glinear x:int, glinear y:int)
    ensures x == x_in
{
    x, y := N1(x_in, y_in);
}

method S0(glinear l_in:int, gshared s_in:int) returns(glinear l:int)
{
  l := l_in;
}

method S1(glinear l_in:int, gshared s_in:int) returns(glinear l:int, gshared s1:int, gshared s2:int)
{
  l := S0(l_in, s_in);
  s1 := s_in;
  s2 := s_in;
}

method S2(glinear x_in:int, glinear y_in:int) returns(glinear x:int, glinear y:int)
{
  x := S0(x_in, y_in);
  y := y_in;
}

method V0(glinear l_in:int, gshared s_in:int) returns(glinear l:int, gshared s:int)
{
  gshared var s0 := s_in;
  glinear var l0 := l_in;
  s := s0;
  l := l0;
}

method V1(glinear l_in:int, gshared s_in:int) returns(glinear l:int, gshared s:int)
{
  gshared var s0 := s_in;
  glinear var l0:int;
  l0 := l_in;
  s := s0;
  l := l0;
}

method V2(glinear l_in:int, gshared s_in:int) returns(glinear l:int, gshared s:int)
{
  gshared var s0 := s_in;
  {
    glinear var l0:int;
    l0 := l_in;
    s := s0;
    l := l0;
  }
}

method V3(glinear l_in:int, gshared s_in:int) returns(glinear l:int, gshared s:int)
{
  gshared var s0 := s_in;
  glinear var l0:int;
  s := s0;
  l := l_in;
}

method Alloc() returns(glinear x:int)
method Free(glinear x:int)
method Loop1()
  decreases *
{
  glinear var y := Alloc();
  while true
    decreases *
  {
    if true {
      break;
    }
    glinear var x := Alloc();
    if true {
      Free(x);
      break;
    }
    Free(x);
  }
  Free(y);
}

// ---------- fails ------------------------------------

function method F1_a(x_in:int):glinear int
{
    x_in
}

function method F1_b(glinear x_in:int):int
{
    x_in
}

function method F1_c(glinear x_in:int, glinear y_in:int):glinear int
{
    x_in
}

function method F1_d(glinear x_in:int, glinear y_in:int):glinear int
{
    x_in + y_in
}

function method F1_e():glinear int
{
    7
}

function method F2_a(glinear x_in:int):(glinear x:int)
{
    F1_c(x_in, x_in)
}

function method F2_b(glinear x_in:int):(glinear x:int)
{
    F1_e()
}

function method F3_a(gshared x_in:int, gshared y_in:int):gshared int
{
    7
}

function method F3_b(gshared x_in:int, gshared y_in:int):int
{
    x_in
}

function method F3_c(x_in:int, gshared y_in:int):gshared int
{
    x_in
}

method M1_a(x_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_b(glinear x_in:int) returns(x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_c(glinear x_in:int, glinear y_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_d(glinear x_in:int) returns(glinear x:int, glinear y:int)
    ensures x == x_in
{
    x := x_in;
    x := F2(x);
}

method M1_e() returns(glinear x:int)
{
}

method M2_a(glinear x_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := M1_c(x_in, x_in);
}

method M2_b(glinear x_in:int) returns(glinear x:int)
    ensures x == x_in
{
    x := M1_e();
}

method S1_a(glinear l_in:int, gshared s_in:int) returns(gshared s1:int, gshared s2:int)
{
  s1 := l_in;
  s2 := s_in;
}

method S1_b(gshared s_in:int) returns(glinear l:int, gshared s1:int, gshared s2:int)
{
  l := s_in;
  s1 := s_in;
  s2 := s_in;
}

method S2_a(glinear x_in:int, glinear y_in:int) returns(glinear x:int, glinear y:int, gshared s1:int, gshared s2:int)
{
  x, s1, s2 := S1(x_in, y_in);
  y := y_in;
}

method V0_a(glinear l_in:int, gshared s_in:int) returns(gshared s:int)
{
  gshared var s0 := s_in;
  {glinear var l0 := l_in;}
  s := s0;
}

method V0_b(glinear l_in:int, gshared s_in:int) returns(gshared s:int)
{
  gshared var s0 := s_in;
  glinear var l0 := l_in;
  s := s0;
}

method V1_a(gshared s_in:int) returns(glinear l:int, gshared s:int)
{
  gshared var s0 := s_in;
  glinear var l0:int;
  s := s0;
  l := l0;
}

method Lambda0(glinear x:int)
{
  var f := (i:int) => x;
}

method Lambda1(gshared x:int)
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
    glinear var x := Alloc();
    if true {
      break;
    }
    Free(x);
  }
}

method Loop3()
  decreases *
{
  glinear var y := Alloc();
  while true
    decreases *
  {
    if true {
      break;
    }
    glinear var x := Alloc();
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
function method{:caller_must_be_pure} NoMod():gshared int

method Mod1()
{
  gshared var _ := NoMod(); // caller_must_be_pure function can't be called from method
}

function method Mod2():gshared int
{
  NoMod() // can't return gshared value
}

method Mod3(gshared s:int)

method Mod4(gshared s:int) returns(gshared q:int)

method Mod5(gshared s:int)
  modifies {}

method Mod6()
{
  gshared var q := Mod4(NoMod()); // can't borrow caller_must_be_pure when calling method that returns gshared
}

method Mod7()
{
  Mod5(NoMod()); // can't borrow caller_must_be_pure when calling method with modifies clause
}

method Mod8()
{
  Mod3(NoMod()); // ok
  gshared var s := NoMod(); // can't directly call caller_must_be_pure from method (only allowed when borrowing in method call)
}
