// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype B = B(n: int)

datatype {:glinear_fold} A = A(n: int)
{
  function defn() : B {
    B(n)
  }
}

/*
function method {:extern} A_fold(a: A, glinear b: B) : (glinear a': A)
requires a.defn() == b
ensures a' == a

function method {:extern} A_unfold(glinear a: A) : (glinear b: B)
ensures b == a.defn()

function method {:extern} A_unfold_borrow(gshared a: A) : (gshared b: B)
ensures b == a.defn()
*/

glinear method x_1(glinear a: A)
returns (glinear b: B)
requires a == A(5)
ensures b == B(5)
{
  b := A_unfold(a);
}

gshared method x_1_borrow(gshared a: A)
returns (gshared b: B)
requires a == A(5)
ensures b == B(5)
{
  b := A_unfold_borrow(a);
}

glinear method y_1(glinear b: B)
returns (glinear a: A)
requires b == B(5)
ensures a == A(5)
{
  ghost var x := A(5);
  a := A_fold(x, b);
}
