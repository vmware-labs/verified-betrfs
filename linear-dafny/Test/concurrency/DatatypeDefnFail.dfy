// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype B = B(n: int)

datatype {:glinear_fold} A = A(n: int)
{
  function defn(x: int) : B {
    B(n)
  }
}

datatype {:glinear_fold} Z = Z(n: int)

glinear datatype {:glinear_fold} X = X(ghost n: int)
linear datatype {:glinear_fold} Y = Y(n: int)
