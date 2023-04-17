// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype A = A(a: int)
linear datatype B = B(b: int)

// crashes
method SeqThenLinear(s: seq<A>, linear inout b: B)
{}

// crashes
method SharedThenLinear(shared b1: B, linear inout b2: B)
{}

