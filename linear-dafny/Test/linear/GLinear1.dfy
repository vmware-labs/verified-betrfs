// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

glinear datatype DX0 = DX0()

// ---------- fails ------------------------------------

gshared datatype DX1 = DX1()
shared datatype DX2 = DX2()
ghost datatype DX3 = DX3()
glinear datatype DX4 = DX4(glinear a:int, gshared b:int)
