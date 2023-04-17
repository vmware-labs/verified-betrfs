// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

glinear datatype GSimple = GSimple
linear datatype LSimple = LSimple

glinear datatype GSucceed =
  | GSucceed(
      ghost x: int,
      glinear y: int)

linear datatype LSucceed =
  | LSucceed(
      ghost x: int,
      glinear y: GSimple,
      linear t: LSimple)

// ---------- fails ------------------------------------

glinear datatype GFail_Linear =
  | GFail_Linear(linear x: LSimple)

glinear datatype GFail_Normal =
  | GFail_Normal(x: int)
