// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

glinear datatype F = F

glinear method maybe_swap(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear x': F, glinear y': F)
{
  if b {
    x' := y;
    y' := x;
  } else {
    x' := x;
    y' := y;
  }
}

glinear method gm(glinear x: F)
returns (glinear y: F)

function method gfm(glinear x: F) : (glinear y: F)

glinear method maybe_swap_1(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear x': F, glinear y': F)
{
  if b {
    x' := gm(y);
    y' := gm(x);
  } else {
    x' := gm(x);
    y' := gm(y);
  }
}

glinear method maybe_swap_2(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear x': F, glinear y': F)
{
  if b {
    x' := y;
    y' := x;
  } else {
    glinear var t := y;
    x' := t;
    y' := x;
  }
}

glinear method maybe_swap_3(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear x': F, glinear y': F)
{
  if b {
    x' := gfm(y);
    y' := gfm(x);
  } else {
    x' := gfm(x);
    y' := gfm(y);
  }
}

glinear datatype Pair = Pair(
  glinear fst: F,
  glinear snd: F)

method make_pair(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear p: Pair)
{
  if b {
    p := Pair(x, y);
  } else {
    p := Pair(y, x);
  }
}

method destruct_pair(glinear p: Pair, ghost b: bool)
returns (glinear x: F, glinear y: F)
{
  if b {
    glinear var Pair(x1, y1) := p;
    x := x1;
    y := y1;
  } else {
    glinear var Pair(x1, y1) := p;
    y := x1;
    x := y1;
  }
}

method swap_while_loop(glinear x: F, glinear y: F, ghost b: bool)
returns (glinear x': F, glinear y': F)
{
  glinear var x1, y1;
  x1 := x;
  y1 := y;

  ghost var cond := b;

  while cond
  decreases (if cond then 1 else 0)
  {
    glinear var tmp;
    tmp := x1;
    x1 := y1;
    y1 := tmp;

    cond := false;
  }

  x' := x1;
  y' := y1;
}

glinear method inout_m(glinear inout x: F)
method normal_inout_m(inout x: F)

method call_inout_m(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  x' := x;
  inout_m(inout x');
}

method ghost_call_inout_m(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  x' := x;
  if b {
    inout_m(inout x');
  }
}

// ---------- fails ------------------------------------

method bad_call_inout_m(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  x' := x;
  normal_inout_m(inout x'); // ERROR // NOTE: has confusing error message: 'expected ordinary expression, found glinear expression'
}

method bad_call_inout_m2(linear x: F, ghost b: bool)
returns (linear x': F)
{
  x' := x;
  inout_m(inout x'); // ERROR
}

method ghost_bad_call_inout_m(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  if b {
    x' := x;
    normal_inout_m(inout x'); // ERROR
  }
}

method ghost_bad_call_inout_m2(linear x: F, ghost b: bool)
returns (linear x': F)
{
  if b {
    x' := x;
    inout_m(inout x'); // ERROR
  }
}

method bad_call_glinear_inout_unassigned(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  inout_m(inout x'); // ERROR
  x' := x;
}


method ghost_bad_call_glinear_inout_unassigned(glinear x: F, ghost b: bool)
returns (glinear x': F)
{
  if b {
    inout_m(inout x'); // ERROR
  } else {
    inout_m(inout x'); // ERROR
  }
  x' := x;
}

datatype FInt = FInt(num: int)

method bad_glinear_inout_update(glinear inout x: FInt)
{
  inout x.num := 5; // probably should be error?
}

method bad_glinear_field_update(glinear x: FInt)
returns (glinear x': FInt)
{
  x' := x.(num := 5); // ERROR
}

method bad_glinear_field_access(glinear x: FInt)
returns (glinear y: int)
{
  y := x.num; // ERROR
}
