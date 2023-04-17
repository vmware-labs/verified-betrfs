// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

// ---------- fails ------------------------------------

datatype DX0 = DX0(linear g:int)
datatype DX1 = DX1(glinear g:int)

method Ga(gshared y: int)

glinear method Gb(gshared y: int)
{
  Ga(y);
}

glinear method Gc(gshared y: int)
  modifies {}
{
}

glinear method Gd(gshared y: int)
  decreases *
{
}

glinear method Ge(shared y: int)
{
}

glinear method Gf(linear y: int)
{
}

glinear method Gg(y: int)
{
}

glinear datatype Wrong1 = Wrong1(glinear a:int, linear b:int)
glinear datatype Wrong2 = Wrong2(glinear a:int, b:int)
