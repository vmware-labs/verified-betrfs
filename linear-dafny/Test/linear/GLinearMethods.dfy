// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

glinear method g_m() {
}

glinear method g_m2() {
  g_m();
}

method m() {
  g_m();
  g_m2();
}

// ---------- fails ------------------------------------

glinear method g_m3() {
  m();
}
