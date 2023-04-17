// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- succeeds ------------------------------------

glinear datatype GSimple = GSimple
linear datatype LSimple = LSimple

linear datatype V =
  | V(
      glinear gl: GSimple,
      linear l: LSimple)

method m_destruct(linear v: V)
returns (glinear gl': GSimple, linear l': LSimple)
{
  linear var V(gl, l) := v;

  gl' := gl;
  l' := l;
}

method m_match(linear v: V)
returns (glinear gl': GSimple, linear l': LSimple)
{
  linear match v {
    case V(gl, l) => {
      gl' := gl;
      l' := l;
    }
  }
}
