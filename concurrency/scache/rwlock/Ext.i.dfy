include "../../framework/PCMExt.s.dfy"

module SomeBase refines PCM {
}

abstract module SimpleExt {
  import Base = SomeBase

  type F(!new,==)

  function unit() : F
  predicate dot_defined(a: F, b: F)
  function dot(a: F, b: F) : F
    requires dot_defined(a, b)

  lemma dot_unit(x: F)
  ensures dot_defined(x, unit())
  ensures dot(x, unit()) == x

  lemma commutative(x: F, y: F)
  requires dot_defined(x, y)
  ensures dot_defined(y, x)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: F, y: F, z: F)
  requires dot_defined(y, z)
  requires dot_defined(x, dot(y, z))
  ensures dot_defined(x, y)
  ensures dot_defined(dot(x, y), z)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  predicate Inv(state: F)

  function Interp(a: F) : Base.M
    requires Inv(a)

  predicate InternalNext(f: F, f': F)
  predicate CrossNext(f: F, f': F, b: Base.M, b': Base.M)

  lemma interp_unit()
  ensures Inv(unit()) && Interp(unit()) == Base.unit()

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  requires InternalNext(f, f')
  requires dot_defined(f, p)
  requires Inv(dot(f, p))
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Interp(dot(f', p)) == Interp(dot(f, p))

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: Base.M, b': Base.M)
  requires CrossNext(f, f', b, b')
  requires dot_defined(f, p)
  requires Inv(dot(f, p))
  requires Base.dot_defined(Interp(dot(f, p)), b)
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Base.dot_defined(Interp(dot(f', p)), b')
  ensures Base.dot(Interp(dot(f', p)), b')
       == Base.dot(Interp(dot(f, p)), b)

  /*lemma interp_monotonic(a: F, b: F)
  requires Inv(a)
  requires dot_defined(a, b) && Inv(dot(a, b))
  ensures Base.le(Interp(a), Interp(dot(a, b)))*/
}
