include "PCM.s.dfy"

abstract module PCMWrap refines PCM {
  /*abstract*/ type G(==,!new)

  type {:extern} M(==,!new)

  function {:extern} nil() : M
  function {:extern} one(g: G) : M

  function unit() : M { nil() }

  predicate {:extern} dot_defined(x: M, y: M)
  function {:extern} dot(x: M, y: M) : M
  lemma {:extern} dot_unit(x: M)
  lemma {:extern} commutative(x: M, y: M)
  lemma {:extern} associative(x: M, y: M, z: M)
  lemma {:extern} transition_is_monotonic(a: M, b: M, c: M)

  predicate transition(a: M, b: M) { a == b }

  function singleton_loc(): Loc

  type GToken = t : Token | t.loc() == singleton_loc()
    witness *

  function method {:extern} wrap(glinear g: G) : (glinear t: GToken)
  ensures t.get() == one(g)

  function method {:extern} unwrap(glinear t: GToken) : (glinear g: G)
  requires exists a :: t.get() == one(a)
  ensures t.get() == one(g)
}
