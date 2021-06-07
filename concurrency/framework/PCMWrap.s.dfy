include "PCM.s.dfy"

abstract module PCMWrap refines PCM {
  /*abstract*/ type G(!new)

  datatype M = M(ghost m: multiset<G>)

  function nil() : M { M(multiset{}) }
  function one(g: G) : M { M(multiset{g}) }

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

  predicate is_one(m: M) {
    exists a :: m == one(a)
  }

  function get_one(m: M) : G
  requires is_one(m)
  {
    var a :| m == one(a); a
  }

  function method {:extern} unwrap(glinear t: GToken) : (glinear g: G)
  requires is_one(t.get())
  ensures g == get_one(t.get())

  function method {:extern} unwrap_borrow(gshared t: GToken) : (gshared g: G)
  requires is_one(t.get())
  ensures g == get_one(t.get())

}
