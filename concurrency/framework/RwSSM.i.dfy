include "PCM.s.dfy"

abstract module RwPCM {
  type StoredType

  type M

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M) 
  function I(x: M) : Option<StoredType> requires Inv(x)

  predicate transition(a: M, b: M) {
    forall p :: Inv(dot(a, p)) ==> Inv(dot(b, p)) && I(dot(a, p)) == I(dot(b, p))
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)

  lemma transition_is_refl(a: M)
  requires transition(a, a)
  { }

  lemma transition_is_trans(a: M, b: M, c: M)
  requires transition(a, b)
  requires transition(b, c)
  ensures transition(a, c)
  { }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  ensures transition(dot(a, c), dot(b, c))
  { }
}
