include "MinimalResourceSpec.s.dfy"

abstract module MorphismResourceSpec refines MinimalResourceSpec {
  import Base : MinimalResourceSpec

  type M' = M

  predicate r(a: Base.M, a': M')

  lemma init_unit(a': M')
  requires Init(a')
  ensures r(Base.unit(), a')

  lemma morphism_additive(a: Base.M, b: Base.M, a': M', b': M')
  requires r(a, a')
  requires r(b, b')
  requires Base.add_defined(a, b)
  ensures add_defined(a', b')
  ensures r(Base.add(a, b), add(a', b'))

  lemma morphism_subtractive(a: Base.M, b: Base.M, a': M', b': M')
  requires r(a, a')
  requires Base.add_defined(a, b)
  requires add_defined(a', b')
  requires r(Base.add(a, b), add(a', b'))
  ensures r(b, b')

  least predicate transition_closure(a: Base.M, b: Base.M)
  {
    a == b || (exists c :: transition_closure(a, c) && Base.transition(c, b))
  }

  lemma self_transition(a: Base.M, b: Base.M, a': M')
  requires r(a, a')
  requires r(b, a')
  ensures transition_closure(a, b)

  lemma transition_transition(a: Base.M, a': M', b': M')
  returns (b: Base.M)
  requires r(a, a')
  requires transition(a', b')
  ensures r(b, b')
  ensures transition_closure(a, b)

  /*
   * Actions
   */

  function method {:extern} translate_to(linear a: Base.M, ghost expected_out: M')
      : (linear out: M')
  requires r(a, expected_out)
  ensures out == expected_out

  function method {:extern} translate_from(linear a': M', ghost expected_out: Base.M)
      : (linear out: Base.M)
  requires r(expected_out, a')
  ensures out == expected_out

  function method {:extern} translate_shared(shared s': M', ghost expected_out: Base.M)
      : (linear s: Base.M)
  requires forall a, a' :: r(a, a') && W(a', s') ==> Base.W(a, expected_out)
  ensures s == expected_out
}
