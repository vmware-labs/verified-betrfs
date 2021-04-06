include "MinimalResourceSpec.s.dfy"

abstract module MorphismResourceSpec refines MinimalResourceSpec {
  import Base : MinimalResourceSpec

  predicate r(a: Base.R, a': R)
  ensures r(a, a') ==> Base.Valid(a) && Valid(a')

  lemma init_unit(a': R)
  requires Init(a')
  ensures r(Base.unit(), a')

  lemma morphism_additive(a: Base.R, b: Base.R, a': R, b': R)
  requires Base.Valid(a)
  requires Base.Valid(b)
  requires Valid(a')
  requires Valid(b')
  requires r(a, a')
  requires r(b, b')
  requires Base.Valid(Base.add(a, b))
  ensures r(Base.add(a, b), add(a',b'))

  lemma morphism_subtractive(a: Base.R, b: Base.R, a': R, b': R)
  requires Base.Valid(a)
  requires Base.Valid(b)
  requires Valid(a')
  requires Valid(b')
  requires r(a, a')
  requires Base.Valid(Base.add(a, b))
  requires r(Base.add(a, b), add(a',b'))
  ensures r(b, b')

  least predicate transition_closure(a: Base.R, b: Base.R)
  {
    a == b || (exists c :: transition_closure(a, c) && Base.transition(c, b))
  }

  lemma self_transition(a: Base.R, b: Base.R, a': R)
  requires r(a, a')
  requires r(b, a')
  ensures transition_closure(a, b)

  lemma transition_transition(a: Base.R, a': R, b': R)
  returns (b: Base.R)
  requires r(a, a')
  requires transition(a', b')
  ensures r(b, b')
  ensures transition_closure(a, b)

  /*
   * Actions
   */

  function method {:extern} translate_to(linear a: Base.R, ghost expected_out: R)
      : (linear out: R)
  requires r(a, expected_out)
  ensures out == expected_out

  function method {:extern} translate_from(linear a': R, ghost expected_out: Base.R)
      : (linear out: Base.R)
  requires r(expected_out, a')
  ensures out == expected_out

  function method {:extern} translate_shared(shared s': R, ghost expected_out: Base.R)
      : (linear s: Base.R)
  requires forall a, a' :: r(a, a') && W(a', s') ==> Base.W(a, expected_out)
  ensures s == expected_out
}
