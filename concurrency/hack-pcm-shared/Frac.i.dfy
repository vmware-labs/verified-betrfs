include "MorphismResource.s.dfy"

abstract module FracResource refines MorphismResourceSpec {
  type M = 

  function unit() : M

  predicate add_defined(x: M, y: M)

  function add(x: M, y: M) : M
  //requires add_defined(x, y)

  lemma add_unit(x: M)
  ensures add_defined(x, unit())
  ensures add(x, unit()) == x
  { }

  lemma commutative(x: M, y: M)
  //requires add_defined(x, y)
  ensures add_defined(y, x)
  ensures add(x, y) == add(y, x)
  { }

  lemma associative(x: M, y: M, z: M)
  //requires add_defined(y, z)
  //requires add_defined(x, add(y, z))
  ensures add_defined(x, y)
  ensures add_defined(add(x, y), z)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  { }

  predicate Init(s: M)

  predicate transition(a: M, b: M)

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires add_defined(a, c)
  ensures add_defined(b, c)
  ensures transition(add(a, c), add(b, c))
  { }

  predicate W(a: M, b: M)

  lemma W_monotonic(a: M, b: M, s: M)
  //requires W(a, s)
  //requires add_defined(a, b)
  ensures W(add(a, b), s)
  { }

  lemma W_self(a: M)
  ensures W(a, a)
  { }

  lemma W_unit(a: M)
  ensures W(a, unit())
  { }

  predicate r(a: Base.M, a': M')

  lemma init_unit(a': M')
  //requires Init(a')
  ensures r(Base.unit(), a')
  { }

  lemma morphism_additive(a: Base.M, b: Base.M, a': M', b': M')
  //requires r(a, a')
  //requires r(b, b')
  //requires Base.add_defined(a, b)
  ensures add_defined(a', b')
  ensures r(Base.add(a, b), add(a', b'))
  { }

  lemma morphism_subtractive(a: Base.M, b: Base.M, a': M', b': M')
  //requires r(a, a')
  //requires Base.add_defined(a, b)
  //requires add_defined(a', b')
  //requires r(Base.add(a, b), add(a', b'))
  ensures r(b, b')
  {
  }

  lemma self_transition(a: Base.M, b: Base.M, a': M')
  //requires r(a, a')
  //requires r(b, a')
  ensures transition_closure(a, b)
  {
  }

  lemma transition_transition(a: Base.M, a': M', b': M')
  returns (b: Base.M)
  //requires r(a, a')
  //requires transition(a', b')
  ensures r(b, b')
  ensures transition_closure(a, b)
  {
  }
}
