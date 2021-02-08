abstract module ResourceSpec {
  type R(==, !new) // TODO user can't construct/destruct the R?

  // Monoid axioms

  function unit() : R
  function add(x: R, y: R) : R

  predicate le(x: R, y: R)
  {
    exists x1 :: add(x, x1) == y
  }

  function pow(x: R, n: nat) : R
  {
    if n == 0 then unit() else add(pow(x, n-1), x)
  }

  lemma add_unit(x: R)
  ensures add(x, unit()) == x

  lemma commutative(x: R, y: R)
  ensures add(x, y) == add(y, x)

  lemma associative(x: R, y: R, z: R)
  ensures add(x, add(y, z)) == add(add(x, y), z)

  predicate Init(s: R)
  predicate Update(s: R, s': R)

  predicate Valid(s: R)

  lemma valid_monotonic(x: R, y: R)
  requires Valid(add(x, y))
  ensures Valid(x)

  lemma update_monotonic(x: R, y: R, z: R)
  requires Update(x, y)
  ensures Update(add(x, z), add(y, z))

  predicate radical(a': R, a: R)
  {
    && le(a', a)
    && (exists n :: le(a, pow(a', n)))
  }

  method {:extern} resources_obey_inv(shared a: R, linear b: R)
  returns (ghost a': R)
  ensures radical(a', a)
  ensures Valid(add(a', b))

  method {:extern} do_transform(
      shared a: R,
      linear b: R,
      ghost expected_out: R)
  returns (linear c: R)
  requires forall a' :: radical(a, a') && Valid(add(a', b)) ==> Update(add(a', b), add(a', expected_out))
  ensures c == expected_out

  function method {:extern} get_unit() : (linear u: R)
  function method {:extern} get_unit_shared() : (shared u: R)

  function method {:extern} join(linear a: R, linear b: R) : (linear sum: R)
  ensures sum == add(a, b)

  method {:extern} split(linear sum: R, ghost a: R, ghost b: R)
  returns (linear a': R, linear b': R)
  requires sum == add(a, b)
  ensures a' == a && b' == b

  method {:extern} sub(shared s: R, ghost t: R)
  returns (linear t': R)
  requires le(t, s)
  ensures t' == t

  // Refining module (.i) needs to prove these properties
  // in order to reap the benefit from the meta-properties above.

  lemma InitImpliesValid(s: R)
  requires Init(s)
  ensures Valid(s)

  lemma UpdatePreservesValid(s: R, t: R)
  requires Update(s, t)
  requires Valid(s)
  ensures Valid(t)
}
