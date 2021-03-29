abstract module MinimalResourceSpec {
  type M(==, !new) // TODO user can't construct/destruct the M?

  type S = M // currently require the 'shared' type to be the same

  // Monoid axioms

  function unit() : M

  predicate add_defined(x: M, y: M)

  function add(x: M, y: M) : M
  requires add_defined(x, y)

  predicate le(x: M, y: M)
  {
    exists x1 :: add_defined(x, x1) && add(x, x1) == y
  }

  lemma add_unit(x: M)
  ensures add_defined(x, unit())
  ensures add(x, unit()) == x

  lemma commutative(x: M, y: M)
  requires add_defined(x, y)
  ensures add_defined(y, x)
  ensures add(x, y) == add(y, x)

  lemma associative(x: M, y: M, z: M)
  requires add_defined(y, z)
  requires add_defined(x, add(y, z))
  ensures add_defined(x, y)
  ensures add_defined(add(x, y), z)
  ensures add(x, add(y, z)) == add(add(x, y), z)

  predicate Init(s: M)

  predicate transition(a: M, b: M)

  lemma transition_preserves_valid(a: M, b: M)
  requires transition(a, b)
  requires Valid(a)
  ensures Valid(b)

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  requires Valid(add(a, c))
  ensures transition(add(a, c), add(b, c))

  predicate W(a: M, b: M)

  lemma W_monotonic(a: M, b: M, s: M)
  requires W(a, s)
  ensures W(add(a, b), s)

  /*
   * What I'd like to do is say: you can borrow a `linear a` into
   * a `shared b` iff W(a, b).
   * However, right now the way borrowing works is via Dafny's linear type system
   * so `linear a` -> `shared a` is the only way to borrow.
   * That means we need W(a, a) to hold.
   */
  lemma W_self(a: M)
  ensures W(a, a)

  lemma W_unit(a: M)
  ensures W(a, unit())

  lemma valid_unit()
  ensures Valid(unit())

  /*
   * Actions
   */

  function method {:extern} is_valid(shared a: M, linear b: M) : ()
  ensures Valid(add(a, b))

  function method {:extern} transition_update(
      shared s: M,
      linear b: M,
      ghost expected_out: M)
    : (linear c: M)
  requires forall a :: W(a, s) ==> transition(add(a, b), add(a, expected_out))
  ensures c == expected_out

  function method {:extern} get_unit() : (linear u: M)
  ensures u == unit()

  function method {:extern} get_unit_shared() : (shared u: M)
  ensures u == unit()

  function method {:extern} join(linear a: M, linear b: M) : (linear sum: M)
  ensures sum == add(a, b)

  method {:extern} split(linear sum: M, ghost a: M, ghost b: M)
  returns (linear a': M, linear b': M)
  requires sum == add(a, b)
  ensures a' == a && b' == b

  function method {:extern} join_shared(shared s: M, shared t: M, ghost expected_q: M)
    : (shared q: M)
  requires forall a :: W(a, s) && W(a, t) ==> W(a, expected_q)
  ensures expected_q == q

  function method {:extern} sub(shared s: M, ghost t: M)
   : (linear t': M)
  requires le(t, s)
  ensures t' == t
}
