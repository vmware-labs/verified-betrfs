abstract module MinimalResourceSpec {
  type R(==, !new) // TODO user can't construct/destruct the R?

  type S = R // currently require the 'shared' type to be the same

  // Monoid axioms

  function unit() : R
  function add(x: R, y: R) : R

  predicate le(x: R, y: R)
  {
    exists x1 :: add(x, x1) == y
  }

  lemma add_unit(x: R)
  ensures add(x, unit()) == x

  lemma commutative(x: R, y: R)
  ensures add(x, y) == add(y, x)

  lemma associative(x: R, y: R, z: R)
  ensures add(x, add(y, z)) == add(add(x, y), z)

  predicate Valid(s: R)

  predicate Init(s: R)
  ensures Init(s) ==> Valid(s)

  lemma valid_monotonic(x: R, y: R)
  requires Valid(add(x, y))
  ensures Valid(x)

  predicate transition(a: R, b: R)

  lemma transition_preserves_valid(a: R, b: R)
  requires transition(a, b)
  requires Valid(a)
  ensures Valid(b)

  lemma transition_is_monotonic(a: R, b: R, c: R)
  requires transition(a, b)
  requires Valid(add(a, c))
  ensures transition(add(a, c), add(b, c))

  predicate W(a: R, b: R)

  lemma W_monotonic(a: R, b: R, s: R)
  requires W(a, s)
  ensures W(add(a, b), s)

  /*
   * What I'd like to do is say: you can borrow a `linear a` into
   * a `shared b` iff W(a, b).
   * However, right now the way borrowing works is via Dafny's linear type system
   * so `linear a` -> `shared a` is the only way to borrow.
   * That means we need W(a, a) to hold.
   */
  lemma W_self(a: R)
  ensures W(a, a)

  lemma W_unit(a: R)
  ensures W(a, unit())

  lemma valid_unit()
  ensures Valid(unit())

  /*
   * Actions
   */

  function method {:extern} is_valid(shared a: R, linear b: R) : ()
  ensures Valid(add(a, b))

  function method {:extern} transition_update(
      shared s: R,
      linear b: R,
      ghost expected_out: R)
    : (linear c: R)
  requires forall a :: W(a, s) ==> transition(add(a, b), add(a, expected_out))
  ensures c == expected_out

  function method {:extern} get_unit() : (linear u: R)
  ensures u == unit()

  function method {:extern} get_unit_shared() : (shared u: R)
  ensures u == unit()

  function method {:extern} join(linear a: R, linear b: R) : (linear sum: R)
  ensures sum == add(a, b)

  method {:extern} split(linear sum: R, ghost a: R, ghost b: R)
  returns (linear a': R, linear b': R)
  requires sum == add(a, b)
  ensures a' == a && b' == b

  function method {:extern} join_shared(shared s: R, shared t: R, ghost expected_q: R)
    : (shared q: R)
  requires forall a :: W(a, s) && W(a, t) ==> W(a, expected_q)
  ensures expected_q == q

  function method {:extern} sub(shared s: R, ghost t: R)
   : (linear t': R)
  requires le(t, s)
  ensures t' == t
}
