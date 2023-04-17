// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module MinimalResourceSpec {
  type M(==, !new) // TODO user can't construct/destruct the M?

  type S = M // currently require the 'gshared' type to be the same

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

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  requires add_defined(a, c)
  ensures add_defined(b, c)
  ensures transition(add(a, c), add(b, c))

  predicate W(a: M, b: M)

  lemma W_monotonic(a: M, b: M, s: M)
  requires W(a, s)
  requires add_defined(a, b)
  ensures W(add(a, b), s)

  /*
   * What I'd like to do is say: you can borrow a `glinear a` into
   * a `gshared b` iff W(a, b).
   * However, right now the way borrowing works is via Dafny's glinear type system
   * so `glinear a` -> `gshared a` is the only way to borrow.
   * That means we need W(a, a) to hold.
   */
  lemma W_self(a: M)
  ensures W(a, a)

  lemma W_unit(a: M)
  ensures W(a, unit())

  /*
   * Actions
   */

  function method {:extern} is_valid(gshared a: M, glinear b: M) : ()
  ensures add_defined(a, b)

  function method {:extern} transition_update(
      gshared s: M,
      glinear b: M,
      ghost expected_out: M)
    : (glinear c: M)
  requires forall a :: W(a, s) && add_defined(a, b) ==> add_defined(a, expected_out) && transition(add(a, b), add(a, expected_out))
  ensures c == expected_out

  function method {:extern} get_unit() : (glinear u: M)
  ensures u == unit()

  function method {:extern} get_unit_shared() : (gshared u: M)
  ensures u == unit()

  // This MUST be 'method', as it wouldn't be safe to call this and
  // obtain the postconditions from only ghost 'a' and 'b'.
  glinear method {:extern} join(glinear a: M, glinear b: M)
  returns (glinear sum: M)
  ensures add_defined(a, b) // yes, this is an 'ensures'
  ensures sum == add(a, b)

  // The only reason this is a 'method' and not a 'function method'
  // is so it can easily have two return args.
  glinear method {:extern} split(glinear sum: M, ghost a: M, ghost b: M)
  returns (glinear a': M, glinear b': M)
  requires add_defined(a, b)
  requires sum == add(a, b)
  ensures a' == a && b' == b

  function method {:extern} join_shared(gshared s: M, gshared t: M, ghost expected_q: M)
    : (gshared q: M)
  requires forall a :: W(a, s) && W(a, t) ==> W(a, expected_q)
  ensures expected_q == q

  function method {:extern} sub(gshared s: M, ghost t: M)
   : (glinear t': M)
  requires le(t, s)
  ensures t' == t
}
