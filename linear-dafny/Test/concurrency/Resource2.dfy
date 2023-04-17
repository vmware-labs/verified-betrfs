// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module MinimalResourceSpec {
  type M(==, !new) // TODO user can't construct/destruct the M?

  type S = M // currently require the 'gshared' type to be the same

  type R(==,!new) {
    function get() : M
  }

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

  function method {:extern} is_valid(gshared a: R, glinear b: R) : ()
  ensures add_defined(a.get(), b.get())

  function method {:extern} transition_update(
      gshared s: R,
      glinear b: R,
      ghost expected_out: M)
    : (glinear c: R)
  requires forall a :: W(a, s.get()) && add_defined(a, b.get()) ==> add_defined(a, expected_out) && transition(add(a, b.get()), add(a, expected_out))
  ensures c.get() == expected_out

  function method {:extern} get_unit() : (glinear u: R)
  ensures u.get() == unit()

  function method {:extern} get_unit_shared() : (gshared u: R)
  ensures u.get() == unit()

  // This MUST be 'method', as it wouldn't be safe to call this and
  // obtain the postconditions from only ghost 'a' and 'b'.
  glinear method {:extern} join(glinear a: R, glinear b: R)
  returns (glinear sum: R)
  ensures add_defined(a.get(), b.get()) // yes, this is an 'ensures'
  ensures sum.get() == add(a.get(), b.get())

  // The only reason this is a 'method' and not a 'function method'
  // is so it can easily have two return args.
  glinear method {:extern} split(glinear sum: R, ghost a: M, ghost b: M)
  returns (glinear a': R, glinear b': R)
  requires add_defined(a, b)
  requires sum.get() == add(a, b)
  ensures a'.get() == a && b'.get() == b

  function method {:extern} join_shared(gshared s: R, gshared t: R, ghost expected_q: M)
    : (gshared q: R)
  requires forall a :: W(a, s.get()) && W(a, t.get()) ==> W(a, expected_q)
  ensures expected_q == q.get()

  function method {:extern} sub(gshared s: R, ghost t: M)
   : (glinear t': R)
  requires le(t, s.get())
  ensures t'.get() == t
}
