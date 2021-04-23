module GhostLoc {
  datatype Loc =
    | BaseLoc(ghost t: nat)
    | ExtLoc(ghost s: nat, ghost l: Loc)
}

abstract module PCM {
  import opened GhostLoc

  type M(==, !new)

  type Ref {
    function {:extern} loc() : Loc
    function {:extern} get() : M
  }

  // Partial Commutative Monoid (PCM) axioms

  function unit() : M

  predicate dot_defined(x: M, y: M)

  function dot(x: M, y: M) : M
  requires dot_defined(x, y)

  predicate le(x: M, y: M)
  {
    exists x1 :: dot_defined(x, x1) && dot(x, x1) == y
  }

  lemma dot_unit(x: M)
  ensures dot_defined(x, unit())
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  requires dot_defined(x, y)
  ensures dot_defined(y, x)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  requires dot_defined(y, z)
  requires dot_defined(x, dot(y, z))
  ensures dot_defined(x, y)
  ensures dot_defined(dot(x, y), z)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  predicate transition(a: M, b: M)

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  requires dot_defined(a, c)
  ensures dot_defined(b, c)
  ensures transition(dot(a, c), dot(b, c))

  /*
   * Actions
   */

  function method {:extern} transition_update(
      gshared s: Ref,
      glinear b: Ref,
      ghost expected_out: M)
    : (glinear c: Ref)
  requires s.loc() == b.loc()
  requires dot_defined(s.get(), b.get()) ==>
    dot_defined(s.get(), expected_out)
      && transition(
        dot(s.get(), b.get()),
        dot(s.get(), expected_out))
  ensures c.get() == expected_out
  ensures c.loc() == s.loc()

  function method {:extern} get_unit(loc: Loc) : (glinear u: Ref)
  ensures u.get() == unit() && u.loc() == loc

  function method {:extern} get_unit_shared(loc: Loc) : (gshared u: Ref)
  ensures u.get() == unit() && u.loc() == loc

  // This MUST be 'method', as it wouldn't be safe to call this and
  // obtain the postconditions from only ghost 'a' and 'b'.
  glinear method {:extern} join(glinear a: Ref, glinear b: Ref)
  returns (glinear sum: Ref)
  requires a.loc() == b.loc()
  ensures dot_defined(a.get(), b.get()) // yes, this is an 'ensures'
  ensures sum.get() == dot(a.get(), b.get())
  ensures sum.loc() == a.loc()

  // Same as above: must be 'method', not 'function method'
  glinear method {:extern} is_valid(gshared a: Ref, glinear b: Ref)
  requires a.loc() == b.loc()
  ensures dot_defined(a.get(), b.get())

  // The only reason this is a 'method' and not a 'function method'
  // is so it can easily have two return args.
  glinear method {:extern} split(glinear sum: Ref, ghost a: M, ghost b: M)
  returns (glinear a': Ref, glinear b': Ref)
  requires dot_defined(a, b)
  requires sum.get() == dot(a, b)
  ensures a'.get() == a && a'.loc() == sum.loc()
  ensures b'.get() == b && b'.loc() == sum.loc()

  function method {:extern} join_shared(gshared s: Ref, gshared t: Ref, ghost expected_q: M)
    : (gshared q: Ref)
  requires forall r :: le(s.get(), r) && le(t.get(), r) ==> le(expected_q, r)
  requires s.loc() == t.loc()
  ensures q.get() == expected_q
  ensures q.loc() == s.loc()

  function method {:extern} sub(gshared s: Ref, ghost t: M)
   : (glinear t': Ref)
  requires le(t, s.get())
  ensures t'.get() == t
  ensures t'.loc() == s.loc()
}
