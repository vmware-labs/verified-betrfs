module GhostLoc {
  datatype Loc =
    | BaseLoc(ghost t: nat)
    | ExtLoc(ghost s: nat, ghost base_loc: Loc)
}

abstract module PCM {
  import opened GhostLoc

  type M(!new)

  datatype Token = Token(loc: Loc, val: M)

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

  least predicate reachable(a: M, b: M) {
    a == b || (exists z :: reachable(a, z) && transition(z, b))
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  requires dot_defined(a, c)
  ensures dot_defined(b, c)
  ensures transition(dot(a, c), dot(b, c))

  /*
   * Actions
   */

  function method {:extern} transition_update(
      gshared s: Token,
      glinear b: Token,
      ghost expected_out: M)
    : (glinear c: Token)
  requires s.loc == b.loc
  requires dot_defined(s.val, b.val) ==>
    dot_defined(s.val, expected_out)
      && transition(
        dot(s.val, b.val),
        dot(s.val, expected_out))
  ensures c.val == expected_out
  ensures c.loc == s.loc

  function method {:extern} get_unit(ghost loc: Loc) : (glinear u: Token)
  ensures u.val == unit() && u.loc == loc

  glinear method {:extern} dispose(glinear u: Token)

  function method {:extern} get_unit_shared(ghost loc: Loc) : (gshared u: Token)
  ensures u.val == unit() && u.loc == loc

  // This MUST be 'method', as it wouldn't be safe to call this and
  // obtain the postconditions from only ghost 'a' and 'b'.
  glinear method {:extern} join(glinear a: Token, glinear b: Token)
  returns (glinear sum: Token)
  requires a.loc == b.loc
  ensures dot_defined(a.val, b.val) // yes, this is an 'ensures'
  ensures sum.val == dot(a.val, b.val)
  ensures sum.loc == a.loc

  // Same as above: must be 'method', not 'function method'
  glinear method {:extern} is_valid(gshared a: Token, glinear inout b: Token)
  requires a.loc == old_b.loc
  ensures b == old_b
  ensures dot_defined(a.val, b.val)

  // The only reason this is a 'method' and not a 'function method'
  // is so it can easily have two return args.
  glinear method {:extern} split(glinear sum: Token, ghost a: M, ghost b: M)
  returns (glinear a': Token, glinear b': Token)
  requires dot_defined(a, b)
  requires sum.val == dot(a, b)
  ensures a'.val == a && a'.loc == sum.loc
  ensures b'.val == b && b'.loc == sum.loc

  function method {:extern} join_shared(gshared s: Token, gshared t: Token, ghost expected_q: M)
    : (gshared q: Token)
  requires forall r :: le(s.val, r) && le(t.val, r) ==> le(expected_q, r)
  requires s.loc == t.loc
  ensures q.val == expected_q
  ensures q.loc == s.loc

  function method {:extern} sub(gshared s: Token, ghost t: M)
   : (glinear t': Token)
  requires le(t, s.val)
  ensures t'.val == t
  ensures t'.loc == s.loc
}
