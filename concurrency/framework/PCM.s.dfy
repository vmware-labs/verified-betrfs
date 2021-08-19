module GhostLoc {
  datatype Loc =
    | BaseLoc(ghost t: nat)
    | ExtLoc(ghost s: nat, ghost base_loc: Loc)
}

abstract module PCM {
  type M(!new)
  function dot(x: M, y: M) : M
  predicate valid(x: M) 
  function unit() : M

  // Partial Commutative Monoid (PCM) axioms

  predicate le(x: M, y: M)
  {
    exists x1 :: dot(x, x1) == y
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma valid_unit(x: M)
  ensures valid(unit())

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  // Transitions

  predicate transition(a: M, b: M)

  lemma transition_is_refl(a: M)
  requires transition(a, a)

  lemma transition_is_trans(a: M, b: M, c: M)
  requires transition(a, b)
  requires transition(b, c)
  ensures transition(a, c)

  lemma transition_is_monotonic(a: M, b: M, c: M)
  requires transition(a, b)
  ensures transition(dot(a, c), dot(b, c))
}

// TODO doesn't need to be a .s
abstract module BasicPCM refines PCM {
  predicate transition(a: M, b: M) {
    forall c :: valid(dot(a, c)) ==> valid(dot(b, c))
  }
  
  lemma transition_is_refl(a: M)
  {
  }

  lemma transition_is_trans(a: M, b: M, c: M)
  {
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  {
    forall d | valid(dot(dot(a, c), d))
    ensures valid(dot(dot(b, c), d))
    {
      associative(a, c, d);
      associative(b, c, d);
    }
  }
}

module Tokens(pcm: PCM) {
  import opened GhostLoc

  datatype Token = Token(ghost loc: Loc, ghost val: pcm.M)

  function method {:extern} transition_update(
      gshared s: Token,
      glinear b: Token,
      ghost expected_out: pcm.M)
    : (glinear c: Token)
  requires s.loc == b.loc
  requires pcm.transition(
        pcm.dot(s.val, b.val),
        pcm.dot(s.val, expected_out))
  ensures c == Token(s.loc, expected_out)

  function method {:extern} get_unit(ghost loc: Loc) : (glinear u: Token)
  ensures u == Token(loc, pcm.unit())

  glinear method {:extern} dispose(glinear u: Token)

  function method {:extern} get_unit_shared(ghost loc: Loc) : (gshared u: Token)
  ensures u == Token(loc, pcm.unit())

  // This MUST be 'method', as it wouldn't be safe to call this and
  // obtain the postconditions from only ghost 'a' and 'b'.
  glinear method {:extern} join(glinear a: Token, glinear b: Token)
  returns (glinear sum: Token)
  requires a.loc == b.loc
  ensures pcm.valid(pcm.dot(a.val, b.val)) // yes, this is an 'ensures'
  ensures sum == Token(a.loc, pcm.dot(a.val, b.val))

  glinear method {:extern} inout_join(glinear inout a: Token, glinear b: Token)
  requires old_a.loc == b.loc
  ensures pcm.valid(pcm.dot(old_a.val, b.val)) // yes, this is an 'ensures'
  ensures a == Token(old_a.loc, pcm.dot(old_a.val, b.val))

  // Same as above: must be 'method', not 'function method'
  glinear method {:extern} is_valid(gshared a: Token, glinear inout b: Token)
  requires a.loc == old_b.loc
  ensures b == old_b
  ensures pcm.valid(pcm.dot(a.val, b.val))

  // The only reason this is a 'method' and not a 'function method'
  // is so it can easily have two return args.
  glinear method {:extern} split(glinear sum: Token, ghost a: pcm.M, ghost b: pcm.M)
  returns (glinear a': Token, glinear b': Token)
  requires sum.val == pcm.dot(a, b)
  ensures a' == Token(sum.loc, a)
  ensures b' == Token(sum.loc, b)

  glinear method {:extern} inout_split(glinear inout sum: Token, ghost a: pcm.M, ghost b: pcm.M)
  returns (glinear b': Token)
  requires old_sum.val == pcm.dot(a, b)
  ensures sum == Token(old_sum.loc, a)
  ensures b' == Token(old_sum.loc, b)

  function method {:extern} join_shared(gshared s: Token, gshared t: Token, ghost expected_q: pcm.M)
    : (gshared q: Token)
  requires forall r :: pcm.le(s.val, r) && pcm.le(t.val, r) ==> pcm.le(expected_q, r)
  requires s.loc == t.loc
  ensures q == Token(s.loc, expected_q)

  function method {:extern} sub(gshared s: Token, ghost t: pcm.M)
   : (glinear t': Token)
  requires pcm.le(t, s.val)
  ensures t' == Token(s.loc, t)
}
