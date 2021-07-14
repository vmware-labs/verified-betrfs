include "PCM.s.dfy"

abstract module SSM {
  type M(!new)

  predicate Init(s: M)
  predicate Next(shard: M, shard': M)
  predicate Inv(s: M)

  function dot(x: M, y: M) : M
  function unit() : M

  lemma InitImpliesInv(s: M)
  requires Init(s)
  ensures Inv(s)

  lemma NextImpliesInv(shard: M, shard': M, rest: M)
  requires Inv(dot(shard, rest))
  requires Next(shard, shard')
  ensures Inv(dot(shard', rest))

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)
}

module SSM_PCM(ssm: SSM) refines PCM {
  type M = ssm.M

  function dot(x: M, y: M) : M { ssm.dot(x, y) }
  function unit() : M { ssm.unit() }

  predicate valid(x: M) {
    exists y :: ssm.Inv(dot(x, y))
  }

  lemma dot_unit(x: M)
  //ensures dot(x, unit()) == x
  {
    ssm.dot_unit(x);
  }

  lemma valid_unit(x: M)
  //ensures valid(unit())
  {
    var x := ssm.exists_inv_state();
    commutative(unit(), x);
    dot_unit(x);
    assert ssm.Inv(dot(unit(), x));
  }

  lemma commutative(x: M, y: M)
  //ensures dot(x, y) == dot(y, x)
  {
    ssm.commutative(x, y);
  }

  lemma associative(x: M, y: M, z: M)
  //ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    ssm.associative(x, y, z);
  }

  // Transitions

  predicate single_step_helper(a: M, b: M, a': M, b': M, c: M) {
    a == dot(a', c) && b == dot(b', c) && ssm.Next(a', b')
  }

  predicate single_step(a: M, b: M) {
    exists a', b', c :: single_step_helper(a, b, a', b', c)
  }

  least predicate reachable(a: M, b: M) {
    a == b || (exists z :: reachable(a, z) && single_step(z, b))
  }

  predicate transition(a: M, b: M) {
    reachable(a, b)
  }

  lemma transition_is_refl(a: M)
  //requires transition(a, a)
  {
  }

  least lemma reachable_is_trans(a: M, b: M, c: M)
  requires reachable(b, c)
  requires transition(a, b)
  ensures reachable(a, c)
  {
    if b == c {
    } else {
      var z :| reachable(b, z) && single_step(z, c);
      reachable_is_trans(a, b, z);
    }
  }

  lemma transition_is_trans(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires transition(b, c)
  ensures transition(a, c)
  {
    reachable_is_trans(a, b, c);
  }

  least lemma reachable_is_monotonic(a: M, b: M, c: M)
  requires reachable(a, b)
  ensures reachable(dot(a, c), dot(b, c))
  {
    if a == b {
    } else {
      var z :| reachable(a, z) && single_step(z, b);
      reachable_is_monotonic(a, z, c);
      var z', b', d :| single_step_helper(z, b, z', b', d);
      associative(z', d, c);
      associative(b', d, c);
      assert single_step_helper(dot(z, c), dot(b, c), z', b', dot(d, c));
      assert single_step(dot(z, c), dot(b, c));
    }
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  ensures transition(dot(a, c), dot(b, c))
  {
    reachable_is_monotonic(a, b, c);
  }
}

module SSMTokens(ssm: SSM) {
  import pcm = SSM_PCM(ssm)
  import Tokens = Tokens(pcm)

  type Token = Tokens.Token

  lemma transition_of_next(a: ssm.M, b: ssm.M)
  requires ssm.Next(a, b)
  ensures pcm.transition(a, b)
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    var a' := a;
    var b' := b;
    var c := ssm.unit();
    assert a == ssm.dot(a', c) && b == ssm.dot(b', c) && ssm.Next(a', b');
    assert pcm.single_step_helper(a, b, a', b', c);
    assert pcm.single_step(a, b);
  }

  lemma transition_of_next_with_unit(a: ssm.M, b: ssm.M)
  requires ssm.Next(a, b)
  ensures pcm.transition(pcm.dot(ssm.unit(), a), pcm.dot(ssm.unit(), b))
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    ssm.commutative(a, ssm.unit());
    ssm.commutative(b, ssm.unit());
    transition_of_next(a, b);
  }

  function method {:opaque} update_next(glinear a: Token, ghost expect_b: ssm.M)
      : (glinear b: Token)
  requires ssm.Next(a.val, expect_b)
  ensures b == Tokens.Token(a.loc, expect_b)
  {
    transition_of_next_with_unit(a.val, expect_b);
    Tokens.transition_update(Tokens.get_unit_shared(a.loc), a, expect_b)
  }

  // TODO more stuff here ...
}
