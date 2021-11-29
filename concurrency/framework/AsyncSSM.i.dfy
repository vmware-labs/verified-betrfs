include "AsyncSSM.s.dfy"

module TicketStubToken(IOIfc: InputOutputIfc, ssm: TicketStubSSM(IOIfc)) {
  import pcm = TicketStubPCM(IOIfc, ssm)
  import Tokens = Tokens(pcm)

  type Token = Tokens.Token

  glinear method obtain_invariant_1(
      glinear inout token1: Token)
  returns (ghost rest1: ssm.M)
  ensures token1 == old_token1
  ensures ssm.Inv(ssm.dot(token1.val, rest1))
  {
    gshared var u := Tokens.get_unit_shared(token1.loc);
    ssm.commutative(u.val, token1.val);
    ssm.dot_unit(token1.val);
    rest1 := obtain_invariant_1_1(u, inout token1);
  }

  glinear method obtain_invariant_1_1(
      gshared s_token1: Token,
      glinear inout token2: Token)
  returns (ghost rest1: ssm.M)
  requires s_token1.loc == old_token2.loc
  ensures token2 == old_token2
  ensures ssm.Inv(ssm.dot(ssm.dot(s_token1.val, token2.val), rest1))
  {
    Tokens.is_valid(s_token1, inout token2);

    rest1 :| ssm.Inv(ssm.dot(
        ssm.dot(s_token1.val, token2.val),
        rest1));
  }

  glinear method obtain_invariant_1_2(
      gshared s_token1: Token,
      glinear inout token2: Token,
      glinear inout token3: Token)
  returns (ghost rest1: ssm.M)
  requires s_token1.loc == old_token2.loc == old_token3.loc
  ensures token2 == old_token2
  ensures token3 == old_token3
  ensures ssm.Inv(ssm.dot(ssm.dot(s_token1.val, ssm.dot(token2.val, token3.val)), rest1))
  {
    glinear var t := Tokens.join(token2, token3);
    rest1 := obtain_invariant_1_1(s_token1, inout t);
    token2, token3 := Tokens.split(t, token2.val, token3.val);
  }

  lemma transition_of_next(a: ssm.M, b: ssm.M)
  requires ssm.Internal(a, b)
  ensures pcm.transition(a, b)
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    var a' := a;
    var b' := b;
    var c := ssm.unit();
    assert a == ssm.dot(a', c) && b == ssm.dot(b', c) && ssm.Internal(a', b');
    assert pcm.single_step_helper(a, b, a', b', c);
    assert pcm.single_step(a, b);
  }

  lemma transition_of_next_with_unit(a: ssm.M, b: ssm.M)
  requires ssm.Internal(a, b)
  ensures pcm.transition(pcm.dot(ssm.unit(), a), pcm.dot(ssm.unit(), b))
  {
    ssm.dot_unit(a);
    ssm.dot_unit(b);
    ssm.commutative(a, ssm.unit());
    ssm.commutative(b, ssm.unit());
    transition_of_next(a, b);
  }

  glinear method transition_1_1(glinear a: Token, ghost expect_b: ssm.M)
  returns (glinear b: Token)
  requires ssm.Internal(a.val, expect_b)
  ensures b == Tokens.Token(a.loc, expect_b)
  {
    transition_of_next_with_unit(a.val, expect_b);
    b := Tokens.transition_update(Tokens.get_unit_shared(a.loc), a, expect_b);
  }

  glinear method transition_1_1_1(gshared s: Token, glinear a: Token, ghost expect_b: ssm.M)
  returns (glinear b: Token)
  requires ssm.Internal(ssm.dot(s.val, a.val), ssm.dot(s.val, expect_b))
  requires s.loc == a.loc
  ensures b == Tokens.Token(a.loc, expect_b)
  {
    transition_of_next(ssm.dot(s.val, a.val), ssm.dot(s.val, expect_b));
    b := Tokens.transition_update(s, a, expect_b);
  }

  glinear method transition_2_2(
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires token1.loc == token2.loc
  requires ssm.Internal(
      ssm.dot(token1.val, token2.val),
      ssm.dot(expected_value1, expected_value2))
  ensures token1' == Tokens.Token(token1.loc, expected_value1)
  ensures token2' == Tokens.Token(token1.loc, expected_value2)
  {
    glinear var x := Tokens.join(token1, token2);
    glinear var y := transition_1_1(x,  
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := Tokens.split(y, expected_value1, expected_value2);
  }

  glinear method transition_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M,
      ghost expected_value3: pcm.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires token1.loc == token2.loc == token3.loc
  requires ssm.Internal(
      ssm.dot(ssm.dot(token1.val, token2.val), token3.val),
      ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3))
  ensures token1' == Tokens.Token(token1.loc, expected_value1)
  ensures token2' == Tokens.Token(token1.loc, expected_value2)
  ensures token3' == Tokens.Token(token1.loc, expected_value3)
  {
    glinear var x := Tokens.join(token1, token2);
    x := Tokens.join(x, token3);
    glinear var y := transition_1_1(x,  
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }

  glinear method {:extern} split3(glinear sum: Token,
      ghost a: pcm.M, ghost b: pcm.M, ghost c: pcm.M)
  returns (glinear a': Token, glinear b': Token, glinear c': Token)
  requires sum.val == ssm.dot(ssm.dot(a, b), c)
  ensures a' == Tokens.Token(sum.loc, a)
  ensures b' == Tokens.Token(sum.loc, b)
  ensures c' == Tokens.Token(sum.loc, c)
  {
    glinear var x;
    x, c' := Tokens.split(sum, ssm.dot(a, b), c);
    a', b' := Tokens.split(x, a, b);
  }

  glinear method transition_1_2_2(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires s.loc == token1.loc == token2.loc
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(token1.val, token2.val)),
      ssm.dot(s.val, ssm.dot(expected_value1, expected_value2)))
  ensures token1' == Tokens.Token(token1.loc, expected_value1)
  ensures token2' == Tokens.Token(token1.loc, expected_value2)
  {
    glinear var x := Tokens.join(token1, token2);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := Tokens.split(y, expected_value1, expected_value2);
  }

  glinear method transition_1_3_3(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M,
      ghost expected_value3: pcm.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires s.loc == token1.loc == token2.loc == token3.loc
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(ssm.dot(token1.val, token2.val), token3.val)),
      ssm.dot(s.val, ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3)))
  ensures token1' == Tokens.Token(token1.loc, expected_value1)
  ensures token2' == Tokens.Token(token1.loc, expected_value2)
  ensures token3' == Tokens.Token(token1.loc, expected_value3)
  {
    glinear var x := Tokens.join(token1, token2);
    x := Tokens.join(x, token3);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }

  glinear method {:opaque} inout_update_next(glinear inout a: Token, ghost expect_b: ssm.M)
  requires ssm.Internal(old_a.val, expect_b)
  ensures a == Tokens.Token(old_a.loc, expect_b)
  {
    a := transition_1_1(a, expect_b);
  }

  glinear method split5(glinear sum: Token,
      ghost a: pcm.M, ghost b: pcm.M, ghost c: pcm.M, ghost d: pcm.M, ghost e: pcm.M)
  returns (glinear a': Token, glinear b': Token, glinear c': Token, glinear d': Token, glinear e': Token)
  requires sum.val == ssm.dot(ssm.dot(ssm.dot(ssm.dot(a, b), c), d), e)
  ensures a' == Tokens.Token(sum.loc, a)
  ensures b' == Tokens.Token(sum.loc, b)
  ensures c' == Tokens.Token(sum.loc, c)
  ensures d' == Tokens.Token(sum.loc, d)
  ensures e' == Tokens.Token(sum.loc, e)
  {
    glinear var x;
    x, e' := Tokens.split(sum, ssm.dot(ssm.dot(ssm.dot(a, b), c), d), e);
    x, d' := Tokens.split(x, ssm.dot(ssm.dot(a, b), c), d);
    x, c' := Tokens.split(x, ssm.dot(a, b), c);
    a', b' := Tokens.split(x, a, b);
  }

  // TODO unused glinear method split6(glinear sum: Token,
  // TODO unused     ghost a: pcm.M, ghost b: pcm.M, ghost c: pcm.M, ghost d: pcm.M, ghost e: pcm.M, ghost f: pcm.M)
  // TODO unused returns (glinear a': Token, glinear b': Token, glinear c': Token, glinear d': Token, glinear e': Token, glinear f': Token)
  // TODO unused requires sum.val == ssm.dot(ssm.dot(ssm.dot(ssm.dot(ssm.dot(a, b), c), d), e), f)
  // TODO unused ensures a' == Tokens.Token(sum.loc, a)
  // TODO unused ensures b' == Tokens.Token(sum.loc, b)
  // TODO unused ensures c' == Tokens.Token(sum.loc, c)
  // TODO unused ensures d' == Tokens.Token(sum.loc, d)
  // TODO unused ensures e' == Tokens.Token(sum.loc, e)
  // TODO unused ensures f' == Tokens.Token(sum.loc, f)
  // TODO unused {
  // TODO unused   glinear var x;
  // TODO unused   x, f' := Tokens.split(sum, ssm.dot(ssm.dot(ssm.dot(ssm.dot(a, b), c), d), e), f);
  // TODO unused   x, e' := Tokens.split(x, ssm.dot(ssm.dot(ssm.dot(a, b), c), d), e);
  // TODO unused   x, d' := Tokens.split(x, ssm.dot(ssm.dot(a, b), c), d);
  // TODO unused   x, c' := Tokens.split(x, ssm.dot(a, b), c);
  // TODO unused   a', b' := Tokens.split(x, a, b);
  // TODO unused }
}
