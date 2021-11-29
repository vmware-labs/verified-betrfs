include "DiskSSM.s.dfy"

module DiskTokenUtils(IOIfc: InputOutputIfc, ssm: DiskSSM(IOIfc)) {
  import pcm = DiskPCM(IOIfc, ssm)
  import Tokens = Tokens(pcm)
  import opened GhostLoc
  import opened DiskSingletonLoc
  import opened Dt = DiskToken(IOIfc, ssm)

  glinear method obtain_invariant_1_1(
      gshared s_token1: Token,
      glinear inout token2: Token)
  returns (ghost rest1: ssm.M)
  ensures token2 == old_token2
  ensures ssm.Inv(ssm.dot(ssm.dot(s_token1.val, token2.val), rest1))
  {
    glinear var t := Token_unfold(token2);
    Tokens.is_valid(Token_unfold_borrow(s_token1), inout t);
    token2 := Token_fold(token2, t);

    rest1 :| ssm.Inv(ssm.dot(
        ssm.dot(s_token1.defn().val, t.val),
        rest1));
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
  ensures b == Token(expect_b)
  {
    transition_of_next_with_unit(a.val, expect_b);
    glinear var bx := Tokens.transition_update(Tokens.get_unit_shared(loc()), Token_unfold(a), expect_b);
    b := Token_fold(Token(bx.val), bx);
  }

  glinear method transition_1_1_1(gshared s: Token, glinear a: Token, ghost expect_b: ssm.M)
  returns (glinear b: Token)
  requires ssm.Internal(ssm.dot(s.val, a.val), ssm.dot(s.val, expect_b))
  ensures b == Token(expect_b)
  {
    transition_of_next(ssm.dot(s.val, a.val), ssm.dot(s.val, expect_b));
    glinear var bx := Tokens.transition_update(Token_unfold_borrow(s), Token_unfold(a), expect_b);
    b := Token_fold(Token(bx.val), bx);
  }

  glinear method transition_2_2(
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires ssm.Internal(
      ssm.dot(token1.val, token2.val),
      ssm.dot(expected_value1, expected_value2))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  {
    glinear var x := join(token1, token2);
    glinear var y := transition_1_1(x,  
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := split2(y, expected_value1, expected_value2);
  }

  glinear method transition_2_3(
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M,
      ghost expected_value3: pcm.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires ssm.Internal(
      ssm.dot(token1.val, token2.val),
      ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  ensures token3' == Token(expected_value3)
  {
    glinear var x := join(token1, token2);
    glinear var y := transition_1_1(x,  
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }

  glinear method transition_3_2(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires ssm.Internal(
      ssm.dot(ssm.dot(token1.val, token2.val), token3.val),
      ssm.dot(expected_value1, expected_value2))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  {
    glinear var x := join(token1, token2);
    x := join(x, token3);
    glinear var y := transition_1_1(x,  
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := split2(y, expected_value1, expected_value2);
  }

  glinear method transition_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M,
      ghost expected_value3: pcm.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires ssm.Internal(
      ssm.dot(ssm.dot(token1.val, token2.val), token3.val),
      ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  ensures token3' == Token(expected_value3)
  {
    glinear var x := join(token1, token2);
    x := join(x, token3);
    glinear var y := transition_1_1(x,  
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }

  glinear method join(glinear a: Token, glinear b: Token)
  returns (glinear sum: Token)
  ensures sum.val == ssm.dot(a.val, b.val)
  {
    glinear var sum1 := Tokens.join(Token_unfold(a), Token_unfold(b));
    sum := Token_fold(Token(sum1.val), sum1);
  }

  glinear method split2(glinear sum: Token,
      ghost a: pcm.M, ghost b: pcm.M)
  returns (glinear a': Token, glinear b': Token)
  requires sum.val == ssm.dot(a, b)
  ensures a' == Token(a)
  ensures b' == Token(b)
  {
    glinear var a1, b1 := Tokens.split(Token_unfold(sum), a, b);
    a' := Token_fold(Token(a), a1);
    b' := Token_fold(Token(b), b1);
  }

  glinear method split3(glinear sum: Token,
      ghost a: pcm.M, ghost b: pcm.M, ghost c: pcm.M)
  returns (glinear a': Token, glinear b': Token, glinear c': Token)
  requires sum.val == ssm.dot(ssm.dot(a, b), c)
  ensures a' == Token(a)
  ensures b' == Token(b)
  ensures c' == Token(c)
  {
    glinear var x;
    x, c' := split2(sum, ssm.dot(a, b), c);
    a', b' := split2(x, a, b);
  }

  glinear method transition_1_1_2(
      gshared s: Token,
      glinear token1: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires ssm.Internal(
      ssm.dot(s.val, token1.val),
      ssm.dot(s.val, ssm.dot(expected_value1, expected_value2)))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  {
    glinear var y := transition_1_1_1(s, token1,
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := split2(y, expected_value1, expected_value2);
  }

  glinear method transition_1_2_3(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M,
      ghost expected_value3: pcm.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(token1.val, token2.val)),
      ssm.dot(s.val, ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3)))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  ensures token3' == Token(expected_value3)
  {
    glinear var x := join(token1, token2);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }


  glinear method transition_1_2_2(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(token1.val, token2.val)),
      ssm.dot(s.val, ssm.dot(expected_value1, expected_value2)))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  {
    glinear var x := join(token1, token2);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := split2(y, expected_value1, expected_value2);
  }

  glinear method transition_1_2_1(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: pcm.M)
  returns (glinear token1': Token)
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(token1.val, token2.val)),
      ssm.dot(s.val, expected_value1))
  ensures token1' == Token(expected_value1)
  {
    glinear var x := join(token1, token2);
    glinear var y := transition_1_1_1(s, x, expected_value1);
    token1' := y;
  }

  glinear method transition_1_3_2(
      gshared s: Token,
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: pcm.M,
      ghost expected_value2: pcm.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(ssm.dot(token1.val, token2.val), token3.val)),
      ssm.dot(s.val, ssm.dot(expected_value1, expected_value2)))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  {
    glinear var x := join(token1, token2);
    x := join(x, token3);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(expected_value1, expected_value2));
    token1', token2' := split2(y, expected_value1, expected_value2);
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
  requires ssm.Internal(
      ssm.dot(s.val, ssm.dot(ssm.dot(token1.val, token2.val), token3.val)),
      ssm.dot(s.val, ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3)))
  ensures token1' == Token(expected_value1)
  ensures token2' == Token(expected_value2)
  ensures token3' == Token(expected_value3)
  {
    glinear var x := join(token1, token2);
    x := join(x, token3);
    glinear var y := transition_1_1_1(s, x,
        ssm.dot(ssm.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }
}
