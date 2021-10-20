include "PCM.s.dfy"
include "PCMExt.s.dfy"
include "PCMWrap.s.dfy"
include "../../lib/Base/Option.s.dfy"

// The common PCM contract for any concurrency primitive that supports a
// single-writer-multi-reader access mode.
abstract module Rw {
  import opened Options

  type StoredType(!new)

  type M(!new)

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M) 
  function I(x: M) : Option<StoredType> requires Inv(x)

  // The stored thing does not change (because the interpretation stays the same),
  // but the implementation of the Rw primitive this object represents has changed
  // state (in a way that doesn't affect the stored thing or the exclusivity/borrowedness).
  // For example: a rw-lock counting down the number of readers.
  predicate transition(a: M, b: M) {
    forall p: M :: Inv(dot(a, p)) ==>
        && Inv(dot(b, p))
        && I(dot(a, p)) == I(dot(b, p))
  }

  // Expresses exclusivity: withdraw something, work with it exclusively for a
  // while, deposit it back when you're done.
  predicate withdraw(a: M, b: M, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==>
        && Inv(dot(b, p))
        && I(dot(a, p)) == Some(x)
        && I(dot(b, p)) == None
  }

  // The end of an exclusive acccess.
  predicate deposit(a: M, b: M, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==>
        && Inv(dot(b, p))
        && I(dot(a, p)) == None
        && I(dot(b, p)) == Some(x)
  }

  // The property that supports shared access.
  // a guards x; this is how we implement a linear borrow.
  // A borrow "begins" when you acquire a.
  // Once you have a, this property lets you reason about the value of x.
  // The borrow "ends" when you don't hold a anymore, after which you don't
  // know anything about x.
  //
  // This is the core magic of this module: it lets you go from a shard-monoid
  // property (holding a) to knowledge of a complete-monoid property (I(a, ...)).
  predicate guard(a: M, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==>
        && I(dot(a, p)) == Some(x)
  }

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma InitImpliesInv(x: M)
  requires Init(x)
  ensures Inv(x)
  ensures I(x) == None

  // TODO(travis) I think this is probably unnecessary
  // For now, just add "or m == unit()" to your Invariant.
  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == None
}

module Rw_PCMWrap(rw: Rw) refines PCMWrap {
  type G = rw.StoredType
}

module Rw_PCMExt(rw: Rw) refines PCMExt(Rw_PCMWrap(rw)) {
  import Wrap = Rw_PCMWrap(rw)

  type M = rw.M
  function dot(x: M, y: M) : M { rw.dot(x, y) }
  predicate valid(x: M) { exists y :: rw.Inv(dot(x, y)) }
  function unit() : M { rw.unit() }

  // Partial Commutative Monoid (PCM) axioms

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
    rw.dot_unit(x);
  }

  lemma valid_unit(x: M)
  ensures valid(unit())
  {
    rw.inv_unit();
    dot_unit(unit());
    assert rw.Inv(dot(unit(), unit()));
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    rw.commutative(x, y);
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    rw.associative(x, y, z);
  }

  predicate transition(a: M, b: M) {
    rw.transition(a, b)
  }

  lemma transition_is_refl(a: M)
  //requires transition(a, a)
  { }

  lemma transition_is_trans(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires transition(b, c)
  //ensures transition(a, c)
  { }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  //ensures transition(dot(a, c), dot(b, c))
  {
    forall p: M | rw.Inv(rw.dot(rw.dot(a, c), p))
    ensures rw.Inv(rw.dot(rw.dot(b, c), p)) && rw.I(rw.dot(rw.dot(a, c), p)) == rw.I(rw.dot(rw.dot(b, c), p))
    {
      associative(b, c, p);
      associative(a, c, p);
      assert rw.Inv(rw.dot(a, rw.dot(c, p)));
    }
    assert rw.transition(dot(a, c), dot(b, c));
    assert transition(dot(a, c), dot(b, c));
  }

  function I(f: F) : Option<B> {
    if rw.Inv(f) then (
      if rw.I(f).Some? then (
        Some(Wrap.one(rw.I(f).value))
      ) else (
        Some(Wrap.unit())
      )
    ) else (
      None
    )
  }

  lemma I_unit()
  ensures I(unit()) == Some(base.unit())
  {
    rw.inv_unit();
  }

  lemma I_respects_transitions(f: F, f': F)
  //requires transition(f, f')
  //requires I(f).Some?
  //ensures I(f').Some?
  //ensures base.transition(I(f).value, I(f').value)
  {
    assert rw.Inv(f);
    rw.dot_unit(f);
    rw.dot_unit(f');
    assert rw.Inv(rw.dot(f, unit()));
  }

  lemma I_valid(f: F)
  //requires I(f).Some?
  //ensures valid(f)
  {
    assert rw.Inv(f);
    rw.dot_unit(f);
    assert rw.Inv(dot(f, unit()));
  }
}

module RwTokens(rw: Rw) {
  import opened GhostLoc

  import Wrap = Rw_PCMWrap(rw)
  import WrapT = PCMWrapTokens(Rw_PCMWrap(rw))
  import WrapPT = Tokens(Rw_PCMWrap(rw))
  import T = Tokens(Rw_PCMExt(rw))
  import ET = ExtTokens(Rw_PCMWrap(rw), Rw_PCMExt(rw))
  import pcm = Rw_PCMExt(rw)
  
  type Token = t : T.Token | t.loc.ExtLoc? && t.loc.base_loc == Wrap.singleton_loc()
    witness *

  glinear method initialize(glinear m: rw.M)
  returns (glinear token: Token)
  requires rw.Init(m)
  ensures token.val == m

  glinear method obtain_invariant_2(
      glinear inout token1: Token,
      glinear inout token2: Token)
  returns (ghost rest: rw.M)
  requires old_token1.loc == old_token2.loc
  ensures token1 == old_token1
  ensures token2 == old_token2
  ensures rw.Inv(rw.dot(rw.dot(token1.val, token2.val), rest))
  {
    T.is_valid(token1, inout token2);
    rest :| rw.Inv(rw.dot(rw.dot(token1.val, token2.val), rest));
  }

  glinear method obtain_invariant_3(
      glinear inout token1: Token,
      glinear inout token2: Token,
      glinear inout token3: Token)
  returns (ghost rest: rw.M)
  requires old_token1.loc == old_token2.loc == old_token3.loc
  ensures token1 == old_token1
  ensures token2 == old_token2
  ensures token3 == old_token3
  ensures rw.Inv(rw.dot(rw.dot(rw.dot(token1.val, token2.val), token3.val), rest))
  {
    glinear var x := T.join(token1, token2);
    T.is_valid(x, inout token3);
    token1, token2 := T.split(x, token1.val, token2.val);
    rest :| rw.Inv(rw.dot(rw.dot(rw.dot(token1.val, token2.val), token3.val), rest));
  }

  glinear method {:extern} split3(glinear sum: Token,
      ghost a: pcm.M, ghost b: pcm.M, ghost c: pcm.M)
  returns (glinear a': Token, glinear b': Token, glinear c': Token)
  requires sum.val == rw.dot(rw.dot(a, b), c)
  ensures a' == T.Token(sum.loc, a)
  ensures b' == T.Token(sum.loc, b)
  ensures c' == T.Token(sum.loc, c)
  {
    glinear var x;
    x, c' := T.split(sum, rw.dot(a, b), c);
    a', b' := T.split(x, a, b);
  }

  function method {:opaque} update(
      glinear b: Token,
      ghost expected_out: rw.M)
    : (glinear c: Token)
  requires pcm.transition(b.val, expected_out)
  ensures c == T.Token(b.loc, expected_out)
  {
    rw.dot_unit(b.val);
    rw.dot_unit(expected_out);
    rw.commutative(b.val, rw.unit());
    rw.commutative(expected_out, rw.unit());
    T.transition_update(T.get_unit_shared(b.loc), b, expected_out)
  }

  glinear method internal_transition(
      glinear token: Token,
      ghost expected_value: rw.M)
  returns (glinear token': Token)
  requires rw.transition(token.val, expected_value)
  ensures token' == T.Token(token.loc, expected_value)
  {
    token' := update(token, expected_value);
  }

  glinear method deposit(
      glinear token: Token,
      glinear stored_value: rw.StoredType,
      ghost expected_value: rw.M)
  returns (glinear token': Token)
  requires rw.deposit(token.val, expected_value, stored_value)
  ensures token' == T.Token(token.loc, expected_value)
  {
    glinear var f, b := ET.ext_transfer(
        token, expected_value, WrapT.wrap(stored_value), Wrap.unit());
    WrapPT.dispose(b);
    token' := f;
  }

  glinear method withdraw(
      glinear token: Token,
      ghost expected_value: rw.M,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token': Token, glinear retrieved_value: rw.StoredType)
  requires rw.withdraw(token.val, expected_value, expected_retrieved_value)
  ensures token' == T.Token(token.loc, expected_value)
  ensures retrieved_value == expected_retrieved_value
  {
    glinear var f, b := ET.ext_transfer(
        token, expected_value,
        WrapPT.get_unit(Wrap.singleton_loc()), Wrap.one(expected_retrieved_value));
    token' := f;
    retrieved_value := WrapT.unwrap(b);
  }

  //method borrow(glinear token: Token)

  /*
   * Helpers
   */

  glinear method internal_transition_1_2(
      glinear token1: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires rw.transition(
      token1.val,
      rw.dot(expected_value1, expected_value2))
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  {
    glinear var y := internal_transition(token1,
        rw.dot(expected_value1, expected_value2));
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method internal_transition_2_1(
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: rw.M)
  returns (glinear token1': Token)
  requires token1.loc == token2.loc
  requires rw.transition(
      rw.dot(token1.val, token2.val),
      expected_value1)
  ensures token1' == T.Token(token1.loc, expected_value1)
  {
    glinear var x := T.join(token1, token2);
    glinear var y := internal_transition(x, expected_value1);
    token1' := y;
  }

  glinear method internal_transition_2_2(
      glinear token1: Token,
      glinear token2: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires token1.loc == token2.loc
  requires rw.transition(
      rw.dot(token1.val, token2.val),
      rw.dot(expected_value1, expected_value2))
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  {
    glinear var x := T.join(token1, token2);
    glinear var y := internal_transition(x,
        rw.dot(expected_value1, expected_value2));
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method internal_transition_3_2(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires token1.loc == token2.loc == token3.loc
  requires rw.transition(
      rw.dot(rw.dot(token1.val, token2.val), token3.val),
      rw.dot(expected_value1, expected_value2))
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  {
    glinear var x := T.join(token1, token2);
    x := T.join(x, token3);
    glinear var y := internal_transition(x,
        rw.dot(expected_value1, expected_value2));
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method internal_transition_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_value3: rw.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires token1.loc == token2.loc == token3.loc
  requires rw.transition(
      rw.dot(rw.dot(token1.val, token2.val), token3.val),
      rw.dot(rw.dot(expected_value1, expected_value2), expected_value3))
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures token3' == T.Token(token1.loc, expected_value3)
  {
    glinear var x := T.join(token1, token2);
    x := T.join(x, token3);
    glinear var y := internal_transition(x,
        rw.dot(rw.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y,
        expected_value1, expected_value2, expected_value3);
  }

  glinear method deposit_2_1(
      glinear token1: Token,
      glinear token2: Token,
      glinear stored_value: rw.StoredType,
      ghost expected_value1: rw.M)
  returns (glinear token1': Token)
  requires token1.loc == token2.loc
  requires rw.deposit(
    rw.dot(token1.val, token2.val),
    expected_value1,
    stored_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  {
    glinear var x := T.join(token1, token2);
    glinear var y := deposit(x, stored_value, expected_value1);
    token1' := y;
  }

  glinear method deposit_2_2(
      glinear token1: Token,
      glinear token2: Token,
      glinear stored_value: rw.StoredType,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires token1.loc == token2.loc
  requires rw.deposit(
    rw.dot(token1.val, token2.val),
    rw.dot(expected_value1, expected_value2),
    stored_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  {
    glinear var x := T.join(token1, token2);
    glinear var y := deposit(x, stored_value,
        rw.dot(expected_value1, expected_value2));
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method deposit_3_2(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      glinear stored_value: rw.StoredType,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M)
  returns (glinear token1': Token, glinear token2': Token)
  requires token1.loc == token2.loc == token3.loc
  requires rw.deposit(
    rw.dot(rw.dot(token1.val, token2.val), token3.val),
    rw.dot(expected_value1, expected_value2),
    stored_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  {
    glinear var x := T.join(token1, token2);
    x := T.join(x, token3);
    glinear var y := deposit(x, stored_value,
        rw.dot(expected_value1, expected_value2));
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method deposit_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      glinear stored_value: rw.StoredType,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_value3: rw.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires token1.loc == token2.loc == token3.loc
  requires rw.deposit(
    rw.dot(rw.dot(token1.val, token2.val), token3.val),
    rw.dot(rw.dot(expected_value1, expected_value2), expected_value3),
    stored_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures token3' == T.Token(token1.loc, expected_value3)
  {
    glinear var x := T.join(token1, token2);
    x := T.join(x, token3);
    glinear var y := deposit(x, stored_value,
        rw.dot(rw.dot(expected_value1, expected_value2), expected_value3));
    token1', token2', token3' := split3(y,
        expected_value1, expected_value2, expected_value3);
  }

  glinear method withdraw_1_1(
      glinear token1: Token,
      ghost expected_value1: rw.M,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token1': Token,
      glinear retrieved_value: rw.StoredType)
  requires rw.withdraw(
      token1.val,
      expected_value1,
      expected_retrieved_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures retrieved_value == expected_retrieved_value
  {
    token1', retrieved_value := withdraw(token1, expected_value1, expected_retrieved_value);
  }

  glinear method withdraw_1_2(
      glinear token1: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token1': Token, glinear token2': Token,
      glinear retrieved_value: rw.StoredType)
  requires rw.withdraw(
      token1.val,
      rw.dot(expected_value1, expected_value2),
      expected_retrieved_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures retrieved_value == expected_retrieved_value
  {
    glinear var y;
    y, retrieved_value := withdraw(token1,
        rw.dot(expected_value1, expected_value2),
        expected_retrieved_value);
    token1', token2' := T.split(y, expected_value1, expected_value2);
  }

  glinear method withdraw_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_value3: rw.M,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token,
      glinear retrieved_value: rw.StoredType)
  requires token1.loc == token2.loc == token3.loc
  requires rw.withdraw(
      rw.dot(rw.dot(token1.val, token2.val), token3.val),
      rw.dot(rw.dot(expected_value1, expected_value2), expected_value3),
      expected_retrieved_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures token3' == T.Token(token1.loc, expected_value3)
  ensures retrieved_value == expected_retrieved_value
  {
    glinear var x := T.join(token1, token2);
    x := T.join(x, token3);
    glinear var y;
    y, retrieved_value := withdraw(x,
        rw.dot(rw.dot(expected_value1, expected_value2), expected_value3),
        expected_retrieved_value);
    token1', token2', token3' := split3(y, expected_value1, expected_value2, expected_value3);
  }

  glinear method get_unit(ghost loc: Loc)
  returns (glinear t: Token)
  requires loc.ExtLoc? && loc.base_loc == Wrap.singleton_loc()
  ensures t.loc == loc
  {
    t := T.get_unit(loc);
  }

  glinear method dispose(glinear t: Token)
  {
    T.dispose(t);
  }

  function method {:opaque} borrow_from_guard(gshared f: Token, ghost expected: rw.StoredType)
      : (gshared s: rw.StoredType)
  requires rw.guard(f.val, expected)
  ensures s == expected
  {
    assert forall p ::
        pcm.I(pcm.dot(f.val, p)).Some? ==> Wrap.le(Wrap.one(expected), pcm.I(pcm.dot(f.val, p)).value)
    by {
      forall p | pcm.I(pcm.dot(f.val, p)).Some?
      ensures Wrap.le(Wrap.one(expected), pcm.I(pcm.dot(f.val, p)).value)
      {
        Wrap.dot_unit(Wrap.one(expected));
      }
    }
    WrapT.unwrap_borrow(
      ET.borrow_back(f, Wrap.one(expected))
    )
  }
}
