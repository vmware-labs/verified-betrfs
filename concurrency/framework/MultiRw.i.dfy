include "PCM.s.dfy"
include "PCMExt.s.dfy"
include "PCMWrap.s.dfy"
include "../../lib/Base/Multisets.i.dfy"
include "../../lib/Base/Option.s.dfy"

abstract module MultiRw {
  type Key(!new)
  type StoredType(!new)

  type M(!new)

  function dot(x: M, y: M) : M
  function unit() : M

  predicate Init(s: M)
  predicate Inv(x: M) 
  function I(x: M) : map<Key, StoredType> requires Inv(x)

  predicate transition(a: M, b: M) {
    forall p: M :: Inv(dot(a, p)) ==> Inv(dot(b, p))
        && I(dot(a, p)) == I(dot(b, p))
  }

  predicate deposit(a: M, b: M, key: Key, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==> Inv(dot(b, p))
        && key !in I(dot(a, p))
        && I(dot(b, p)) == I(dot(a, p))[key := x]
  }

  predicate withdraw(a: M, b: M, key: Key, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==> Inv(dot(b, p))
        && I(dot(a, p)) == I(dot(b, p))[key := x]
        && key !in I(dot(b, p))
  }

  predicate borrow(a: M, key: Key, x: StoredType)
  {
    forall p: M :: Inv(dot(a, p)) ==>
        && key in I(dot(a, p))
        && I(dot(a, p))[key] == x
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
  ensures I(x) == map[]

  // TODO(travis) I think this is probably unnecessary
  // For now, just add "or m == unit()" to your Invariant.
  lemma inv_unit()
  ensures Inv(unit())
  ensures I(unit()) == map[]
}

module MultiRw_PCMWrap(rw: MultiRw) refines PCMWrap {
  type G = rw.StoredType
}

module MultiRw_PCMExt(rw: MultiRw) refines PCMExt(MultiRw_PCMWrap(rw)) {
  import Wrap = MultiRw_PCMWrap(rw)
  import opened Multisets

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
      Some(Wrap.M(ValueMultiset(rw.I(f))))
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

module MultiRwTokens(rw: MultiRw) {
  import opened GhostLoc

  import Wrap = MultiRw_PCMWrap(rw)
  import WrapT = PCMWrapTokens(MultiRw_PCMWrap(rw))
  import WrapPT = Tokens(MultiRw_PCMWrap(rw))
  import T = Tokens(MultiRw_PCMExt(rw))
  import ET = ExtTokens(MultiRw_PCMWrap(rw), MultiRw_PCMExt(rw))
  import pcm = MultiRw_PCMExt(rw)
  import Multisets
  
  type Token = t : T.Token | t.loc.ExtLoc? && t.loc.base_loc == Wrap.singleton_loc()
    witness *

  glinear method initialize(glinear m: rw.M)
  returns (glinear token: Token)
  requires rw.Init(m)
  ensures token.val == m

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
      ghost key: rw.Key,
      glinear stored_value: rw.StoredType,
      ghost expected_value: rw.M)
  returns (glinear token': Token)
  requires rw.deposit(token.val, expected_value, key, stored_value)
  ensures token' == T.Token(token.loc, expected_value)
  {
    glinear var m := WrapT.wrap(stored_value);
    ghost var m' := Wrap.unit();

    forall p |
          pcm.I(pcm.dot(token.val, p)).Some?
            && Wrap.valid(Wrap.dot(m.val, pcm.I(pcm.dot(token.val, p)).value))
    ensures pcm.I(pcm.dot(expected_value, p)).Some?
    ensures Wrap.transition(
              Wrap.dot(m.val, pcm.I(pcm.dot(token.val, p)).value),
              Wrap.dot(m', pcm.I(pcm.dot(expected_value, p)).value))
    {
      Multisets.ValueMultisetInduct(rw.I(rw.dot(token.val, p)), key, stored_value);
      /*
       calc {
         Wrap.dot(m.val, pcm.I(pcm.dot(token.val, p)).value);
         Wrap.dot(Wrap.M(multiset{stored_value}), pcm.I(pcm.dot(token.val, p)).value);
         pcm.I(pcm.dot(expected_value, p)).value;
         Wrap.dot(m', pcm.I(pcm.dot(expected_value, p)).value);
       }
       */
    }

    glinear var f, b := ET.ext_transfer(
        token, expected_value, m, Wrap.unit());
    WrapPT.dispose(b);
    token' := f;
  }

  glinear method withdraw(
      glinear token: Token,
      ghost expected_value: rw.M,
      ghost key: rw.Key,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token': Token, glinear retrieved_value: rw.StoredType)
  requires rw.withdraw(token.val, expected_value, key, expected_retrieved_value)
  ensures token' == T.Token(token.loc, expected_value)
  ensures retrieved_value == expected_retrieved_value
  {
    glinear var m := WrapPT.get_unit(Wrap.singleton_loc());
    ghost var m' := Wrap.one(expected_retrieved_value);

    forall p |
          pcm.I(pcm.dot(token.val, p)).Some?
            && Wrap.valid(Wrap.dot(m.val, pcm.I(pcm.dot(token.val, p)).value))
    ensures pcm.I(pcm.dot(expected_value, p)).Some?
    ensures Wrap.transition(
              Wrap.dot(m.val, pcm.I(pcm.dot(token.val, p)).value),
              Wrap.dot(m', pcm.I(pcm.dot(expected_value, p)).value))
    {
      Multisets.ValueMultisetInduct(rw.I(rw.dot(expected_value, p)), key,
          expected_retrieved_value);
    }

    glinear var f, b := ET.ext_transfer(
        token, expected_value,
        m, m');
    token' := f;
    retrieved_value := WrapT.unwrap(b);
  }

  glinear method obtain_invariant_3(
      glinear inout token1: Token,
      glinear inout token2: Token,
      glinear inout token3: Token)
  returns (ghost rest: rw.M)
  requires old_token1.loc == old_token2.loc == old_token3.loc
  ensures (
    && old_token1 == token1
    && old_token2 == token2
    && old_token3 == token3
  )
  ensures rw.Inv(rw.dot(rw.dot(rw.dot(token1.val, token2.val), token3.val), rest))

  // TODO borrow method

  /*
   * Helpers
   */

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

  glinear method deposit_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost key: rw.Key,
      glinear stored_value: rw.StoredType,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_value3: rw.M)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token)
  requires token1.loc == token2.loc == token3.loc
  requires rw.deposit(
    rw.dot(rw.dot(token1.val, token2.val), token3.val),
    rw.dot(rw.dot(expected_value1, expected_value2), expected_value3),
    key, stored_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures token3' == T.Token(token1.loc, expected_value3)

  glinear method withdraw_3_3(
      glinear token1: Token,
      glinear token2: Token,
      glinear token3: Token,
      ghost expected_value1: rw.M,
      ghost expected_value2: rw.M,
      ghost expected_value3: rw.M,
      ghost key: rw.Key,
      ghost expected_retrieved_value: rw.StoredType)
  returns (glinear token1': Token, glinear token2': Token, glinear token3': Token,
      glinear retrieved_value: rw.StoredType)
  requires token1.loc == token2.loc == token3.loc
  requires rw.withdraw(
      rw.dot(rw.dot(token1.val, token2.val), token3.val),
      rw.dot(rw.dot(expected_value1, expected_value2), expected_value3),
      key, expected_retrieved_value)
  ensures token1' == T.Token(token1.loc, expected_value1)
  ensures token2' == T.Token(token1.loc, expected_value2)
  ensures token3' == T.Token(token1.loc, expected_value3)
  ensures retrieved_value == expected_retrieved_value
}
