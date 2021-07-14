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
  // TODO fill in init, transition, withdraw, deposit methods
}
