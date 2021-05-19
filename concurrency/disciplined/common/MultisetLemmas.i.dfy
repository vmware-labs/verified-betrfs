include "../../lib/Base/Multisets.i.dfy"

module MultisetLemmas {
  import opened Multisets

  lemma ApplyId<A>(fn: A -> A, s: multiset<A>)
  requires forall x | x in s :: fn(x) == x
  ensures Apply(fn, s) == s
  {
  }

  lemma ApplyCompose<A,B,C>(fn: A -> B, gn: B -> C, hn: A -> C, s: multiset<A>)
  requires forall x | x in s :: gn(fn(x)) == hn(x)
  ensures Apply(gn, Apply(fn, s)) == Apply(hn, s)
  {
  }

  lemma ApplyGetBackwards<A,B>(fn : A -> B, s: multiset<A>, b: B)
  returns (a: A)
  requires b in Apply(fn, s)
  ensures fn(a) == b
  ensures a in s
  {
  }

  lemma apply_eq_1_2<A, B, C>(s: multiset<A>,
      a_c: A -> C,
      a_b: A -> B,
      b_c: B -> C)
  requires forall x | x in s :: a_c(x) == b_c(a_b(x))
  ensures Apply(a_c, s) == Apply(b_c, Apply(a_b, s))
  {
  }

  lemma MultisetSimplificationTriggers<P,Q>()
  ensures forall fn: P -> Q :: Multisets.Apply(fn, multiset{}) == multiset{};
  ensures forall fn: P -> Q, a :: Multisets.Apply(fn, multiset{a}) == multiset{fn(a)}
  ensures forall fn: P -> Q, a, s :: a in s ==> fn(a) in Multisets.Apply(fn, s)
  ensures forall fn: P -> Q, s, t :: Multisets.Apply(fn, s + t) == Multisets.Apply(fn, s) + Multisets.Apply(fn, t)
  {
    Multisets.reveal_Apply();
  }
}
