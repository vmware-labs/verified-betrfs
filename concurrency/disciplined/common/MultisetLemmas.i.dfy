include "../../../lib/Base/Multisets.i.dfy"

module MultisetLemmas {
  import opened Multisets

  lemma ApplyId<A>(fn: A -> A, s: multiset<A>)
  requires forall x | x in s :: fn(x) == x
  ensures Apply(fn, s) == s
  {
    reveal_Apply();
    if |s| == 0 {
    } else {
      var x := Choose(s);
      ApplyId(fn, s - multiset{x});
    }
  }

  lemma ApplyCompose<A,B,C>(fn: A -> B, gn: B -> C, hn: A -> C, s: multiset<A>)
  requires forall x | x in s :: gn(fn(x)) == hn(x)
  ensures Apply(gn, Apply(fn, s)) == Apply(hn, s)
  {
    if |s| == 0 {
      assert Apply(gn, Apply(fn, s)) == Apply(hn, s) by {
        reveal_Apply();
      }
    } else {
      var x := Choose(s);
      calc {
        Apply(gn, Apply(fn, s));
        {
          reveal_Apply();
          assert Apply(fn, s) == multiset{fn(x)} + Apply(fn, s - multiset{x});
        }
        Apply(gn, multiset{fn(x)} + Apply(fn, s - multiset{x}));
        {
          ApplyAdditive(gn, multiset{fn(x)}, Apply(fn, s - multiset{x}));
        }
        Apply(gn, multiset{fn(x)}) + Apply(gn, Apply(fn, s - multiset{x}));
        {
          ApplySingleton(gn, fn(x));
        }
        multiset{gn(fn(x))} + Apply(gn, Apply(fn, s - multiset{x}));
        {
          ApplyCompose(fn, gn, hn, s - multiset{x});
        }
        multiset{gn(fn(x))} + Apply(hn, s - multiset{x});
        {
          assert gn(fn(x)) == hn(x);
        }
        multiset{hn(x)} + Apply(hn, s - multiset{x});
        {
          reveal_Apply();
        }
        Apply(hn, s);
      }
    }
  }

  lemma ApplyGet<A,B>(fn : A -> B, s: multiset<A>, a: A)
  requires a in s
  ensures fn(a) in Apply(fn, s)
  {
    reveal_Apply();
    if |s| == 0 {
    } else {
      var x := Choose(s);
      if x == a {
      } else {
        ApplyGet(fn, s - multiset{x}, a);
      }
    }
  }

  lemma ApplyGetBackwards<A,B>(fn : A -> B, s: multiset<A>, b: B)
  returns (a: A)
  requires b in Apply(fn, s)
  ensures fn(a) == b
  ensures a in s
  {
    reveal_Apply();
    if |s| == 0 {
    } else {
      var x := Choose(s);
      if fn(x) == b {
        a := x;
      } else {
        a := ApplyGetBackwards(fn, s - multiset{x}, b);
      }
    }
  }

  lemma apply_eq_1_2<A, B, C>(s: multiset<A>,
      a_c: A -> C,
      a_b: A -> B,
      b_c: B -> C)
  requires forall x | x in s :: a_c(x) == b_c(a_b(x))
  ensures Apply(a_c, s) == Apply(b_c, Apply(a_b, s))
  {
    ApplyCompose(a_b, b_c, a_c, s);
  }

  predicate True<P,Q>(fn: P -> Q, a: P, s: multiset<P>) {
    true
  }

  predicate True2<P,Q>(fn: P -> Q, s: multiset<P>, t: multiset<P>) {
    true
  }

  lemma MultisetSimplificationTriggers<P,Q>()
  ensures forall fn: P -> Q :: Multisets.Apply(fn, multiset{}) == multiset{};
  ensures forall fn: P -> Q, a :: Multisets.Apply(fn, multiset{a}) == multiset{fn(a)}
  ensures forall fn: P -> Q, a, s :: True(fn, a, s) ==> a in s ==> fn(a) in Multisets.Apply(fn, s)
  ensures forall fn: P -> Q, s, t :: True2(fn, s, t) ==> Multisets.Apply(fn, s + t) == Multisets.Apply(fn, s) + Multisets.Apply(fn, t)
  {
    forall fn: P -> Q ensures Multisets.Apply(fn, multiset{}) == multiset{};
    {
      reveal_Apply();
    }

    forall fn: P -> Q, a ensures Multisets.Apply(fn, multiset{a}) == multiset{fn(a)}
    {
      ApplySingleton(fn, a);
    }

    forall fn: P -> Q, a, s {:trigger True(fn, a, s)} | a in s ensures fn(a) in Multisets.Apply(fn, s)
    {
      ApplyGet(fn, s, a);
    }

    forall fn: P -> Q, s, t {:trigger True2(fn, s, t)} ensures Multisets.Apply(fn, s + t) == Multisets.Apply(fn, s) + Multisets.Apply(fn, t)
    {
      ApplyAdditive(fn, s, t);
    }
  }
}
