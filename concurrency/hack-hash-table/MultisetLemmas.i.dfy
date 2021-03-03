include "../../lib/Base/Multisets.i.dfy"

module MultisetLemmas {
  import opened Multisets

  lemma ApplyId<A>(fn: A ~> A, s: multiset<A>)
  requires forall x | x in s :: fn(x) == x
  ensures Apply(fn, s) == s
  {
  }

  lemma ApplyCompose<A,B,C>(fn: A ~> B, gn: B ~> C, hn: A ~> C, s: multiset<A>)
  requires forall x | x in s :: gn(fn(x)) == hn(x)
  ensures Apply(gn, Apply(fn, s)) == Apply(hn, s)
  {
  }
}
