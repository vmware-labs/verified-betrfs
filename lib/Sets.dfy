module Sets {
  predicate {:opaque} IsFiniteSet<A>(s: iset<A>)

  function {:opaque} FiniteSeq<A>(s: iset<A>) : seq<A>
  requires IsFiniteSet(s)
  ensures s == (iset r | r in FiniteSeq(s))
}
