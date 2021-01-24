abstract module ResourceSpec {
  type R(==, !new)
  predicate Init(s: multiset<R>)
  predicate transform(a: multiset<R>, b: multiset<R>)

  predicate Inv(s: multiset<R>)

  // TODO create one general axiom (e.g., taking an lseq)

  method {:axiom} is_allowed_1(shared a: R)
  returns (t: multiset<R>)
  ensures a in t
  ensures Inv(t)

  method {:axiom} is_allowed_2(shared a: R, shared b: R)
  returns (t: multiset<R>)
  ensures a in t
  ensures b in t
  ensures Inv(t)

  method {:axiom} transform_1_2(
      linear a1: R,
      ghost b1: R,
      ghost b2: R)
  returns (linear b1': R, linear b2': R)
  requires transform(multiset{a1}, multiset{b1, b2})
  ensures b1' == b1 && b2' == b2

  method {:axiom} transform_2_2(
      linear a1: R,
      linear a2: R,
      ghost b1: R,
      ghost b2: R)
  returns (linear b1': R, linear b2': R)
  requires transform(multiset{a1, a2}, multiset{b1, b2})
  ensures b1' == b1 && b2' == b2

  // User needs to fill these in:

  lemma InitImpliesInv(s: multiset<R>)
  requires Init(s)
  ensures Inv(s)

  predicate Next(s: multiset<R>, s': multiset<R>)
  {
    exists a, b, c ::
      s == a + c && s' == b + c && transform(a, b)
  }

  lemma NextPreservesInv(s: multiset<R>, s': multiset<R>)
  requires Init(s)
  requires Next(s, s')
  ensures Inv(s')
}
