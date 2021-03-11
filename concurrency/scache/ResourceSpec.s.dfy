// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

abstract module ResourceSpec {
  type R(==, !new)
  predicate Init(s: multiset<R>)
  predicate transform(a: multiset<R>, b: multiset<R>)

  predicate Inv(s: multiset<R>)

  // TODO create one general axiom (e.g., taking an lseq)

  method {:axiom} is_allowed_1(linear a: R)
  returns (t: multiset<R>)
  ensures Inv(multiset{a} + t)

  method {:axiom} is_allowed_2(linear a: R, linear b: R)
  returns (t: multiset<R>)
  ensures Inv(multiset{a, b} + t)

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
