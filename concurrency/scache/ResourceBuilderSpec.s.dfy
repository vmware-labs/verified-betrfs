// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

abstract module ResourceBuilderSpec {
  type Q(==, !new)
  type V(==, !new)

  linear datatype R =
    | Exc(linear v: V)
    | Const(/*readonly*/ linear v: V)
    | Internal(q: Q)

  datatype Variables = Variables(m: multiset<R>, saved: multiset<V>)

  predicate Init(s: Variables)
  predicate transform(a: multiset<R>, b: multiset<R>)

  predicate NewExc(s: Variables, s': Variables)
  {
    exists v ::
      && s'.saved == s.saved + multiset{v}
      && s'.m == s.m + multiset{Exc(v)}
  }

  predicate InternalStep(s: Variables, s': Variables)
  {
    && s'.saved == s.saved
    && (exists a, b, c ::
      s.m == a + c && s'.m == b + c && transform(a, b))
  }

  predicate Next(s: Variables, s': Variables)
  {
    || NewExc(s, s')
    || NewExc(s', s)
    || InternalStep(s, s')
  }

  predicate Inv(s: Variables)

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)

  lemma NextPreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')

  lemma InvWorksConst(s: Variables, v: V)
  requires Inv(s)
  requires Const(v) in s.m
  ensures v in s.saved

  lemma InvWorksExc(s: Variables, v: V)
  requires Inv(s)
  requires Exc(v) in s.m
  ensures v in s.saved
}
