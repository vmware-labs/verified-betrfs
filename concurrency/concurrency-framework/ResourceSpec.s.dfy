// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

abstract module ResourceSpec {
  import opened LinearSequence

  type R(==, !new) // TODO user can't construct/destruct the R?

  predicate Init(s: multiset<R>)
  predicate Transform(readonly_set: set<R>, a: multiset<R>, b: multiset<R>)

  predicate Inv(s: multiset<R>)

  ghost method {:extern} resources_obey_inv(shared objects: lseq<R>)
  returns (t: multiset<R>)
  ensures (forall a in objects.as_set() :: a in t)
  ensures Inv(t)

  ghost method {:extern} do_transform(
      shared readonly_objects: lseq<R>,
      linear objects_in: lseq<R>,
      ghost expected_objects_out: multiset<R>)
  returns (linear objects_out: lseq<R>)
  requires Transform(readonly_objects.as_set(), objects_in.as_multiset(), expected_objects_out)
  ensures objects_out.as_multiset() == expected_objects_out

  // Refining module (.i) needs to prove these properties
  // in order to reap the benefit from the meta-properties above.

  lemma InitImpliesInv(s: multiset<R>)
  requires Init(s)
  ensures Inv(s)

  predicate Next(s: multiset<R>, s': multiset<R>)
  {
    exists readonly_set: set<R>, a: multiset<R>, a': multiset<R>, rest: multiset<R> ::
      && s == a + rest
      && s' == a' + rest
      && Transform(readonly_set, a, a')
      && (forall a | a in readonly_set :: a in rest)
  }

  lemma NextPreservesInv(s: multiset<R>, s': multiset<R>)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
}
