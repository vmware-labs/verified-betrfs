// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

module Multisets {
  function Count<A>(fn: A ~> bool, s: multiset<A>) : nat

  function Sum<A>(fn: A ~> int, s: multiset<A>) : int

  lemma Count_ge_1<A>(fn: A -> bool, s: multiset<A>, v: A)
  requires fn(v)
  requires v in s
  ensures Count(fn, s) >= 1

  lemma get_nonzero_elem<A>(fn: A -> int, s: multiset<A>)
  returns (v: A)
  requires Sum(fn, s) != 0
  ensures v in s
  ensures fn(v) != 0

  lemma get_true_elem<A>(fn: A -> bool, s: multiset<A>)
  returns (v: A)
  requires Count(fn, s) != 0
  ensures v in s
  ensures fn(v)

  lemma SumAdditive<A>(fn: A -> int, s: multiset<A>, t: multiset<A>)
  ensures Sum(fn, s) + Sum(fn, t) == Sum(fn, s + t)

  lemma SumMultiset1<A>(fn: A -> int, v: A)
  ensures Sum(fn, multiset{v}) == fn(v)

  lemma CountAdditive<A>(fn: A -> bool, s: multiset<A>, t: multiset<A>)
  ensures Count(fn, s) + Count(fn, t) == Count(fn, s + t)

  lemma CountMultiset1<A>(fn: A -> bool, v: A)
  ensures fn(v) ==> Count(fn, multiset{v}) == 1
  ensures !fn(v) ==> Count(fn, multiset{v}) == 0
}
