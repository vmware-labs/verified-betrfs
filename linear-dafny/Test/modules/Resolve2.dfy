// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module TotalOrder {
  type K(==,!new)
  predicate lt(a: K, b: K)
}

module IntTotalOrder refines TotalOrder {
  type K = int

  predicate lt(a: K, b: K)
  {
    a < b
  }
}

abstract module SortUtil(T: TotalOrder) {
  predicate IsStrictlySorted(s: seq<T.K>)
  {
    forall i, j | 0 <= i < j < |s| :: T.lt(s[i], s[j])
  }
}

abstract module SortMethodUtil(T: TotalOrder) {
  import S = SortUtil(T)

  method m(x: seq<T.K>) returns (y: seq<T.K>)
    ensures S.IsStrictlySorted(y)
  {
    assume false;
  }
}

abstract module Stuff {
  import T = IntTotalOrder
  import W = SortMethodUtil(IntTotalOrder).S.T

  lemma same_types(x: T.K, y: W.K)
  requires x == y == 0
  {
  }
}

abstract module ParameterizedStuff(T: TotalOrder) {
  import W = SortMethodUtil(T).S.T

  lemma same_types(x: T.K, y: W.K)
  requires x == y
  {
  }
}
