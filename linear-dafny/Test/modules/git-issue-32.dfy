// RUN: %dafny /compile:0 /titrace "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module TotalOrder {
  type V

  predicate le(a: V, b: V)

  lemma le_self(a: V)
  ensures le(a, a)

  lemma le_transitive(a: V, b: V, c: V)
  ensures le(a, b) && le(b, c) ==> le(a, c)
}

abstract module TotalOrderImpl(to: TotalOrder) {
  method compute_le(x: to.V, y: to.V)
  returns (b: bool)
  ensures b == to.le(x, y)
}

module IntTotalOrder refines TotalOrder {
  type V = int
  predicate le(a: V, b: V) { a <= b }
  lemma le_self(a: V) { }
  lemma le_transitive(a: V, b: V, c: V) { }
}

module BoolTotalOrder refines TotalOrder {
  type V = bool
  predicate le(a: V, b: V) { !a || b }
  lemma le_self(a: V) { }
  lemma le_transitive(a: V, b: V, c: V) { }
}

module X {
  import ZZZ = IntTotalOrder
  import BoolTotalOrder

  predicate f(x: ZZZ.V) {
    BoolTotalOrder.le(x, x)
  }
}
