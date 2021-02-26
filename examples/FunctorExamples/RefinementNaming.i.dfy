
abstract module E {
  type R
}

abstract module G refines E {
  predicate foo(r:R) { false }
}
