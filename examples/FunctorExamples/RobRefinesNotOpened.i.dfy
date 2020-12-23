abstract module A {
  type X
}

abstract module B refines A {
  predicate foo(x: X) {
    true
  }
}

abstract module C(D:A) {
  predicate foo(x: D.X) {
    true
  }
}
