// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ABase {
  type Key
}

// Use an element of a formal parameter
// Morally equivalent to P_normal above
abstract module P(A: ABase) {
  method Test(a:A.Key)
}

// Try passing module of the wrong type to a functor
abstract module NoBase {
}

abstract module BadApplication {
  import ShouldFail = P(NoBase)
}

module InnocentA refines ABase {
    type Key = int
}


abstract module MissingParameter {
  import P    // Fails with: P expects 1 arguments
}

abstract module B_bad_compare_to_abstract {
    module Q refines ABase { }
    import P1 = P(InnocentA)
    lemma foo(a: Q.Key, b: P1.A.Key)
        requires a == b // Fails with: not-comparable types: Q.Key, P1.A.Key
    { }
}

module SinisterA refines ABase {
    type Key = bool
}

abstract module B_bad {
    import P1 = P(InnocentA)
    import P2 = P(SinisterA)
    lemma foo(a: P1.A.Key, b: P2.A.Key)
        requires a == b // Fails with: mismatched types: P1.A.Key, P2.A.Key
    { }
}
