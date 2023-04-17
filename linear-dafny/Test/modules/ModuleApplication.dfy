// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ABase {
    type Key
}

module InnocentA refines ABase {
    type Key = int
}

module SinisterA refines ABase {
    type Key = bool
}

abstract module P(A: ABase) {
}

abstract module MissingParameter {
    import P    // Fails with: P expects 1 arguments
}

abstract module B_good {
    import P1 = P(InnocentA)
    import P2 = P(InnocentA)
    lemma foo(a: P1.A.Key, b: P2.A.Key)
        ensures a == b  // succeeds, as it should
    { }
}

abstract module B_bad_compare_to_abstract {
    module Q refines ABase { }
    import P1 = P(InnocentA)
    lemma foo(a: Q.Key, b: P1.A.Key)
        ensures a == b // Fails with: not-comparable types: Q.Key, P1.A.Key
    { }
}

abstract module B_bad {
    import P1 = P(InnocentA)
    import P2 = P(SinisterA)
    lemma foo(a: P1.A.Key, b: P2.A.Key)
        ensures a == b // Fails with: mismatched types: P1.A.Key, P2.A.Key
    { }
}

