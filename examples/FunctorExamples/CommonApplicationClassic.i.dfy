module ABase {
    type Key
}

module InnocentA refines ABase {
    type Key = int
}

module SinisterA refines ABase {
    type Key = bool
}

abstract module P {
    import A : ABase
}

abstract module B {
    module P1def refines P { import A = InnocentA }
    import P1 = P1def
    module P2def refines P { import A = SinisterA }
    import P2 = P2def
    lemma foo(a: P1.A.Key, b: P2.A.Key)
        ensures a == b
    { }
}
