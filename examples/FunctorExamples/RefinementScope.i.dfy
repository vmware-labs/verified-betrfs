module A {
    type T // UserDataType
}
abstract module E(ea:A) {
//abstract module E { import ea : A
  predicate f1(x:ea.T) { false }
}
abstract module G(ga:A) refines E(ga) { }
//abstract module G refines E { }
