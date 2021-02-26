module A {
    type T // UserDataType
}
module A' refines A {
    type T = int    // TypeSynonym
}
module E(ea: A) {
  predicate f1(x:ea.T) { false }
}
module F {
    import Aalias = A
    import EA' = E(A')
        // 1. construct a ModuleDefinition right here at the point of Application -- and ask the Resolver to resolve it?
        // 2. You've already done resolution for E; do some translation of the type resolution for E(A')
    predicate f2(x:EA'.ea.T) ensures false {
        x < 7
    }
}

module G(ga: A) refines E(ga) {
}
module H(ha: A) refines G(ha) {
  import U=ea
  import V=G(ha).ea
  import W=E(ha).ea
  predicate f3(x:U.T) ensures false { false }
}
