abstract module A {
  datatype T = T
}

module B refines A {
}

abstract module C(a: A) {
}

abstract module D(a: A) refines C(a) {
}

// { D -> PM{D's literals + a -> AM(A), ptr to C(a)'s AM-mod-syms }

abstract module E(c: C) {
    type R
}

// { E -> PM(

abstract module F(e: E) {
}

abstract module G(a: A) refines E(C(a)) {
    import X = a
    import Y = c.a
    import Z = E(C(a)).c.a
    lemma types_eq(x:X.T, y:Y.T, z:Z.T, r:R)
    requires x == y == z
    {}
}

abstract module H(a: A) refines F(G(a)) {
  import X = a
  // > I think "import e.c.a" is impossible ...
  // It's fine now that we have paved the module parts of the Resolver
  // and replaced it with the ModuleResolver.
  import U = e.c.a
  import Y = G(a).a
  import Z = C(a).a
  import W = G(a).c.a
  import V = F(G(a)).e.c.a

  lemma types_eq(x: X.T, y: Y.T, z: Z.T, w: W.T, v: V.T)
  requires /*x == y == */ z == w == v
  {
  }
}

///////////////////////////////////////////////////////////////////////////
//
//module Key {
//    type KeyType
//}
//
//module IntKey refines Key {
//    type KeyType = int
//}
//
//module A(km:Key) {
////    type T = List<km.KeyType>
//    datatype T = Foo(k : km.KeyType)
//}
//
//module B(km:Key) {
//    import A = A(km)
//    predicate empty(thing: A.T) { |thing| == 0 }
//}
//
//module C(km:Key) {
//    import B = B(km)
//    predicate fuzzy(thing: B.A.T) { B.empty(thing) }
//    // AM: thing has type A.Foo<UserDefinedType>
//}
//
//module C2 {  // should name-mangle this C_O_module_DD_DIntKey_C
//    import km = IntKey
//    import B = B(km)
//    predicate fuzzy(thing: B.A.T) { B.empty(thing) }
//    // AM: thing has type A.Foo<UserDefinedType>
//}
//
//
//module D {
//    import C = C(IntKey)
//    // thing has type List<int>
//    // In this AM, this is the first time A(IntKey).T has been instantiated;
//    // it's a new datatype (with k:int) that's not been seen before.
//    // AM: thing has type A.Foo<UserDefinedType>
//}
