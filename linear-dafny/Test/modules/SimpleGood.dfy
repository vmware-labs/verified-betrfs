// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ABase {
  type Key
}

//abstract module P_normal {
//  import A : ABase
//
//  method Test(a:A.Key)
//}

// Use an element of a formal parameter
// Morally equivalent to P_normal above
abstract module P(A: ABase) {
  method Test(a:A.Key)
}

// Try simple functor application
abstract module Apply {
  import OutputBase = P(ABase)

  method More(a:OutputBase.A.Key) {
    OutputBase.Test(a);
  }
}

// Make sure functors behave applicatively
abstract module Apply2 {
  import Output0 = P(ABase)
  import Output1 = P(ABase)

  method More(a:Output0.A.Key, b:Output1.A.Key)
    requires a == b
  {
    Output1.Test(a);
  }
}

// Try passing a refinement to a functor
abstract module B refines ABase {
  method BTest()
}

abstract module ApplyRefinement {
  import OutputRefined = P(B)

  method UseB() {
    OutputRefined.A.BTest();
  }

  method KeyTest(b:OutputRefined.A.Key)
  {
    OutputRefined.Test(b);
  }
}

// Try refining the result of a functor application
abstract module FunctorAppRefiner refines P(ABase) {
  method MoreTest(x:A.Key) {
    Test(x);
  }
}

//// Try refining a functor application applied to our formal argument
//module FunctorAppParamRefiner(abase: ABase) refines P(abase) {
//  // Refer to the formal name of our refinement functor
//  import X = A
//}
//
//// Dafny says this isn't okay
//module NormalRefinement refines P_normal {
//  import A
//  import X = A
//}

// Try a functor that itself applies a functor
abstract module AnotherFunctor(AB: ABase) {
  import P1 = P(AB)
}

module AInt refines ABase {
  type Key = int
}

abstract module DeepApplication {
  import AF = AnotherFunctor(AInt)

  method Test(x:int, y:AF.P1.A.Key)
    requires x == y

}

//  Create a functor that takes an argument that is itself a functor application...
abstract module ComplexFormal(p: P(ABase)) {

}

abstract module C refines ABase {
  method CTest()
}

// ... and then try to instantiate it with the functor applied to a refinement
abstract module InstantiateComplex {
  import CF = ComplexFormal(P(C))
}

// Try to instantiate a functor formal with an actual that refines that functor
abstract module ComplexFormalDependent(a:ABase, p: P(a)) { }

abstract module FunctorAppRefiner2(a:ABase) refines P(a) { }

abstract module FunctorRefinementInstantiation {
  import Test = ComplexFormalDependent(ABase, FunctorAppRefiner2(ABase))
}

// Make sure we can call methods from our parent when refining
abstract module Q(A: ABase) {
  predicate Valid(a:A.Key)

  method Test(a:A.Key)
    requires Valid(a)
}

abstract module FunctorAppRefiner3(a:ABase) refines Q(a) {
  method MyTest(a:A.Key)
    requires Valid(a)
  {
    Test(a);
  }
}

// Try refining a functor application that includes a method from the parent
abstract module T(A: ABase) {
  predicate Valid(a:A.Key)

  method Test(a:A.Key)
    requires Valid(a)

  method DoIt(a:A.Key)
    requires Valid(a)
}

abstract module FunctorAppRefiner4(someA:ABase) refines T(someA) {
  //method Test(a:someA.Key) // Fails
  method Test(a:A.Key)  // Succeeds when using parent name
  {
    DoIt(a);
  }
}

abstract module SameFunctorRefinmentWithArg(MyA:ABase, PA0:P(MyA), PA1:P(MyA)) refines P(MyA)
{
  method MyTest(a:A.Key) {
    assert 3 > 2;
    PA0.Test(a);
    PA1.Test(a);
  }
}

// Test abstract vs. concrete module rules

module Pconcrete(A: ABase) {
  method Test(a:A.Key)
}

module AIntAgain refines ABase {
  type Key = int
}

module AConsumer(a:ABase, b:Pconcrete(a)) {
  method MyTest(x:b.A.Key) {
    b.Test(x);
  }
}

module PconcreteRefiner refines AConsumer(AIntAgain, Pconcrete(AIntAgain)) {
  method Test(y:a.Key) {
    var x:int := y;
  }
}
