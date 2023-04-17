// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module InputOutputIfc {
}

module AsyncIfc(Ifc: InputOutputIfc) refines Ifc {
}

//
// Original Repro
//
//  abstract module Ifc {
//    type Op
//  }
//
//  abstract module StateMachine(Ifc: Ifc) {
//    type Variables
//    predicate Init(s: Variables)
//    predicate Next(s: Variables, s': Variables, op: Ifc.Op)
//  }
//
//  // Async state machines
//
//  abstract module InputOutputIfc refines Ifc {
//    type Input
//    type Output
//
//    datatype Op = Op(input: Input, output: Output)
//  }
//
//  module AsyncIfc(Ifc: InputOutputIfc) refines Ifc {
//  }
