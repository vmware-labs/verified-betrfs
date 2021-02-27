// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

// TotalOrder (for, e.g., KeyType)

abstract module TotalOrder {
  // abstract module: these need to be filled in
  type K
  function lt(a: K, b: K)
  lemma is_transitive ...
}

module TotalOrderUtil(T: TotalOrder) {
  // useful utilities like IsStrictlySorted
  // this module doesn't depend on the definition
  // of lt, all its lemmas can be proven from
  // the abstract TotalOrder.
  // Therefore, TotalOrderUtil is *concrete*:
  // that is, it automatically becomes concrete when supplied
  // with a concrete T.
}

abstract module TotalOrderImpl(T: TotalOrder) {
  // For fast implementation of lt and so on.

  // This module is abstract. Even if someone picks out
  // a concrete T, they need to implement the compute_lt method.

  method compute_lt(a: T.K, b: T.K)
}

// State machines

abstract module Ifc {
  type TransitionLabel
}

abstract module StateMachine(ifc: Ifc) {
  type Variables
  predicate Next(s: Variables, s': Variables)
  // ...
}

abstract module StateMachineRefinement(ifc: Ifc, L: StateMachine(ifc), R: StateMachine(ifc)) {
  // ...
}

// MapSpec

abstract module ValueType {
  type Value
}

module MapIfc(K: TotalOrder, V: ValueType) {
  // concrete when K and V are concrete
  type TransitionLabel =
    | Query(k: K.K, v: V.V)
    | Insert(k: K.K, v: V.V)
    | ...
}

module MapSpec(K: TotalOrder, V: ValueType)
    refines StateMachine(MapIfc(K, V))
{
  // concrete when K and V are concrete
}

// MessageType

abstract module MessageType(V: ValueType) {
  type Delta // abstract

  datatype Message =
    | Define(value: V.Value)
    | Update(delta: Delta)

  // abstract lemmas here for
  // properties of Delta (e.g., associativity lemmas)
}

// Concretize MessageType into a BasicMessageType
// where the only delta is a no-op. Hence the only Messages
// are updates and no-ops.
// Still parameterized over V.
module BasicMessage(V: ValueType) refines MessageType(V) {
  datatype Delta = NoOp

  // ...
}

// B-epsilon tree
// Parameterized over key, value, and message type

module Betree(K: TotalOrder, V: ValueType, M: MessageType(V))
  refines StateMachine(MapIfc(K, V))
{
  // ...
}

module Betree_Refines_Map(K: TotalOrder, V: ValueType)
  refines StateMachineRefinement(
      MapIfc(K, V),
      Betree(K, V, BasicMessage(V)),
      MapSpec(K, V))

// PivotBetree

abstract module Graph {
  type Reference
  type Node
  function successors(n: Node) : set<Reference>
}

abstract module GraphOps(Ifc: Ifc, G: Graph) {
  // ...
}

module GraphStateMachine(Ifc: Ifc, G: Graph, Ops: GraphOps(Ifc, G))
  refines StateMachine(Ifc)
{
  // ...
}

module PivotBetreeGraph(K: KeyType, V: ValueType, M: MessageType(V)) refines Graph {
  type Reference = uint64
  type Node = Node(...)
  function successors(n: Node) : set<Reference> { ... }
}

module PivotBetreeGraphOps(K: KeyType, V: ValueType, M: MessageType(V))
    refines GraphOps(MapIfc(K, V), PivotBetreeGraph(K, V, M))
{
  // define split, query, insert, etc.
}

module PivotBetree(K: TotalOrder, V: ValueType, M: MessageType(V))
  = GraphStateMachine(MapIfc(K, V), PivotBetreeGraph(K, V, M), GraphOps(K, V, M))

module PivotBetree_Refines_Betree(K: TotalOrder, V: ValueType, M: MessageType(V))
  refines StateMachineRefinement(
      MapIfc(K, V),
      PivotBetree(K, V, M),
      Betree(K, V, M))
{
  import TotalOrderUtil(K) // this will probably be useful for the proof

  // ...
}

// Generic mechanism for composing two refinements

module ComposeRefinements(
    Ifc: Ifc,
    P: StateMachine(Ifc),
    Q: StateMachine(Ifc),
    R: StateMachine(Ifc),
    Ref1: StateMachineRefinement(Ifc, P, Q),
    Ref2: StateMachineRefinement(Ifc, Q, R))
  refines StateMachineRefinement(Ifc, P, R)
{
  // This module is concrete, proof of composition
  // is entirely self-contained and dependent only on
  // abstract properties of Ref1 and Ref2
}

// Now we can put it together:
import PivotBetree_Refines_Map =
  ComposeRefinements(
      MapIfc(K, V)
      PivotBetree(K, V, BasicMessage(ValueType)),
      Betree(K, V, BasicMessage(ValueType)),
      MapSpec(K, V),
      PivotBetree_Refines_Betree(K, V, BasicMessage(ValueType)),
      Betree_Refines_Map(K, V)
  )

// Define what it means to be CrashSafe

module CrashableIfc(InnerIfc: Ifc) refines Ifc
{
  type TransitionLable =
    | CrashOp
    | NormalOp(InnerIfc.TransitionLabel)
}

module CrashSafeMachine(Ifc: Ifc, sm: StateMachine(Ifc))
  refines StateMachine(CrashableIfc(Ifc))

// Define IOSystem

module Machine(Ifc: Ifc) {
}

module IOSystem(Ifc: Ifc, m: Machine(Ifc))
  refines StateMachine(CrashableIfc(Ifc))
{
  // ...
}

// Define a cache

module BlockCache(Ifc: Ifc, g: Graph, Ops: GraphOps(Ifc, G))
  refines Machine(Ifc)
{
  // ...
}

module BlockCacheRefinementThm(Ifc: Ifc, g: Graph, Ops: GraphOps(Ifc, G))
  refines StateMachineRefinement(
    CrashableIfc(Ifc),
    IOSystem(Ifc, BlockCache(Ifc, g, Ops)),
    CrashSafeMachine(GraphStateMachine(Ifc, g, Ops))
  )
{
  // proof here
}

// BlockCacheRefinementThm can now be instantiated

import AwesomeTheorem = BlockCacheRefinementThm(
  MapIfc(K, V),
  PivotBetreeGraph(K, V, M),
  PivotBetreeGraphOps(K, V, M))

// Suppose in our implementation, we have a bunch of
// nested modules from the top level: Impl
// imports A which imports B ...
// all parameterized over KeyType
//
// Impl(K) -> A(K) -> B(K) -> C(K) -> D(K) -> E(K) -> TotalOrderImpl(K)
//
// As mentioned above, TotalOrderImpl(K) is abstract, so this whole chain
// is abstract. What's the best way to instantiate this module?
//
// In this system, we could make TotalOrderImpl a concrete argument,
//
// module Impl(K: KeyType, KI: TotalOrderImpl(K))
//
// and pass KI down the entire module chain.
//
// Thus any module which depends (even indirectly) on TotalOrderImpl will
// need to declare this in their signature and pass it down to the child module.
// I don't think this is necessarily a bad thing.
