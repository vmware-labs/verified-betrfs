// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

abstract module StateMachineRefinement(
  _v1: Ifc, // L.Ifc == H.Ifc
  L: StateMachine(_v1),
  H: StateMachine(_v1))
{
  // ...
}


module Betree(
    _v1: ValueType, // M.V
    K: TotalOrder,
    M: MessageType(_v1)
)
  refines StateMachine(MapIfc(K, _v1))
{
  import V = M.V
    // M.V = MessageType(_v1).V
    //     = _v1
}

/*
module Betree_Refines_Map(K: TotalOrder, V: ValueType)
  refines StateMachineRefinement(
    Betree(K, BasicMessage(V)),
    MapSpec(K, V)
  )

We need to check for well-formedness of this module expression

StateMachineRefinement(
   Betree(K, BasicMessage(V)),
   MapSpec(K, V))

To test for equality, we expand each module
to the canonical forms. (A canonical form has no periods.)

   Betree(K, BasicMessage(V)).Ifc
-> StateMachine(MapIfc(K, BasicMessage(V).V)).Ifc   // from refines relation
-> MapIfc(K, BasicMessage(V).V)                     // Ifc is first param of StateMachine
-> MapIfc(K, V)                                     // V is the first param of BasicMessage

   MapSpec(K, V).Ifc
-> StateMachine(MapIfc(K, V)).Ifc                   // from refines relation
-> MapIfc(K, V)                                     // Ifc is the first param of StateMachine

The module "desugars" to
*/

module Betree_Refines_Map(K: TotalOrder, V: ValueType)
  refines StateMachineRefinement(
    _v = MapIfc(K, V),
    Betree(K, BasicMessage(V)),
    MapSpec(K, V)
  )

/*
module GraphStateMachine(Ops: GraphOps)
  refines StateMachine(Ops.Ifc)
{
  // ...
}
*/

module GraphStateMachine(_v1: Ifc, _v2: Graph, Ops: GraphOps(_v1, _v2))
  refines StateMachine(_v1)
{
  // ...
}

/*
module PivotBetreeGraph(K: KeyType, M: MessageType)
*/

module PivotBetreeGraph(_v: ValueType, K: KeyType, M: MessageType(_v1))

/*
module PivotBetreeGraphOps(K: KeyType, M: MessageType)
    refines GraphOps(MapIfc(K, V), PivotBetreeGraph(K, M))

Need to do argument inference on
  PivotBetreeGraph(K, M) 
We get _v = M.V
*/

module PivotBetreeGraphOps(_v: ValueType, K: KeyType, M: MessageType(_v))
    refines GraphOps(MapIfc(K, V), PivotBetreeGraph(M.V, K, M))

/*
module PivotBetree_Refines_Betree(K: TotalOrder, M: MessageType)
  refines StateMachineRefinement(PivotBetree(K, M), Betree(K, M))

   PivotBetree(K, M).Ifc
-> GraphStateMachine(PivotBetreeGraphOps(M.V, K, M)).Ifc
-> StateMachine(PivotBetreeGraphOps(M.V, K, M).Ifc).Ifc
-> StateMachine(GraphOps(MapIfc(K, M.V), PivotBetreeGraph(M.V, K, M)).Ifc).Ifc
-> StateMachine(MapIfc(K, M.V), PivotBetreeGraph(M.V, K, M)).Ifc
-> MapIfc(K, M.V)

   Betree(M.V, K, M).Ifc
-> StateMachine(MapIfc(K, M.V)).Ifc
-> MapIfc(K, M.V)
*/

module PivotBetree_Refines_Betree(_v: ValueType, K: TotalOrder, M: MessageType(_v1))
  refines StateMachineRefinement(MapIfc(K, M.V), PivotBetree(K, M), Betree(K, M))

/*

module ComposeRefinements(
    Ref1: StateMachineRefinement,
    Ref2: StateMachineRefinement)
  refines StateMachineRefinement(Ref1.L, Ref2.H)
  requires Ref1.H == Ref2.L
{
  import A = Ref1.L
  import B = Ref1.H
  import C = Ref2.H
}

first add in missing params:

_v1: Ifc,
_v2: StateMachine(_v1),
_v3: StateMachine(_v1),
_v4: Ifc,
_v5: StateMachine(_v4),
_v6: StateMachine(_v4),
Ref1: StateMachineRefinement(_v1, _v2, _v3)
Ref2: StateMachineRefinement(_v4, _v5, _v6)

from the constraints,
  requires Ref1.H == Ref2.L
we get _v3 = _v5.

That in turn gives StateMachine(_v1) = StateMachine(_v4)
(Note that if those terms didn't already unify, then one would need to refine the other)
so _v1 = _v4. This all collapses to (with some renaming for clarity)
*/

_vIfc: Ifc,
_va: StateMachine(_vIfc),
_vb: StateMachine(_vIfc),
_vc: StateMachine(_vIfc),
Ref1: StateMachineRefinement(_vIfc, _va, _vb)
Ref2: StateMachineRefinement(_vIfc, _vb, _vc)

module ComposeRefinements(
  _vIfc: Ifc,
  _va: StateMachine(_vIfc),
  _vb: StateMachine(_vIfc),
  _vc: StateMachine(_vIfc),
  Ref1: StateMachineRefinement(_vIfc, _va, _vb)
  Ref2: StateMachineRefinement(_vIfc, _vb, _vc)
)
  refines StateMachineRefinement(_va, _vb)
{
  import A = Ref1.L
  // Ref1.L -> StateMachineRefinement(_vIfc, _va, _vb).L -> _va

  import B = Ref1.H
  // Ref1.H -> StateMachineRefinement(_vIfc, _va, _vb).H -> _vb

  import B' = Ref2.L
  // Ref2.L -> StateMachineRefinement(_vIfc, _vb, _vc).L -> _vb
  // Note that Ref1.H and Ref2.L reduce to the same canonical name

  import C = Ref2.H
  // Ref2.H -> StateMachineRefinement(_vIfc, _vb, _vc).H -> _vc
}

/*
import PivotBetree_Refines_Map =
  ComposeRefinements(
    PivotBetree_Refines_Betree(K, BasicMessage(V)),
    Betree_Refines_Map(K, V))

Need to resolve:

PivotBetree_Refines_Betree(BasicMessage(V).V, K, BasicMessage(V)).Ifc -> MapIfc(K, V)

PivotBetree_Refines_Betree(BasicMessage(V).V, K, BasicMessage(V)).L ->
  GraphStateMachine(PivotBetreeGraphOps(V, K, BasicMessage(M)))

PivotBetree_Refines_Betree(BasicMessage(V).V, K, BasicMessage(V)).H ->
  Betree(V, K, BasicMessage(V))

Betree_Refines_Map(K, V).Ifc -> MapIfc(K, V)

Betree_Refines_Map(K, V).L ->
  Betree(V, K, BasicMessage(V))

Betree_Refines_Map(K, V).H ->
  MapSpec(K, V)

*/

import PivotBetree_Refines_Map =
  ComposeRefinements(
    MapIfc(K, V)
    GraphStateMachine(PivotBetreeGraphOps(V, K, BasicMessage(M)))
    Betree(V, K, BasicMessage(V))
    MapSpec(K, V)
    PivotBetree_Refines_Betree(V, K, V),
    Betree_Refines_Map(K, V))
