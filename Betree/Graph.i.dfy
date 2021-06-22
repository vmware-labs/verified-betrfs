// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Sequences.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
//
// An abstract graph that tracks dependencies.
// It is an interface implemented by BetreeGraph (and the refined
// PivotBetreeGraph): trees whose dependencies are child pointers that
// reference other nodes.
// It is used by the BlockInterface to identify which blocks can be
// garbage-collected because they're unreachable from the graph roots.
//

module ReferenceType {
  import NativeTypes

  type Reference(==,!new) = NativeTypes.uint64
  function method Root() : Reference { 0 }

  function method toRef(i: NativeTypes.uint64) : Reference { i }
  function method toUint64(i: Reference) : NativeTypes.uint64 { i }

  export S provides Reference, Root, toRef, toUint64, NativeTypes
  export extends S
  export Internal reveals *
}

abstract module Graph {
  import opened Sequences
  import ReferenceType

  // Abstract features
  type Reference = ReferenceType.Reference
  type Node(!new)
  function method Root() : Reference { ReferenceType.Root() }
  function Successors(node: Node) : iset<Reference>

  type Graph = imap<Reference, Node>
  type Path = seq<Reference>

  // TODO Transactable is a more natural place for this
  datatype Op =
    | AllocOp(ref: Reference, node: Node)
    | WriteOp(ref: Reference, node: Node)

  datatype ReadOp =
    | ReadOp(ref: Reference, node: Node)

  //
  // Helpers for proving graph-related facts about your data structure.
  //

  predicate IsClosed(g: Graph) {
    forall ref :: ref in g ==> Successors(g[ref]) <= g.Keys
  }

  predicate IsPath(g: Graph, path: Path) {
    forall i :: 0 <= i < |path|-1 ==> path[i] in g && path[i+1] in Successors(g[path[i]])
  }

  predicate IsCycle(g: Graph, path: Path) {
    && IsPath(g, path)
    && 0 < |path|
    && Last(path) in g
    && path[0] in Successors(g[Last(path)])
  }

  lemma CycleRotation(g: Graph, path: Path, i: nat)
    requires IsCycle(g, path)
    requires 0 <= i <= |path|
    ensures IsCycle(g, path[i..] + path[..i]);
  {
    var path' := path[i..] + path[..i];
    forall j | 0 <= j < |path'| - 1
      ensures path'[j] in g && path'[j+1] in Successors(g[path'[j]])
    {
      if j < |path[i..]| - 1 {
      } else if j == |path[i..]| - 1 {
      } else {
      }
    }
  }

  predicate IsSimple(g: Graph, path: Path) {
    && IsPath(g, path)
    && (forall i, j :: 0 <= i < |path| && 0 <= j < |path| && i != j ==> path[i] != path[j])
  }

  predicate IsAcyclic(g: Graph) {
    forall path :: IsPath(g, path) ==> !IsCycle(g, path)
  }

  lemma AcyclicGraphImpliesSimplePath(g: Graph, path: Path)
    requires IsAcyclic(g)
    requires IsPath(g, path)
    ensures IsSimple(g, path)
  {
    if !IsSimple(g, path) {
      var i, j :| 0 <= i < |path| && 0 <= j < |path| && i < j && path[i] == path[j];
      var cycle := path[i..j];
      assert IsCycle(g, cycle);
    }
  }

  predicate IsPathFromTo(g: Graph, path: Path, start: Reference, end: Reference)
  {
    IsPath(g, path) && 1 < |path| && path[0] == start && Last(path) == end
  }

  function ReachableReferences(g: Graph, p: Reference) : iset<Reference>
  {
    iset path |
    && IsPath(g, path)
    && 1 < |path|
    && path[0] == p
    :: Last(path)
  }

  predicate NewPath(g: Graph, g': Graph, p: Reference, path: Path) {
    && IsPath(g', path)
    && 1 < |path|
    && path[0] == p
    && (forall i :: 0 < i < |path| - 1 ==> path[i] in g'.Keys - g.Keys)
    && Last(path) in g
  }

  function NewlyReachableReferences(g: Graph, g': Graph, p: Reference) : iset<Reference>
  {
    iset path | NewPath(g, g', p, path) :: Last(path)
  }

  predicate EditIsLocal(g: Graph, g': Graph, p: Reference)
  {
    && (forall ref :: ref in g.Keys * g'.Keys - iset{p} ==> Successors(g[ref]) == Successors(g'[ref]))
    && NewlyReachableReferences(g, g', p) <= ReachableReferences(g, p)
  }

  predicate NewNodesAreCycleFree(g: Graph, g': Graph)
  {
    forall path ::
      && IsPath(g', path)
      && (forall i :: 0 <= i < |path| ==> path[i] in g'.Keys - g.Keys)
      ==> !IsCycle(g', path)
  }

  function FirstInGraph(path: Path, g: Graph) : (pos: int)
    requires exists i :: 0 <= i < |path| && path[i] in g
    ensures 0 <= pos < |path|
    ensures path[pos] in g
    ensures forall i :: 0 <= i < pos ==> path[i] !in g
  {
    if path[0] in g then 0
    else 1 + FirstInGraph(path[1..], g)
  }

  lemma UndoLocalEdit(g: Graph, g': Graph, p: Reference, path: Path) returns (result: Path)
    requires IsClosed(g)
    requires 1 < |path|
    requires path[0] in g.Keys
    requires Last(path) in g.Keys
    requires EditIsLocal(g, g', p)
    requires IsPath(g', path)
    ensures IsPathFromTo(g, result, path[0], Last(path))
  {
    if path[0] == p {
      var len := 1 + FirstInGraph(path[1..], g);
      var wit := path[..len+1];
      assert NewPath(g, g', p, wit);
      assert Last(wit) in NewlyReachableReferences(g, g', p);
      var replacement :| IsPathFromTo(g, replacement, path[0], Last(wit));
      if len < |path| - 1 {
        var sub := UndoLocalEdit(g, g', p, path[len..]);
        return DropLast(replacement) + sub;
      } else {
        return replacement;
      }
    } else if |path| == 2 {
      return path;
    } else {
      var sub := UndoLocalEdit(g, g', p, path[1..]);
      return path[..1] + sub;
    }
  }

  lemma CycleVisitsG(g: Graph, g': Graph, cycle: Path) returns (i: nat)
    requires IsClosed(g)
    requires NewNodesAreCycleFree(g, g')
    requires IsCycle(g', cycle)
    ensures 0 <= i < |cycle|
    ensures cycle[i] in g
  {
    var j :| 0 <= j < |cycle| && cycle[j] in g;
    return j;
  }

  lemma {:timeLimitMultiplier 4} {:fuel Successors,0} LocalEditPreservesAcyclic(g: Graph, g': Graph, p: Reference)
    requires IsClosed(g)
    requires IsAcyclic(g)
    requires EditIsLocal(g, g', p)
    requires NewNodesAreCycleFree(g, g')
    ensures IsAcyclic(g')
  {
    if cycle :| IsCycle(g', cycle) {
      var i := CycleVisitsG(g, g', cycle);
      CycleRotation(g', cycle, i);
      var rcycle := cycle[i..] + cycle[..i];
      var path := rcycle + [rcycle[0]];
      assert Last(path) in g.Keys;
      var rpath := UndoLocalEdit(g, g', p, path);
      assert IsCycle(g, DropLast(rpath));
    }
  }

  lemma UnallocPreservesAcyclic(g: Graph, g': Graph)
    requires IsClosed(g)
    requires IsAcyclic(g)
    requires forall node | node in g' :: node in g && g[node] == g'[node]
    ensures IsAcyclic(g')
  {
    forall path | IsPath(g', path)
    ensures !IsCycle(g', path)
    {
      assert IsPath(g, path);
      assert !IsCycle(g, path);
    }
  }
}
