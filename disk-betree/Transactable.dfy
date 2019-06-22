include "../lib/sequences.dfy"
include "Graph.dfy"

abstract module Transactable {
  import opened Sequences

  import G : Graph

  type Reference = G.Reference
  type Node = G.Node

  type Constants(!new)
  type Variables(!new)
  type Op = G.Op
  type ReadOp = G.ReadOp

  predicate ReadStep(k: Constants, s: Variables, op: ReadOp)
  predicate OpStep(k: Constants, s: Variables, s': Variables, op: Op)

  predicate Reads(k: Constants, s: Variables, ops: seq<ReadOp>)
  // TODO prove these:
  ensures |ops| == 1 ==> ReadStep(k, s, ops[0])
  ensures |ops| == 2 ==> ReadStep(k, s, ops[0]) && ReadStep(k, s, ops[1])
  ensures |ops| == 3 ==> ReadStep(k, s, ops[0]) && ReadStep(k, s, ops[1]) && ReadStep(k, s, ops[2])
  {
    forall op :: op in ops ==> ReadStep(k, s, op)
  }

  predicate IsStatePath(k: Constants, s: Variables, s': Variables, ops: seq<Op>, path: seq<Variables>)
  {
    && |path| == |ops| + 1
    && path[0] == s
    && Last(path) == s'
    && (forall i :: 0 <= i < |ops| ==> OpStep(k, path[i], path[i+1], ops[i]))
  }

  lemma Transaction1Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 1
  ) ==>
      && OpStep(k, s, s', ops[0])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        && |ops| == 1)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      assert OpStep(k, s, s', ops[0]);
    }
  }


  lemma Transaction2Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 2
  ) ==>
      exists sint ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, s', ops[1])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        &&| ops| == 2)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      var sint := path[1];
      assert OpStep(k, s, sint, ops[0]);
      assert OpStep(k, sint, s', ops[1]);
    }
  }

  lemma Transaction3Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 3
  ) ==>
      exists sint, sint' ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, sint', ops[1])
      && OpStep(k, sint', s', ops[2])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        && |ops| == 3)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      var sint := path[1];
      var sint' := path[2];
      assert OpStep(k, s, sint, ops[0]);
      assert OpStep(k, sint, sint', ops[1]);
      assert OpStep(k, sint', s', ops[2]);
    }
  }
  
  predicate OpTransaction(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
    // These postconditions help automation a lot.
    ensures OpTransaction(k, s, s', ops) && |ops| == 1 ==>
      && OpStep(k, s, s', ops[0])
    ensures OpTransaction(k, s, s', ops) && |ops| == 2 ==> exists sint ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, s', ops[1])
    ensures OpTransaction(k, s, s', ops) && |ops| == 3 ==> exists sint, sint' ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, sint', ops[1])
      && OpStep(k, sint', s', ops[2])
  {
    Transaction1Steps(k, s, s', ops);
    Transaction2Steps(k, s, s', ops);
    Transaction3Steps(k, s, s', ops);
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
  }

  // Helper lemmas
  lemma OpTransactionAugment(k: Constants, s: Variables, s': Variables, s'': Variables, ops: seq<Op>, op: Op)
  requires OpTransaction(k, s, s', ops)
  requires OpStep(k, s', s'', op)
  ensures OpTransaction(k, s, s'', ops + [op])
  {
    var path :| IsStatePath(k, s, s', ops, path);
    var path1 := path + [s''];
    assert IsStatePath(k, s, s'', ops + [op], path1);
  }
}
