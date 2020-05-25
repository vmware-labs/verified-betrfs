include "../lib/Base/sequences.i.dfy"
include "../Betree/Graph.i.dfy"
//
// A Transactable is a state machine defined by atomically gluing together
// groups of a few step primitives. Each BetreeSpec operation performs
// an atomic sequence of cache updates, such as a block allocation
// followed by a write (which includes a reference to the allocated block).
//

// Note that these aren't disk transactions; we're not assuming anything
// atomic about the I/O subsystem. Transactable is a way of defining a
// complex in-memory atomic action by composing simpler primitives offered
// by an underlying module (the cache). This is (metatheoretically) safe with
// respect to crashes, because the effect of a crash (to reset the RAM) can't
// distinguish whether that reset occurs within or after a transaction.
// It's not safe with respect to CPU concurrency, which is okay because
// we don't yet expliot it.

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
  ensures Reads(k, s, ops) && 0 < |ops|  ==> ReadStep(k, s, ops[0])
  ensures Reads(k, s, ops) && 1 < |ops|  ==> ReadStep(k, s, ops[1])
  ensures Reads(k, s, ops) && 2 < |ops|  ==> ReadStep(k, s, ops[2])
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

  lemma Transaction0Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 0
  ) ==>
      && s == s'
  ensures s == s' ==> IsStatePath(k, s, s', [], [s])
  {
    if (
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        && |ops| == 0)
    {
      var path :| IsStatePath(k, s, s', ops, path);
    }
  }

  lemma Transaction1Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 1
  ) ==>
      && OpStep(k, s, s', ops[0])
  ensures |ops| == 1 && OpStep(k, s, s', ops[0]) ==> IsStatePath(k, s, s', ops, [s, s'])
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
  
  predicate {:opaque} OpTransaction(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
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
    ensures |ops| == 1 && OpStep(k, s, s', ops[0]) ==> OpTransaction(k, s, s', ops)
    ensures OpTransaction(k, s, s', ops) && |ops| == 0 ==> s == s'
    ensures |ops| == 0 && s == s' ==> OpTransaction(k, s, s', ops)
  {
    Transaction0Steps(k, s, s', ops);
    Transaction1Steps(k, s, s', ops);
    Transaction2Steps(k, s, s', ops);
    Transaction3Steps(k, s, s', ops);
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
  }

  // Helper lemmas
  // Dealing with paths and the IsStatePath existential is annoying.
  // Thus we make OpTransaction opaque and use its postconditions
  // as well as the below lemmas to make it easy to write inductive proofs
  // on transactions.

  lemma SplitTransaction(k: Constants, s: Variables, s': Variables, ops: seq<Op>) returns (ops1: seq<Op>, smid: Variables, ops2: seq<Op>)
  requires OpTransaction(k, s, s', ops)
  requires |ops| >= 2
  ensures OpTransaction(k, s, smid, ops1)
  ensures OpTransaction(k, smid, s', ops2)
  ensures ops1 + ops2 == ops
  ensures |ops1| < |ops|
  ensures |ops2| < |ops|
  {
    reveal_OpTransaction();
    var path: seq<Variables> :| IsStatePath(k, s, s', ops, path);
    ops1 := ops[..|ops|-1];
    ops2 := [ops[|ops|-1]];
    smid := path[|path| - 2];
    assert IsStatePath(k, s, smid, ops1, path[..|path|-1]);
    assert IsStatePath(k, smid, s', ops2, [smid, s']);
  }

  lemma JoinTransactions(k: Constants, s: Variables, smid: Variables, s': Variables, ops1: seq<Op>, ops2: seq<Op>)
  requires OpTransaction(k, s, smid, ops1)
  requires OpTransaction(k, smid, s', ops2)
  ensures OpTransaction(k, s, s', ops1 + ops2)
  {
    reveal_OpTransaction();
    var path1 :| IsStatePath(k, s, smid, ops1, path1);
    var path2 :| IsStatePath(k, smid, s', ops2, path2);
    var path := path1 + path2[1..];
    assert IsStatePath(k, s, s', ops1 + ops2, path);
  }

//~  lemma OpTransactionAugment(k: Constants, s: Variables, s': Variables, s'': Variables, ops: seq<Op>, op: Op)
//~  requires OpTransaction(k, s, s', ops)
//~  requires OpStep(k, s', s'', op)
//~  ensures OpTransaction(k, s, s'', ops + [op])
//~  {
//~    reveal_OpTransaction();
//~    var path :| IsStatePath(k, s, s', ops, path);
//~    var path1 := path + [s''];
//~    assert IsStatePath(k, s, s'', ops + [op], path1);
//~  }

  lemma MakeTransaction1(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  requires |ops| == 1
  requires OpStep(k, s, s', ops[0]);
  ensures OpTransaction(k, s, s', ops);
  {
    reveal_OpTransaction();
    var path := [s, s'];
    assert IsStatePath(k, s, s', ops, path);
  }

  lemma MakeTransaction2(k: Constants, s: Variables, s': Variables, s'': Variables, ops: seq<Op>)
  requires |ops| == 2
  requires OpStep(k, s, s', ops[0]);
  requires OpStep(k, s', s'', ops[1]);
  ensures OpTransaction(k, s, s'', ops);
  {
    reveal_OpTransaction();
    var path := [s, s', s''];
    assert IsStatePath(k, s, s'', ops, path);
  }

  lemma MakeTransaction3(k: Constants, s: Variables, s': Variables, s'': Variables, s''': Variables, ops: seq<Op>)
  requires |ops| == 3
  requires OpStep(k, s, s', ops[0]);
  requires OpStep(k, s', s'', ops[1]);
  requires OpStep(k, s'', s''', ops[2]);
  ensures OpTransaction(k, s, s''', ops);
  {
    reveal_OpTransaction();
    var path := [s, s', s'', s'''];
    assert IsStatePath(k, s, s''', ops, path);
  }

  lemma GetPenultimateState(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  returns (smid : Variables)
  requires |ops| >= 1
  requires OpTransaction(k, s, s', ops)
  ensures OpTransaction(k, s, smid, DropLast(ops))
  ensures OpStep(k, smid, s', Last(ops))
  {
    reveal_OpTransaction();
    var path :| IsStatePath(k, s, s', ops, path);
    smid := path[|path| - 2];
    assert IsStatePath(k, s, smid, DropLast(ops), DropLast(path));
  }
}
