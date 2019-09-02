// A LRU-queue.

include "NativeTypes.s.dfy"
include "Sequences.s.dfy"

module LruModel {
	export S provides LruQueue, WF, I, Empty, Remove, Use, Pop, Next, LruUse, LruRemove, NativeTypes

	export Internal reveals *
	export extends S

  import opened NativeTypes
  import opened Sequences

  // Index-0: Least recently used
  // Index-1: Most recently used
  type LruQueue = seq<uint64>

  predicate {:opaque} distinct(q: seq<uint64>)
  {
    forall i, j | 0 <= i < |q| && 0 <= j < |q| && i != j :: q[i] != q[j]
  }

  predicate WF(q: LruQueue)
  {
    distinct(q)
  }

  function I(q: LruQueue) : set<uint64>
  {
    set i | i in q
  }

  function method Empty() : (q : LruQueue)
  ensures I(q) == {}
  ensures WF(q)
  {
    reveal_distinct();
    []
  }

  function method Remove(q: LruQueue, i: uint64) : LruQueue
  {
    if |q| == 0 then [] else (
      if Last(q) == i then Remove(DropLast(q), i) else Remove(DropLast(q), i) + [Last(q)]
    )
  }

  function method Use(q: LruQueue, i: uint64) : LruQueue
  {
    Remove(q, i) + [i]
  }

  function method Next(q: LruQueue) : (i : uint64)
  requires |I(q)| > 0
  ensures i in I(q)
  {
    q[0]
  }

  function method Pop(q: LruQueue) : (LruQueue, uint64)
  requires |I(q)| > 0
  {
    (q[1..], q[0])
  }

  lemma LruUse(q: LruQueue, i: uint64)
  requires WF(q)
  ensures WF(Use(q, i))
  ensures I(Use(q, i)) == I(q) + {i}

  lemma LruRemove(q: LruQueue, i: uint64)
  requires WF(q)
  ensures WF(Remove(q, i))
  ensures I(Remove(q, i)) == I(q) - {i}
}
