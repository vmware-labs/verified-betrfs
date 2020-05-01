include "../Lang/NativeTypes.s.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Option.s.dfy"
include "MutableMapImpl.i.dfy"
//
// An LRU-queue.
//

module LruModel {
	export S provides LruQueue, WF, I, Empty, Remove, Use, Pop, Next, LruUse, NextOpt, LruRemove, NativeTypes, Options

	export Internal reveals *
	export extends S

  import opened NativeTypes
  import opened Sequences
  import opened Options

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
    set x | x in q
  }

  function Empty() : (q : LruQueue)
  ensures I(q) == {}
  ensures WF(q)
  {
    reveal_distinct();
    []
  }

  function Remove(q: LruQueue, x: uint64) : LruQueue
  {
    if |q| == 0 then [] else (
      if Last(q) == x then Remove(DropLast(q), x) else Remove(DropLast(q), x) + [Last(q)]
    )
  }

  function Remove'(q: LruQueue, x: uint64) : LruQueue
  {
    if x !in q then q else
    var i :| 0 <= i < |q| && x == q[i];
    q[.. i] + q[i + 1 ..]
  }

  function Use(q: LruQueue, x: uint64) : LruQueue
  {
    Remove(q, x) + [x]
  }

  function Next(q: LruQueue) : (x : uint64)
  requires |I(q)| > 0
  ensures x in I(q)
  {
    q[0]
  }

  function {:opaque} NextOpt(q: LruQueue) : (x : Option<uint64>)
  ensures x.Some? ==> x.value in I(q)
  ensures x.None? ==> I(q) == {}
  {
    if q == [] then None else Some(q[0])
  }

  function Pop(q: LruQueue) : (LruQueue, uint64)
  requires |I(q)| > 0
  {
    (q[1..], q[0])
  }

  lemma LruRemove'(q: LruQueue, x: uint64)
    requires WF(q)
    ensures Remove(q, x) == Remove'(q, x)
  {
    reveal_distinct();
    if |q| > 0 {LruRemove'(DropLast(q), x);}
  }

  lemma LruRemoveGetIndex(q: LruQueue, x: uint64, j: int)
  returns (i: int)
  requires WF(q)
  requires 0 <= j < |Remove(q, x)|
  ensures 0 <= i < |q|
  ensures q[i] == Remove(q, x)[j];
  {
    if j + 1 == |Remove(q, x)| && q[|q| - 1] != x {
      i := |q| - 1;
    } else {
      i := LruRemoveGetIndex(DropLast(q), x, j);
    }
  }

  lemma LruRemoveGetIndex2(q: LruQueue, x: uint64, j1: int, j2: int)
  returns (i1: int, i2: int)
  requires WF(q)
  requires 0 <= j1 < |Remove(q, x)|
  requires 0 <= j2 < |Remove(q, x)|
  requires j1 != j2
  ensures 0 <= i1 < |q|
  ensures 0 <= i2 < |q|
  ensures i1 != i2
  ensures q[i1] == Remove(q, x)[j1];
  ensures q[i2] == Remove(q, x)[j2];
  {
    if j2 + 1 == |Remove(q, x)| && q[|q| - 1] != x {
      i1 := LruRemoveGetIndex(DropLast(q), x, j1);
      i2 := |q| - 1;
    } else if j1 + 1 == |Remove(q, x)| && q[|q| - 1] != x {
      i2 := LruRemoveGetIndex(DropLast(q), x, j2);
      i1 := |q| - 1;
    } else {
      i1, i2 := LruRemoveGetIndex2(DropLast(q), x, j1, j2);
    }
  }

  lemma LruRemoveGetIndexRev(q: LruQueue, x: uint64, i: int)
  returns (j: int)
  requires WF(q)
  requires 0 <= i < |q|
  requires q[i] != x
  ensures 0 <= j < |Remove(q, x)|
  ensures q[i] == Remove(q, x)[j];
  {
    if i + 1 == |q| {
      j := |Remove(q,x)| - 1;
    } else {
      j := LruRemoveGetIndexRev(DropLast(q), x, i);
    }
  }

  lemma LruRemove(q: LruQueue, x: uint64)
  requires WF(q)
  ensures WF(Remove(q, x))
  ensures I(Remove(q, x)) == I(q) - {x}
  {
    if |q| == 0 {
    } else {
      LruRemove(DropLast(q), x);
      if q[|q| - 1] != x {
        reveal_distinct();
        forall i, j | 0 <= i < |Remove(q,x)| && 0 <= j < |Remove(q,x)| && i != j
        ensures Remove(q,x)[i] != Remove(q,x)[j]
        {
          var i1, j1 := LruRemoveGetIndex2(q, x, i, j);
        }
      }
    }

    var a := I(Remove(q, x));
    var b := I(q) - {x};
    forall r | r in a
    ensures r in b
    {
      var j :| 0 <= j < |Remove(q, x)| && Remove(q, x)[j] == r;
      var j1 := LruRemoveGetIndex(q, x, j);
    }
    forall r | r in b
    ensures r in a
    {
      var i :| 0 <= i < |q| && q[i] == r;
      var j := LruRemoveGetIndexRev(q, x, i);
    }
  }

  lemma notInRemove(q: LruQueue, x: uint64, i: int)
  requires 0 <= i < |Remove(q,x)|
  ensures Remove(q,x)[i] != x
  {
    if i + 1 == |Remove(q, x)| && q[|q| - 1] != x {
    } else {
      notInRemove(DropLast(q), x, i);
    }
  }

  lemma LruUse(q: LruQueue, x: uint64)
  requires WF(q)
  ensures WF(Use(q, x))
  ensures I(Use(q, x)) == I(q) + {x}
  {
    LruRemove(q, x);
    reveal_distinct();
    forall i, j | 0 <= i < |Use(q,x)| && 0 <= j < |Use(q,x)| && i != j
    ensures Use(q,x)[i] != Use(q,x)[j]
    {
      if (i == |Use(q,x)| - 1) {
        notInRemove(q, x, j);
      } else if (j == |Use(q,x)| - 1) {
        notInRemove(q, x, i);
      } else {
      }
    }
    assert I(Use(q, x))
        == I(Remove(q,x) + [x])
        == I(Remove(q,x)) + {x}
        == (I(q) - {x}) + {x}
        == I(q) + {x};
  }

  lemma QueueCount(q: LruQueue)
  requires WF(q)
  ensures |I(q)| == |q|
  {
    if (|q| > 0) {
      assert I(q) == I(q[1..]) + {q[0]};
      QueueCount(q[1..]);
    }
  }
}
