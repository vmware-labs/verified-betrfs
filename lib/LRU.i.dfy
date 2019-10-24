// A LRU-queue.

include "NativeTypes.s.dfy"
include "sequences.s.dfy"
include "MutableMapImpl.i.dfy"
include "Option.s.dfy"

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
}

module MutableLru {
  import opened NativeTypes
  import opened Sequences
  import opened LruModel`Internal
  import MutableMap
  import opened Options

  lemma lemmaRemoveNonPresentKeyFromQueue(q: LruQueue, x: uint64)
  requires x !in q
  requires WF(q)
  ensures LruModel.Remove(q, x) == q
  {
    if |q| == 0 {
    } else {
      lemmaRemoveNonPresentKeyFromQueue(q[..|q|-1], x);
    }
  }

  lemma LemmaQueueCountEqInterpCount(q: LruQueue)
  requires WF(q)
  ensures |I(q)| == |q|
  {
    reveal_distinct();
    if |q| == 0 {
    } else {
      LemmaQueueCountEqInterpCount(q[..|q| - 1]);
      assert I(q) == I(q[..|q|-1]) + {q[|q|-1]};
      assert |I(q)|
          == |I(q[..|q|-1]) + {q[|q|-1]}|
          == |I(q[..|q|-1])| + |{q[|q|-1]}|
          == |q[..|q|-1]| + 1
          == |q|;
    }
  }

  lemma lemmaGetRemoveQueueIndex(q: LruQueue, x: uint64)
  returns (j: int)
  requires x in q
  requires WF(q)
  ensures 0 <= j < |q|
  ensures q[j] == x
  ensures LruModel.Remove(q, x) == q[..j] + q[j+1..]
  {
    assert |q| > 0;
    if q[|q| - 1] == x {
      j := |q| - 1;
      reveal_distinct();
      lemmaRemoveNonPresentKeyFromQueue(q[..|q|-1], x);
    } else {
      j := lemmaGetRemoveQueueIndex(q[..|q|-1], x);
    }
  }

  class Node {
    var prev: Node?;
    var next: Node?;
    var value: uint64;

    constructor (p: Node?, n: Node?, v: uint64)
    ensures prev == p
    ensures next == n
    ensures value == v
    {
      prev := p;
      next := n;
      value := v;
    }
  }

  class MutableLruQueue {
    ghost var Queue: LruQueue;
    ghost var Repr: set<object>;

    var nodemap: MutableMap.ResizingHashMap<Node>;
    var head_node: Node?;
    var tail_node: Node?;

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    ensures Inv() ==> WF(Queue)
    {
      && nodemap in Repr
      && nodemap.Repr <= Repr
      && nodemap.Inv()
      && Repr == {this} + nodemap.Repr + nodemap.I().contents.Values
      && this !in nodemap.Repr
      && nodemap.I().contents.Values !! nodemap.Repr
      && (|Queue| == 0 ==> (
        && head_node == null
        && tail_node == null
        && nodemap.I().contents == map[]
      ))
      && (forall i | 0 <= i < |Queue| :: Queue[i] in nodemap.I().contents)
      && (forall ref | ref in nodemap.I().contents :: ref in Queue)
      && (forall ref | ref in nodemap.I().contents :: nodemap.I().contents[ref].value == ref)
      && (|Queue| > 0 ==>
        && head_node == nodemap.I().contents[Queue[0]]
        && tail_node == nodemap.I().contents[Queue[|Queue| - 1]]
        && nodemap.I().contents[Queue[0]].prev == null
        && nodemap.I().contents[Queue[|Queue| - 1]].next == null
      )
      && (forall i | 0 <= i < |Queue| - 1 ::
          nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]])
      && (forall i | 0 <= i < |Queue| - 1 ::
          nodemap.I().contents[Queue[i]] == nodemap.I().contents[Queue[i+1]].prev)
      && nodemap.Repr !! nodemap.I().contents.Values
      && WF(Queue)
    }

    constructor ()
    ensures Inv()
    ensures Queue == Empty()
    ensures fresh(Repr)
    {
      var m := new MutableMap.ResizingHashMap<Node>(128);

      nodemap := m;
      head_node := null;
      tail_node := null;

      Queue := [];
      Repr := {this} + m.Repr + m.Contents.Values;
    }

    method Remove(x: uint64)
    requires Inv()
    ensures Inv()
    ensures Queue == LruModel.Remove(old(Queue), x)
    ensures Repr <= old(Repr)
    modifies this, this.Repr
    {
      ghost var oldContents := nodemap.I().contents;
      ghost var oldQueue := Queue;

      var node := nodemap.RemoveAndGet(x);
      if node.Some? {
        var prev := node.value.prev;
        var next := node.value.next;

        ghost var j := lemmaGetRemoveQueueIndex(Queue, x);
        if (j > 0) {
          assert oldContents[x].prev == oldContents[Queue[j-1]];
        }
        if (j < |Queue| - 1) {
          assert oldContents[x].next == oldContents[Queue[j+1]];
        }

        if (prev == null) {
          head_node := next;
        } else {
          prev.next := next;
        }

        if (next == null) {
          tail_node := prev;
        } else {
          next.prev := prev;
        }

        Repr := {this} + nodemap.Repr + nodemap.I().contents.Values;
        Queue := LruModel.Remove(Queue, x);

        forall k | 0 <= k < |Queue| ensures Queue[k] in nodemap.I().contents
        {
          reveal_distinct();
          if k < j {
            assert oldQueue[k] == Queue[k];
            assert oldQueue[k] in oldContents;
            assert oldQueue[k] != x;
            assert oldQueue[k] in nodemap.I().contents;
          } else {
            assert oldQueue[k+1] == Queue[k];
            assert oldQueue[k+1] in oldContents;
            assert oldQueue[k+1] != x;
            assert oldQueue[k+1] in nodemap.I().contents;
          }
        }

        forall ref | ref in nodemap.I().contents ensures ref in Queue
        {
          assert ref in oldContents;
          var k :| 0 <= k < |oldQueue| && oldQueue[k] == ref;
          assert k != j;
          if k < j {
            assert Queue[k] == ref;
          } else {
            assert Queue[k-1] == ref;
          }
        }

        forall k | 0 <= k < |Queue| - 1
        ensures nodemap.I().contents[Queue[k]] == nodemap.I().contents[Queue[k+1]].prev
        {
          if k < j-1 {
            assert nodemap.I().contents[Queue[k]] == nodemap.I().contents[Queue[k+1]].prev;
          } else if k == j-1 {
            assert nodemap.I().contents[Queue[k]] == nodemap.I().contents[Queue[k+1]].prev;
          } else {
            assert nodemap.I().contents[Queue[k]] == nodemap.I().contents[Queue[k+1]].prev;
          }
        }

        forall i | 0 <= i < |Queue| - 1 
        ensures nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]]
        {
          if i < j - 1 {
            assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
          } else if i == j-1 {
            assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
          } else {
            assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
          }
        }
      } else {
        assert nodemap.I().contents == oldContents;
        lemmaRemoveNonPresentKeyFromQueue(Queue, x);

        forall k | 0 <= k < |Queue| - 1
        ensures nodemap.I().contents[Queue[k]] == nodemap.I().contents[Queue[k+1]].prev
        {
        }

        forall i | 0 <= i < |Queue| - 1 
        ensures nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]]
        {
        }
      }

      LruRemove(oldQueue, x);
    }

    lemma LemmaMapCountEqInterpCount()
    requires Inv()
    ensures |I(Queue)| == nodemap.Count as int
    {
      assert I(Queue) == nodemap.I().contents.Keys;
      assert |I(Queue)|
          == |nodemap.I().contents.Keys|
          ==|nodemap.I().contents|
          == nodemap.Count as int;
    }

    method Use(x: uint64)
    requires Inv()
    requires |I(Queue)| <= 0x1_0000_0000
    ensures Inv()
    ensures Queue == LruModel.Use(old(Queue), x)
    ensures forall x | x in Repr :: x in old(Repr) || fresh(x)
    modifies this, this.Repr
    {
      ghost var oldContents := nodemap.I().contents;
      ghost var oldQueue := Queue;
      LemmaMapCountEqInterpCount();

      var node := nodemap.Get(x);
      if node.Some? {
        var prev := node.value.prev;
        var next := node.value.next;

        ghost var j := lemmaGetRemoveQueueIndex(Queue, x);
        if (j > 0) {
          assert oldContents[x].prev == oldContents[Queue[j-1]];
        }
        if (j < |Queue| - 1) {
          assert oldContents[x].next == oldContents[Queue[j+1]];
        }

        if (next != null) {
          if (prev == null) {
            head_node := next;
          } else {
            prev.next := next;
          }

          next.prev := prev;

          node.value.prev := tail_node;
          node.value.next := null;
          if (tail_node != null) {
            tail_node.next := node.value;
          } else {
            head_node := node.value;
          }
          tail_node := node.value;

          Repr := {this} + nodemap.Repr + nodemap.I().contents.Values;
          Queue := LruModel.Remove(Queue, x) + [x];

          forall i | 0 <= i < |Queue| - 1
          ensures nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]]
          {
            if i == |Queue| - 2 {
              assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
            } else if i == j-1 {
              assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
            } else if i < j-1 {
              assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
            } else {
              assert nodemap.I().contents[Queue[i]].next == nodemap.I().contents[Queue[i+1]];
            }
          }

          forall i | 0 <= i < |Queue| - 1
          ensures nodemap.I().contents[Queue[i]] == nodemap.I().contents[Queue[i+1]].prev
          {
          }
        } else {
          Repr := {this} + nodemap.Repr + nodemap.I().contents.Values;
          Queue := LruModel.Remove(Queue, x) + [x];
        }
      } else {
        lemmaRemoveNonPresentKeyFromQueue(Queue, x);

        var newnode := new Node(tail_node, null, x);
        assert newnode.next == null;
        if (tail_node != null) {
          tail_node.next := newnode;
        } else {
          head_node := newnode;
        }
        tail_node := newnode;

        nodemap.Insert(x, newnode);

        Repr := {this} + nodemap.Repr + nodemap.I().contents.Values;
        Queue := oldQueue + [x];

        assert Queue[|Queue| - 1] == x;
        assert nodemap.I().contents[x] == newnode;
        assert newnode.next == null;
        assert nodemap.I().contents[Queue[|Queue| - 1]].next == null;
        forall ref | ref in nodemap.I().contents ensures nodemap.I().contents[ref].value == ref
        {
        }
        forall i | 0 <= i < |Queue| ensures Queue[i] in nodemap.I().contents
        {
          if (i == |Queue| - 1) {
          } else {
          }
        }
      }

      LruUse(oldQueue, x);
    }

    method Next()
    returns (x: uint64)
    requires |I(Queue)| > 0
    requires Inv()
    ensures x == LruModel.Next(Queue)
    {
      LemmaQueueCountEqInterpCount(Queue);
      assert head_node != null;
      x := head_node.value;
    }

    method NextOpt()
    returns (x: Option<uint64>)
    requires Inv()
    ensures x == LruModel.NextOpt(Queue)
    {
      LruModel.reveal_NextOpt();
      LemmaQueueCountEqInterpCount(Queue);
      if head_node != null {
        x := Some(head_node.value);
      } else {
        x := None;
      }
    }

  }
}
