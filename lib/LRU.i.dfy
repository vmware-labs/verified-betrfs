// A LRU-queue.

include "NativeTypes.s.dfy"
include "Sequences.s.dfy"
include "MutableMap.i.dfy"

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
    set x | x in q
  }

  function method Empty() : (q : LruQueue)
  ensures I(q) == {}
  ensures WF(q)
  {
    reveal_distinct();
    []
  }

  function method Remove(q: LruQueue, x: uint64) : LruQueue
  {
    if |q| == 0 then [] else (
      if Last(q) == x then Remove(DropLast(q), x) else Remove(DropLast(q), x) + [Last(q)]
    )
  }

  function method Use(q: LruQueue, x: uint64) : LruQueue
  {
    Remove(q, x) + [x]
  }

  function method Next(q: LruQueue) : (x : uint64)
  requires |I(q)| > 0
  ensures x in I(q)
  {
    q[0]
  }

  function method Pop(q: LruQueue) : (LruQueue, uint64)
  requires |I(q)| > 0
  {
    (q[1..], q[0])
  }

  lemma LruUse(q: LruQueue, x: uint64)
  requires WF(q)
  ensures WF(Use(q, x))
  ensures I(Use(q, x)) == I(q) + {x}

  lemma LruRemove(q: LruQueue, x: uint64)
  requires WF(q)
  ensures WF(Remove(q, x))
  ensures I(Remove(q, x)) == I(q) - {x}
}

module Lru {
  import opened NativeTypes
  import opened Sequences
  import opened LruModel`Internal
  import MutableMap

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
    {
      && nodemap in Repr
      && nodemap.Repr <= Repr
      && Repr == {this} + nodemap.Repr + nodemap.Contents.Values
      && (|Queue| == 0 ==> (
        && head_node == null
        && tail_node == null
        && nodemap.Contents == map[]
      ))
      && (forall i | 0 <= i < |Queue| :: Queue[i] in nodemap.Contents)
      && (forall ref | ref in nodemap.Contents :: ref in Queue)
      && (forall ref | ref in nodemap.Contents :: nodemap.Contents[ref].value == ref)
      && (|Queue| > 0 ==>
        && head_node == nodemap.Contents[Queue[0]]
        && tail_node == nodemap.Contents[Queue[|Queue| - 1]]
        && nodemap.Contents[Queue[0]].prev == null
        && nodemap.Contents[Queue[|Queue| - 1]].next == null
      )
      && (forall i | 0 <= i < |Queue| - 1 ::
          nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]])
      && (forall i | 0 <= i < |Queue| - 1 ::
          nodemap.Contents[Queue[i]] == nodemap.Contents[Queue[i+1]].prev)
      && nodemap.Inv()
      && nodemap.Repr !! nodemap.Contents.Values
      && WF(Queue)
    }

    constructor ()
    ensures Inv()
    ensures Queue == Empty()
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
      ghost var oldContents := nodemap.Contents;
      ghost var oldQueue := Queue;

      var node := nodemap.Remove(x);
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

        Repr := {this} + nodemap.Repr + nodemap.Contents.Values;
        Queue := LruModel.Remove(Queue, x);

        forall k | 0 <= k < |Queue| ensures Queue[k] in nodemap.Contents
        {
          reveal_distinct();
          if k < j {
            assert oldQueue[k] == Queue[k];
            assert oldQueue[k] in oldContents;
            assert oldQueue[k] != x;
            assert oldQueue[k] in nodemap.Contents;
          } else {
            assert oldQueue[k+1] == Queue[k];
            assert oldQueue[k+1] in oldContents;
            assert oldQueue[k+1] != x;
            assert oldQueue[k+1] in nodemap.Contents;
          }
        }

        forall ref | ref in nodemap.Contents ensures ref in Queue
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
        ensures nodemap.Contents[Queue[k]] == nodemap.Contents[Queue[k+1]].prev
        {
          if k < j-1 {
            assert nodemap.Contents[Queue[k]] == nodemap.Contents[Queue[k+1]].prev;
          } else if k == j-1 {
            assert nodemap.Contents[Queue[k]] == nodemap.Contents[Queue[k+1]].prev;
          } else {
            assert nodemap.Contents[Queue[k]] == nodemap.Contents[Queue[k+1]].prev;
          }
        }
      } else {
        assert nodemap.Contents == oldContents;
        lemmaRemoveNonPresentKeyFromQueue(Queue, x);

        forall k | 0 <= k < |Queue| - 1
        ensures nodemap.Contents[Queue[k]] == nodemap.Contents[Queue[k+1]].prev
        {
        }
      }

      LruRemove(oldQueue, x);
    }

    lemma LemmaMapCountEqInterpCount()
    requires Inv()
    ensures |I(Queue)| == nodemap.Count as int
    {
      assert I(Queue) == nodemap.Contents.Keys;
      assert |I(Queue)|
          == |nodemap.Contents.Keys|
          ==|nodemap.Contents|
          == nodemap.Count as int;
    }

    method Use(x: uint64)
    requires Inv()
    requires |I(Queue)| <= 0x10000
    ensures Inv()
    ensures Queue == LruModel.Use(old(Queue), x)
    ensures forall x | x in Repr :: x in old(Repr) || fresh(x)
    modifies this, this.Repr
    {
      ghost var oldContents := nodemap.Contents;
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

          Repr := {this} + nodemap.Repr + nodemap.Contents.Values;
          Queue := LruModel.Remove(Queue, x) + [x];

          forall i | 0 <= i < |Queue| - 1
          ensures nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]]
          {
            if i == |Queue| - 2 {
              assert nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]];
            } else if i == j-1 {
              assert nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]];
            } else if i < j-1 {
              assert nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]];
            } else {
              assert nodemap.Contents[Queue[i]].next == nodemap.Contents[Queue[i+1]];
            }
          }
        } else {
          Repr := {this} + nodemap.Repr + nodemap.Contents.Values;
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

        var _ := nodemap.Insert(x, newnode);

        Repr := {this} + nodemap.Repr + nodemap.Contents.Values;
        Queue := oldQueue + [x];

        assert Queue[|Queue| - 1] == x;
        assert nodemap.Contents[x] == newnode;
        assert newnode.next == null;
        assert nodemap.Contents[Queue[|Queue| - 1]].next == null;
        forall ref | ref in nodemap.Contents ensures nodemap.Contents[ref].value == ref
        {
        }
        forall i | 0 <= i < |Queue| ensures Queue[i] in nodemap.Contents
        {
          if (i == |Queue| - 1) {
          } else {
          }
        }
      }
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
  }
}
