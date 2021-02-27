// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../lib/Base/sequences.i.dfy"
  
module Circular_List {
  import opened Sequences
  
  class Node<T> {
    var value: T
      var prev: Node<T>
      var next: Node<T>
      ghost var nodes: seq<Node<T> >;

      constructor(x: T)
        ensures Valid(this);
        ensures this == this.nodes[0];
        ensures Singleton(this);
        ensures this.value == x;
      {
        reveal_NoDupes();
        value := x;
        prev := this;
        next := this;
        nodes := [ this ];
      }
  }

  predicate Valid(node: Node)
    reads node;
    reads node.nodes;
  {
    var nodes := node.nodes;
    // We're in the list
    && (node in multiset(nodes))
    // Everybody in the list agrees on the list
    && (forall node' :: node' in nodes ==> node'.nodes == nodes)
    // There's no duplicates in the list (technically redundant but helpful)
    && NoDupes(nodes)
    // nexts and prevs point right and left in the list, respectively
    && (forall i :: 0 <= i < |nodes| - 1 ==> nodes[i].next == nodes[i+1])
    && nodes[|nodes|-1].next == nodes[0]
    && (forall i :: 1 <= i < |nodes| ==> nodes[i].prev == nodes[i-1])
    && nodes[0].prev == nodes[|nodes|-1]
  }

  // The veg-o-matic of circular lists.
  //
  // - If a and b are nodes in separate circular lists, then
  //   this method will join them into the list
  //      a, a.next, ..., a.prev, b, b.next, ..., b.prev
  //
  // - If a and b are distinct nodes in the same circular list,
  //   then this method will divide them into two lists:
  //      a, a.next, ..., b.prev
  //   and
  //      b, b.next, ..., a.prev
  //
  // Thus this method can be used to insert nodes, remove nodes,
  // concatenate lists, slice up lists, etc.
  method Splice(a: Node, b: Node)
    requires Valid(a);
    requires Valid(b);
    requires a != b;
    requires a == a.nodes[0];
    requires multiset(a.nodes) !! multiset(b.nodes) || a.nodes == b.nodes;
    requires a.nodes != b.nodes ==> b == b.nodes[0];
    ensures Valid(a);
    ensures Valid(b);
    ensures forall n :: n in old(a.nodes) ==> n.value == old(n.value);
    ensures forall n :: n in old(b.nodes) ==> n.value == old(n.value);
    ensures old(a.nodes) == old(b.nodes) ==> (
      && a.nodes == old(a.nodes[0..IndexOf(a.nodes, b)])
      && b.nodes == old(a.nodes[IndexOf(a.nodes, b)..])
      );
    ensures multiset(old(a.nodes)) !! multiset(old(b.nodes)) ==> (
        && a.nodes == old(a.nodes) + old(b.nodes)
        && a.nodes == b.nodes
        );
    modifies a, b, multiset(a.nodes), multiset(b.nodes);
  {
    var a_last := a.prev;
    var b_last := b.prev;

    assert IndexOf(b.nodes, b) > 0 ==> b_last == b.nodes[IndexOf(b.nodes, b)-1]; // Observe

    // Le code
    a_last.next := b;
    b_last.next := a;
    a.prev := b_last;
    b.prev := a_last;

    // Le proof
    if a.nodes != b.nodes {
      reveal_NoDupes();
      DisjointConcatenation(a.nodes, b.nodes);
      ghost var newnodes := a.nodes + b.nodes;
      forall a' | a' in newnodes {
        a'.nodes := newnodes;
      }
    } else {
      reveal_NoDupes();
      assert |multiset(a.nodes)| > 0; // Observe
      ghost var newanodes := a.nodes[..IndexOf(a.nodes, b)];
      ghost var newbnodes := b.nodes[IndexOf(b.nodes, b)..];
      forall a' | a' in newanodes {
        a'.nodes := newanodes;
      }
      forall b' | b' in newbnodes {
        b'.nodes := newbnodes;
      }
    }
  }

  predicate method Singleton(n: Node)
    requires Valid(n);
    ensures Singleton(n) ==> n.nodes == [ n ];
    reads n, n.nodes;
  {
    reveal_NoDupes();
    ghost var i := IndexOf(n.nodes, n);
    assert n.next == n.nodes[(i + 1) % |n.nodes|];
    n.prev == n.next == n
  }

  method Remove(n: Node) returns (other: Node)
    requires Valid(n);
    requires !Singleton(n);
    requires n == n.nodes[0];
    ensures Valid(n);
    ensures Valid(other);
    ensures Singleton(n);
    ensures other.nodes == old(n.nodes[1..]);
    ensures other == other.nodes[0];
    ensures forall x :: x in old(n.nodes) ==> x.value == old(x.value);
    modifies n, multiset(n.nodes);
  {
    assert n.nodes[1] == n.next; // Observe
    other := n.next;
    Splice(n, other);
  }
  
  function {:opaque} ReverseSeq<T>(s: seq<T>) : seq<T>
    ensures |ReverseSeq(s)| == |s|;
    ensures forall i :: 0 <= i < |s| ==> ReverseSeq(s)[i] == s[|s|-1-i];
  {
    if |s| <= 1 then s
    else ReverseSeq(s[1..]) + [s[0]]
  }
  
  method ReverseTail(reversed: Node, head: Node)
    requires Valid(reversed);
    requires Valid(head);
    requires reversed == reversed.nodes[0];
    requires head == head.nodes[0];
    requires multiset(reversed.nodes) !! multiset(head.nodes);
    ensures Valid(reversed);
    ensures forall n :: n in old(reversed.nodes) ==> n.value == old(n.value);
    ensures forall n :: n in old(head.nodes) ==> n.value == old(n.value);
    ensures reversed.nodes == ReverseSeq(old(head.nodes)) + old(reversed.nodes);
    modifies multiset(reversed.nodes);
    modifies head, multiset(head.nodes);
    decreases |head.nodes|;
  {
    if Singleton(head) {
      Splice(head, reversed);
    } else {
      var tail := Remove(head);
      Splice(head, reversed);
      ReverseTail(head, tail);
    }
  }

  method Reverse(head: Node)
    requires Valid(head);
    requires head == head.nodes[0];
    ensures Valid(head);
    ensures forall n :: n in old(head.nodes) ==> n.value == old(n.value);
    ensures head.nodes == ReverseSeq(old(head.nodes));
    modifies multiset(head.nodes);
  {
    if ! Singleton(head) {
      var tail := Remove(head);
      ReverseTail(head, tail);
    }
  }
}

method Main()
{
  var n1 := new Circular_List.Node(7);
  var n2 := new Circular_List.Node(8);
  var n3 := new Circular_List.Node(9);
  var n4 := new Circular_List.Node(10);


  Circular_List.Splice(n1, n2);

  assert n1.value == 7;
  assert n2.value == 8;
  assert n3.value == 9;

  assert n1.next == n2;
  assert n1.next.value == 8;
  assert n1.next.next.value == 7;

  assert n1.nodes == [ n1, n2 ];
  
  Circular_List.Splice(n1, n3);

  assert n1.nodes == [ n1, n2, n3 ];
  assert n1.next == n1.nodes[1];
  assert n1.next == n2;

  assert n1.value == 7;
  assert n2.value == 8;
  assert n3.value == 9;

  assert n1.prev == n3;
  assert n3.next == n1;
  assert n1.next == n2;
  assert n2.next == n3;
  assert n1.next.value == 8;
  assert n1.next.next.value == 9;
  assert n1.next.next.next.value == 7;

  Circular_List.Splice(n1, n4);
  assert n1.nodes == [ n1, n2, n3, n4 ]; // observe
  assert n1.next == n1.nodes[1];
  assert n1.next.next == n1.nodes[2];
  assert n1.next.next.next == n1.nodes[3];
  assert n1.next.next.next.value == 10;

  Circular_List.Reverse(n1);
  assert n1.nodes == [ n4, n3, n2, n1 ]; // observe
  assert [ n1.value, n1.next.value, n1.next.next.value, n1.next.next.next.value ] == [7, 10, 9, 8];
}
