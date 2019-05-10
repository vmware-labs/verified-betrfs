module Circular_List {
  
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
      value := x;
      prev := this;
      next := this;
      nodes := [ this ];
    }
  }

  predicate NoDupes<T>(a: seq<T>) {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  lemma DisjointConcatenation<T>(a: seq<T>, b: seq<T>)
    requires NoDupes(a);
    requires NoDupes(b);
    requires multiset(a) !! multiset(b);
    ensures NoDupes(a + b);
  {
    var c := a + b;
    if |c| > 1 {
      assert forall i, j :: i != j && 0 <= i < |a| && |a| <= j < |c| ==>
        c[i] in multiset(a) && c[j] in multiset(b) && c[i] != c[j]; // Observe
    }
  }

  function IndexOf<T>(s: seq<T>, e: T) : int
    requires e in s;
    ensures 0 <= IndexOf(s,e) < |s|;
    ensures s[IndexOf(s,e)] == e;
  {
    var i :| 0 <= i < |s| && s[i] == e;
    i
  }

  predicate RotationallyEquivalent<T>(a: seq<T>, b: seq<T>) {
    exists i :: 0 <= i < |b| && a == (b[i..] + b[..i])
  }

  predicate ClosedUnderNextsAndPrevs<T>(s: seq<Node<T> >)
    reads s;
  {
    forall n :: n in s ==> n.prev in s && n.next in s
  }
  
  predicate Valid(node: Node)
    reads node;
    reads node.nodes;
  {
    var nodes := node.nodes;
    // We're in the list
    (node in nodes) &&
    // Everybody in the list agrees on the list
    (forall node' :: node' in nodes ==> node'.nodes == nodes) &&
    // There's no duplicates in the list (technically redundant but helpful)
    NoDupes(nodes) &&
    // nexts and prevs point right and left in the list, respectively
    (forall i :: 0 <= i < |nodes|-1 ==> nodes[i].next == nodes[i+1]) &&
    nodes[|nodes|-1].next == nodes[0] &&
    (forall i :: 1 <= i < |nodes| ==> nodes[i].prev == nodes[i-1]) &&
    nodes[0].prev == nodes[|nodes|-1]
  }

  lemma ValidImpliesClosed(l: Node)
    requires Valid(l);
    ensures ClosedUnderNextsAndPrevs(l.nodes);
  {
    forall n | n in l.nodes
      ensures n.next in l.nodes && n.prev in l.nodes;
      {
        var idx := IndexOf(n.nodes, n);
        assert idx < |n.nodes|-1  ==> n.next == n.nodes[idx+1];
        assert idx == |n.nodes|-1 ==> n.next == n.nodes[0];
        assert n.next in n.nodes;

        assert idx > 0  ==> n.prev == n.nodes[idx-1];
        assert idx == 0 ==> n.prev == n.nodes[|n.nodes|-1];
        assert n.prev in n.nodes;
      }

  }
  
  lemma NextIsValid(node: Node)
    requires Valid(node);
    ensures Valid(node.next);
    ensures node.next in node.nodes;
    ensures node.next.nodes == node.nodes;
  {
    var idx := IndexOf(node.nodes, node);
    if idx < |node.nodes|-1 {
      assert node.next == node.nodes[idx + 1];
    }
  }

  lemma PrevIsValid(node: Node)
    requires Valid(node);
    ensures Valid(node.prev);
    ensures node.prev in node.nodes;
    ensures node.prev.nodes == node.nodes;
  {
    var idx := IndexOf(node.nodes, node);
    if idx > 0 {
      assert node.prev == node.nodes[idx - 1];
    }
  }

  lemma PrevNextCancel(n: Node)
    requires Valid(n);
    ensures n.next.prev == n;
  {
    NextIsValid(n);
    var idx := IndexOf(n.nodes, n);
    if idx < |n.nodes|-1 {
      assert n.next == n.nodes[idx+1];
    }
  }

  ghost method BringToFront(a: Node)
    requires Valid(a);
    ensures Valid(a);
    ensures a.nodes == old(a.nodes[IndexOf(a.nodes, a)..]) + old(a.nodes[..IndexOf(a.nodes, a)]);
    ensures forall n :: n in a.nodes ==> n.value == old(n.value);
    modifies a, a.nodes;
  {
    ghost var i := IndexOf(a.nodes, a);
    ghost var newnodes := a.nodes[i..] + a.nodes[..i];
    forall a' | a' in a.nodes {
      a'.nodes := newnodes;
    }
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
      && old(a.nodes) == old(b.nodes) == a.nodes + b.nodes
      && multiset(a.nodes) !! multiset(b.nodes)
      );
    ensures multiset(old(a.nodes)) !! multiset(old(b.nodes)) ==> (
      && a.nodes == old(a.nodes) + old(b.nodes)
      && a.nodes == b.nodes
      && |old(a.nodes)| > 1 ==> a.next == old(a.next)
      // && forall i :: 0 <= i < |old(a.nodes)|-1 ==> a.nodes[i].next == old(a.nodes[i].next)
      );
    modifies a, b, a.nodes, b.nodes;
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
      DisjointConcatenation(a.nodes, b.nodes);
      ghost var newnodes := a.nodes + b.nodes;
      forall a' | a' in newnodes {
        a'.nodes := newnodes;
      }
    } else {
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
    reads n, n.nodes;
  {
    n.prev == n.next == n
  }

  lemma SingletonFacts(n: Node)
    requires Valid(n);
    requires Singleton(n);
    ensures n.nodes == [n];
  {
    var idx := IndexOf(n.nodes, n);
    if idx > 0 {
      assert n.nodes[idx-1] == n;
    }
  }

  lemma NonSingletonFacts(n: Node)
    requires Valid(n);
    requires !Singleton(n);
    ensures Valid(n.next);
    ensures Valid(n.prev);
    ensures n.next != n;
    ensures n.prev != n;
    ensures |n.nodes| > 1;
  {
    NextIsValid(n);
    PrevIsValid(n);
    var idx := IndexOf(n.nodes, n);
    if idx < |n.nodes|-1 {
      assert n.next == n.nodes[idx+1];
    }
    if idx > 0 {
      assert n.prev == n.nodes[idx-1];
    }
  }

  // method Remove(n: Node) returns (other: Node)
  //   requires Valid(n);
  //   requires !Singleton(n);
  //   ensures Valid(n);
  //   ensures Valid(other);
  //   ensures Singleton(n);
  //   ensures other.nodes == old(n.nodes[IndexOf(n.nodes,n)+1..]) + old(n.nodes[..IndexOf(n.nodes,n)]);
  //   ensures forall i :: 0 <= i < |other.nodes| ==> other.nodes[i] in old(n.nodes);
  //   ensures forall x :: x in old(n.nodes) ==> x.value == old(x.value);
  //   modifies n, n.next, n.nodes, n.next.nodes;
  // {
  //   BringToFront(n);
  //   NonSingletonFacts(n);
  //   assert n.nodes[1] == n.next; // Observe
  //   other := n.next;
  //   Splice(n, other);
  // }

  // The convention for a dll is that head == head.nodes[0]
  // predicate IsHead(n: Node)
  //   requires Valid(n);
  //   reads n, n.nodes;
  // {
  //   n == n.nodes[0]
  // }
  
  // function ReverseSeq<T>(s: seq<T>) : seq<T> {
  //   if |s| <= 1 then s
  //   else ReverseSeq(s[1..]) + [s[0]]
  // }

  // lemma ListsAreDisjointOrEqual(l1: Node, l2: Node)
  //   requires Valid(l1);
  //   requires Valid(l2);
  //   ensures l1.nodes == l2.nodes || multiset(l1.nodes) !! multiset(l2.nodes);
  // {
  //   if ! (multiset(l1.nodes) !! multiset(l2.nodes)) {
  //     var n :| n in l1.nodes && n in l2.nodes; // OBSERVE
  //   }
  // }

  // method FlipTail(reversed: Node, head: Node)
  //   requires Valid(reversed);
  //   requires IsHead(reversed);
  //   requires Valid(head);
  //   requires IsHead(head);
  //   requires reversed != head;
  //   ensures forall n :: n in old(reversed.nodes) ==> n.value == old(n.value);
  //   ensures forall n :: n in old(head.nodes) ==> n.value == old(n.value);
  //   modifies set n : Node | n in reversed.nodes;
  //   modifies set n : Node | n in head.nodes;
  //   decreases |head.nodes|;
  // {
  //   ValidImpliesClosed(head); // OBSERVE
    
  //   if Singleton(head) {
  //     Splice(head, reversed);
  //   } else {
  //     var tail := Remove(head);

  //     SingletonFacts(head); // OBSERVE
  //     BringToFront(tail); // OBSERVE
      
  //     Splice(head, reversed);
  //     FlipTail(head, tail);
  //   }
  // }

  // method Reverse(head: Node)
  //   requires Valid(head);
  //   requires IsHead(head);
  //   ensures head.nodes == ReverseSeq(old(head.nodes));
  //   modifies set n : Node | n in head.nodes;
  // {
  //   ValidImpliesClosed(head); // OBSERVE
  //   if ! Singleton(head) {
  //     var tail := Remove(head);
  //     SingletonFacts(head); // OBSERVE
  //     BringToFront(tail); // OBSERVE
  //     FlipTail(head, tail);
  //   }
  // }
}

method Main()
{
  var n1 := new Circular_List.Node(7);
  var n2 := new Circular_List.Node(8);
  var n3 := new Circular_List.Node(9);
  //var n4 := new Circular_List.Node(10);


  Circular_List.Splice(n1, n2);

  assert n1.value == 7;
  assert n2.value == 8;
  assert n3.value == 9;

  assert n1.next.value == 8;
  assert n1.next.next.value == 7;
  
  Circular_List.Splice(n1, n3);

  assert n1.value == 7;
  assert n2.value == 8;
  assert n3.value == 9;
  
  assert n1.next.value == 8;
  assert n1.next.next.value == 9;
  assert n1.next.next.next.value == 7;
}
