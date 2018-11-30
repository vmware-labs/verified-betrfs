module Circular_List {
  
  class Node<T> {
    var value: T
      var prev: Node<T>
      var next: Node<T>
      ghost var nodes: seq<Node<T> >;

      constructor(x: T) {
        value := x;
        prev := this;
        next := this;
      }
  }

  predicate NoDupes<T>(a: seq<T>) {
    (forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j])
  }

  function IndexOf<T(==)>(s: seq<T>, e: T) : int
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

  predicate Valid(node: Node)
    reads node;
    reads node.nodes;
  {
    var nodes := node.nodes;
    // We're in the list
    (node in nodes) &&
    // Everybody in the list agrees on the list
    (forall node' :: node' in nodes ==> node'.nodes == nodes) &&
    // There's no duplicates in the list (technically reduncant but helpful)
    NoDupes(nodes) &&
    // next and prevs point right and left in the list, respectively
    (forall i :: 0 <= i < |nodes|-1 ==> nodes[i].next == nodes[i+1]) &&
    nodes[|nodes|-1].next == nodes[0] &&
    (forall i :: 1 <= i < |nodes| ==> nodes[i].prev == nodes[i-1]) &&
    nodes[0].prev == nodes[|nodes|-1]
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
    modifies a, a.nodes;
  {
    ghost var i := IndexOf(a.nodes, a);
    ghost var newnodes := a.nodes[i..] + a.nodes[..i];
    forall a' | a' in a.nodes {
      a'.nodes := newnodes;
    }
  }

  lemma DisjointConcatenation<T(==)>(a: seq<T>, b: seq<T>)
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

  method Splice(a: Node, b: Node)
    requires Valid(a);
    requires Valid(b);
    requires a != b;
    requires a == a.nodes[0];
    requires multiset(a.nodes) !! multiset(b.nodes) || a.nodes == b.nodes;
    requires a.nodes != b.nodes ==> b == b.nodes[0];
    ensures Valid(a);
    ensures Valid(b);
    ensures old(a.nodes) == old(b.nodes) ==>
      (multiset(a.nodes) !! multiset(b.nodes) &&
      a.nodes == old(a.nodes[..IndexOf(a.nodes, b)]) &&
      b.nodes == old(b.nodes[IndexOf(b.nodes, b)..]));
      ensures multiset(old(a.nodes)) !! multiset(old(b.nodes)) ==>
        (a.nodes == old(a.nodes) + old(b.nodes) &&
        a.nodes == b.nodes);
        modifies a, b, a.nodes, b.nodes;
  {
    var a_last := a.prev;
    var b_last := b.prev;

    assert IndexOf(b.nodes, b) > 0 ==> b_last == b.nodes[IndexOf(b.nodes, b)-1]; // Observe

    a_last.next := b;
    b_last.next := a;
    a.prev := b_last;
    b.prev := a_last;

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

  predicate Singleton(n: Node)
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

  method InsertAfter(a: Node, b: Node)
    requires Valid(a);
    requires Valid(b);
    requires a != b;
    requires Singleton(b);
    ensures Valid(a);
    ensures Valid(b);
    ensures a.next == b;
    ensures a.nodes == old(a.nodes[IndexOf(a.nodes, a)+1..]) + old(a.nodes[..IndexOf(a.nodes, a)+1]) + [b];
    modifies a, a.nodes, a.next, a.next.nodes, b, b.nodes;
  {
    var a' := a.next;
    SingletonFacts(b);
    NextIsValid(a);
    PrevNextCancel(a);
    BringToFront(a');
    BringToFront(b);
    Splice(a', b);
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

  method Remove(n: Node) returns (other: Node)
    requires Valid(n);
    requires !Singleton(n);
    ensures Valid(n);
    ensures Valid(other);
    ensures Singleton(n);
    ensures other.nodes == old(n.nodes[IndexOf(n.nodes,n)+1..]) + old(n.nodes[..IndexOf(n.nodes,n)]);
    modifies n, n.next, n.nodes, n.next.nodes;
  {
    BringToFront(n);
    NonSingletonFacts(n);
    other := n.next;
    assert n.nodes[1] == other; // Observe
    Splice(n, other);
  }
}
