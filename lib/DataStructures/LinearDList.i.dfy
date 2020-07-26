include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"

module DList {
  import opened NativeTypes
  import opened Options
  import opened LinearSequence_s
  import opened LinearSequence_i
  export
    provides NativeTypes
    provides DList
    provides Inv, Seq, ValidPtr, Index, IndexHi
    reveals MaybePtr
    provides Get, Next, Prev
    provides Alloc, Free, Remove, InsertAfter, InsertBefore, Clone

  /*
  A DList<A> is a doubly-linked list that represents a sequence s of type seq<A>.
  It supports efficient insertion and removal but not efficient indexing.
  A pointer p of type int is a pointer to a node in the list.
  The DList is implemented as a mutable sequence of nodes, where nodes[0] is a sentinel.
  */
  datatype Node<A> = Node(data:Option<A>, next:uint64, prev:uint64)
  linear datatype DList<A> = DList(
    linear nodes:seq<Node<A>>, // sequence of nodes held by the list, indexed by pointer p
    freeStack:uint64, // pointer to singly-linked stack of free nodes
    ghost s:seq<A>, // sequence of data values held by the list, indexed by integer index i
    ghost f:seq<int>, // map index to pointer: f[i] = p (where p > 0)
    ghost g:seq<int>  // map pointer to index: g[p] = i (where g[p] == -2 means p is unused and g[0] == -1 (sentinel))
    )

  ghost const unused:int := -2
  ghost const sentinel:int := -1

  predicate PointerInRange<A>(nodes:seq<Node<A>>, f:seq<int>, i:nat)
  requires i < |f|
  {
    0 < f[i] < |nodes|
  }

  lemma RevealPointerInRange<A>(nodes:seq<Node<A>>, f:seq<int>)
  requires forall i :: 0 <= i < |f| ==> PointerInRange(nodes, f, i)
  ensures forall i :: 0 <= i < |f| ==> 0 < f[i] < |nodes|
  {
    forall i | 0 <= i < |f|
    ensures 0 < f[i] < |nodes|
    {
      assert PointerInRange(nodes, f, i);
    }
  }

  predicate Invs<A>(nodes:seq<Node<A>>, freeStack:uint64, s:seq<A>, f:seq<int>, g:seq<int>)
  {
    && |f| == |s|
    && |g| == |nodes|
    && |nodes| > 0
    && g[0] == sentinel
    && 0 <= freeStack as int < |nodes|
    && (forall i :: 0 <= i < |f| ==> PointerInRange(nodes, f, i))
    && (forall i {:trigger g[f[i]]} :: 0 <= i < |f| ==> (
      assert PointerInRange(nodes, f, i);
      g[f[i]] == i
    ))
    && (forall p :: 0 <= p < |g| ==>
      && unused <= g[p] < |s|
      && 0 <= nodes[p].next as int < |g|
      && (g[p] >= 0 <==> nodes[p].data.Some?))
    && (forall p :: 0 <= p < |g| && sentinel <= g[p] ==>
      && (g[p] == sentinel ==> p == 0)
      && (0 <= g[p] ==> f[g[p]] == p && nodes[p].data == Some(s[g[p]]))
      && nodes[p].next as int == (
        if g[p] + 1 < |f| then f[g[p] + 1] // nonlast.next or sentinel.next
        else 0) // last.next == sentinel or sentinel.next == sentinel
      && nodes[p].prev as int == (
        if g[p] > 0 then f[g[p] - 1] // nonfirst.prev
        else if g[p] == 0 || |f| == 0 then 0 // first.prev == sentinel or sentinel.prev == sentinel
        else f[|f| - 1]) // sentinel.prev == last
      && nodes[p].prev as int < |nodes|
      )
  }

  predicate Inv<A>(l:DList<A>)
  {
    Invs(l.nodes, l.freeStack, l.s, l.f, l.g)
  }

  function Seq<A>(l:DList<A>):seq<A>
  {
    l.s
  }

  function ValidPtr<A>(l:DList<A>, p:uint64):(b:bool)
    ensures b ==> p != 0
  {
    0 < p as int < |l.g| && l.g[p] >= 0
  }

  predicate MaybePtr<A>(l:DList<A>, p:uint64)
  {
    p == 0 || ValidPtr(l, p)
  }

  function Index<A>(l:DList<A>, p:uint64):(i:int)
    ensures Inv(l) && ValidPtr(l, p) ==> 0 <= i < |Seq(l)|
    ensures Inv(l) && p == 0 ==> i == -1
  {
    if Inv(l) && MaybePtr(l, p) then l.g[p] else 0
  }

  function IndexHi<A>(l:DList<A>, p:uint64):(i:int)
    ensures Inv(l) && ValidPtr(l, p) ==> i == Index(l, p)
    ensures Inv(l) && p == 0 ==> i == |Seq(l)|
  {
    if Inv(l) && ValidPtr(l, p) then l.g[p] else |l.s|
  }

  function method Get<A>(shared l:DList<A>, p:uint64):(a:A)
    requires Inv(l)
    requires ValidPtr(l, p)
    ensures a == Seq(l)[Index(l, p)]
  {
    seq_get(l.nodes, p).data.value
  }

  function method Next<A>(shared l:DList<A>, p:uint64):(p':uint64)
    requires Inv(l)
    requires MaybePtr(l, p)
    ensures MaybePtr(l, p')
    ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == 0
    ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
    ensures p != 0 && Index(l, p) + 1 < |Seq(l)| ==> Index(l, p') == Index(l, p) + 1
    ensures p != 0 && Index(l, p) + 1 == |Seq(l)| ==> p' == 0
  {
    seq_get(l.nodes, p).next
  }

  function method Prev<A>(shared l:DList<A>, p:uint64):(p':uint64)
    requires Inv(l)
    requires MaybePtr(l, p)
    ensures MaybePtr(l, p')
    ensures p == 0 && |Seq(l)| > 0 ==> Index(l, p') == |Seq(l)| - 1
    ensures p == 0 && |Seq(l)| == 0 ==> p' == 0
    ensures p != 0 && Index(l, p) > 0 ==> Index(l, p') == Index(l, p) - 1
    ensures p != 0 && Index(l, p) == 0 == |Seq(l)| ==> p' == 0
  {
    seq_get(l.nodes, p).prev
  }

  method BuildFreeStack<A>(linear inout a:seq<Node<A>>, k:uint64)
    requires 0 < k as nat <= |old_a|
    ensures |a| == |old_a|
    ensures forall i :: 0 <= i < k as nat ==> a[i] == old_a[i]
    ensures forall i :: k as nat <= i < |old_a| <= 0xffff_ffff_ffff_ffff ==> a[i] == Node(None, i as uint64 - 1, 0)
  {
    var n := k;
    shared_seq_length_bound(a);
    while (n < seq_length(a))
      invariant k as int <= n as int <= |a|
      invariant |a| == |old_a| //?
      invariant forall i :: 0 <= i < k as nat ==> a[i] == old_a[i]
      invariant forall i :: k as nat <= i < n as nat ==> a[i] == Node(None, i as uint64 - 1, 0)
    {
      mut_seq_set(inout a, n, Node(None, n - 1, 0));
      n := n + 1;
    }
  }

  // initial_len should be the initial capacity plus 1
  method Alloc<A>(initial_len:uint64) returns(linear l:DList<A>)
    requires initial_len > 0
    ensures Inv(l)
    ensures Seq(l) == []
  {
    linear var nodes := seq_alloc<Node>(initial_len, Node(None, 0, 0));
    BuildFreeStack(inout nodes, 1);
    l := DList(nodes, initial_len - 1, [], [], seq(initial_len as nat, p => if p == 0 then sentinel else unused));
  }

  method Free<A>(linear l:DList<A>)
  {
    linear var DList(nodes, freeStack, s, f, g) := l;
    var _ := seq_free(nodes);
  }

  predicate PointerToIndexUnchanged<A>(old_l: DList<A>, l: DList<A>, x: uint64)
  requires ValidPtr(old_l, x)
  {
    && ValidPtr(l, x)
    && l.g[x] == old_l.g[x]
  }

  method Expand<A>(linear inout l:DList<A>)
    requires Inv(old_l)
    ensures Inv(l)
    ensures l.s == old_l.s
    ensures forall x :: ValidPtr(old_l, x) ==> PointerToIndexUnchanged(old_l, l, x)
    ensures l.freeStack != 0 && l.nodes[l.freeStack].data.None?
  {
    shared_seq_length_bound(l.nodes);
    var len := seq_length(l.nodes);
    shared_seq_length_bound(l.nodes);
    var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
    var s := l.freeStack;
    SeqResizeMut(inout l.nodes, len', Node(None, s, 0));
    BuildFreeStack(inout l.nodes, len + 1);
    
    inout l.freeStack := len' - 1;
    inout ghost l.g := seq(|l.nodes|, i requires 0 <= i < |l.nodes| => if i < |l.g| then l.g[i] else unused);

    forall i | 0 <= i < |l.f|
    ensures PointerInRange(l.nodes, l.f, i)
    {
      assert PointerInRange(old_l.nodes, old_l.f, i); // observe
    }
    
    RevealPointerInRange(old_l.nodes, old_l.f);
    RevealPointerInRange(l.nodes, l.f);
  }

  method Remove<A>(linear inout l:DList<A>, p:uint64)
    requires Inv(old_l)
    requires ValidPtr(old_l, p)
    ensures Inv(l)
    ensures Seq(l) == Seq(old_l)[.. Index(old_l, p)] + Seq(old_l)[Index(old_l, p) + 1 ..]
    ensures forall x :: x != p && ValidPtr(old_l, x) ==>
      ValidPtr(l, x) && Index(l, x) == Index(old_l, x) - (if Index(old_l, x) < Index(old_l, p) then 0 else 1)
  {
    ghost var index := l.g[p];
    ghost var s' := l.s[.. index] + l.s[index + 1 ..];
    ghost var f' := l.f[.. index] + l.f[index + 1 ..];
    ghost var g' := seq(|l.g|, x requires 0 <= x < |l.g| =>
      if l.g[x] == index then unused else if l.g[x] > index then l.g[x] - 1 else l.g[x]);

    var freeStack := l.freeStack;

    var node := seq_get(l.nodes, p);
    var node_prev := seq_get(l.nodes, node.prev);
    mut_seq_set(inout l.nodes, node.prev, node_prev.(next := node.next));
    var node_next := seq_get(l.nodes, node.next);
    mut_seq_set(inout l.nodes, node.next, node_next.(prev := node.prev));
    mut_seq_set(inout l.nodes, p, Node(None, freeStack, 0));

    inout l.freeStack := p;
    inout ghost l.s := s';
    inout ghost l.f := f';
    inout ghost l.g := g';

    forall i | 0 <= i < |l.f|
    ensures PointerInRange(l.nodes, l.f, i)
    ensures 0 < l.f[i] < |l.nodes|
    {
      if i < index {
        assert PointerInRange(old_l.nodes, old_l.f, i); // observe
      } else {
        assert PointerInRange(old_l.nodes, old_l.f, i + 1); // observe
      }
    }
  }

  method InsertAfter<A>(linear inout l:DList<A>, p:uint64, a:A) returns (p':uint64)
    requires Inv(old_l)
    requires MaybePtr(old_l, p)
    ensures Inv(l)
    ensures Seq(l) == Seq(old_l)[.. Index(old_l, p) + 1] + [a] + Seq(old_l)[Index(old_l, p) + 1 ..]
    ensures ValidPtr(l, p') && Index(l, p') == Index(old_l, p) + 1
    ensures forall x :: ValidPtr(old_l, x) ==>
      ValidPtr(l, x) && Index(l, x) == Index(old_l, x) + (if Index(old_l, x) <= Index(old_l, p) then 0 else 1)
  {
    p' := l.freeStack;
    var freeNode := seq_get(l.nodes, p');
    if (p' == 0 || freeNode.data.Some?) {
      Expand(inout l);
      p' := l.freeStack;
      freeNode := seq_get(l.nodes, p');
    }

    ghost var lExpanded := l;

    forall i | 0 <= i < |lExpanded.f|
    ensures PointerInRange(lExpanded.nodes, lExpanded.f, i)
    {
      assert PointerInRange(l.nodes, l.f, i); // observe
    }

    ghost var lBefore := l;

    // linear var DList(nodes, freeStack, s, f, g) := l';
    ghost var index := l.g[p];
    ghost var index' := index + 1;
    inout ghost l.s := lBefore.s[.. index'] + [a] + lBefore.s[index' ..];
    inout ghost l.f := lBefore.f[.. index'] + [p' as int] + lBefore.f[index' ..];
    inout ghost l.g := seq(|l.g|, x requires 0 <= x < |l.g| =>
      if x == p' as int then index' else if l.g[x] > index then l.g[x] + 1 else l.g[x]);
    var node := seq_get(l.nodes, p);
    var node' := Node(Some(a), node.next, p);
    mut_seq_set(inout l.nodes, p, node.(next := p'));
    var node_next := seq_get(l.nodes, node.next);
    mut_seq_set(inout l.nodes, node.next, node_next.(prev := p'));
    mut_seq_set(inout l.nodes, p', node');

    forall i | 0 <= i < |l.f|
    ensures PointerInRange(l.nodes, l.f, i)
    {
      if i < index {
        assert PointerInRange(lExpanded.nodes, lExpanded.f, i); // observe
      } else if i == index {
      } else if (i as int - 1 >= 0) {
        assert PointerInRange(lExpanded.nodes, lExpanded.f, i - 1); // observe
      }
    }

    assert Inv(l) by {
      RevealPointerInRange(lBefore.nodes, lBefore.f);
      RevealPointerInRange(l.nodes, l.f);
    }
  }

  method InsertBefore<A>(linear inout l:DList<A>, p:uint64, a:A) returns(p':uint64)
    requires Inv(old_l)
    requires MaybePtr(old_l, p)
    ensures Inv(l)
    ensures Seq(l) == Seq(old_l)[.. IndexHi(old_l, p)] + [a] + Seq(old_l)[IndexHi(old_l, p) ..]
    ensures ValidPtr(l, p') && Index(l, p') == IndexHi(old_l, p)
    ensures forall x :: ValidPtr(old_l, x) ==>
      ValidPtr(l, x) && Index(l, x) == Index(old_l, x) + (if Index(old_l, x) < IndexHi(old_l, p) then 0 else 1)
  {
    //l' := l;
    p' := l.freeStack;
    var freeNode := seq_get(l.nodes, p');
    if (p' == 0 || freeNode.data.Some?) {
      Expand(inout l);
      p' := l.freeStack;
      freeNode := seq_get(l.nodes, p');
    }

    ghost var lExpanded := l;

    forall i | 0 <= i < |lExpanded.f|
    ensures PointerInRange(lExpanded.nodes, lExpanded.f, i)
    {
      assert PointerInRange(l.nodes, l.f, i); // observe
    }

    ghost var lBefore := l;

    //linear var DList(nodes, freeStack, s, f, g) := l';
    ghost var index' := IndexHi(l, p);
    inout ghost l.s := lBefore.s[.. index'] + [a] + lBefore.s[index' ..];
    inout ghost l.f := l.f[.. index'] + [p' as int] + l.f[index' ..];
    inout ghost l.g := seq(|l.g|, x requires 0 <= x < |l.g| =>
      if x == p' as int then index' else if l.g[x] >= index' then l.g[x] + 1 else l.g[x]);
    var node := seq_get(l.nodes, p);
    var node' := Node(Some(a), p, node.prev);
    mut_seq_set(inout l.nodes, p, node.(prev := p'));
    var node_prev := seq_get(l.nodes, node.prev);
    mut_seq_set(inout l.nodes, node.prev, node_prev.(next := p'));
    mut_seq_set(inout l.nodes, p', node');

    forall i | 0 <= i < |l.f|
    ensures PointerInRange(l.nodes, l.f, i)
    {
      if i < index' {
        assert PointerInRange(lExpanded.nodes, lExpanded.f, i); // observe
      } else if i == index' {
      } else {
        assert PointerInRange(lExpanded.nodes, lExpanded.f, i - 1); // observe
      }
    }

    assert Inv(l) by {
      forall i | 0 <= i < |l.f|
      ensures (
        assert PointerInRange(l.nodes, l.f, i);
        l.g[l.f[i]] == i
      )
      {
        if i == index' {
        }
      }
    }
  }

  method Clone<A>(shared l:DList<A>) returns(linear l':DList<A>)
    ensures l' == l
  {
    shared var DList(nodes, freeStack, s, f, g) := l;
    shared_seq_length_bound(nodes);
    linear var nodes' := AllocAndCopy(nodes, 0, seq_length(nodes));
    l' := DList(nodes', freeStack, s, f, g);
  }
}

/*
module Test
{
  import opened NativeTypes
  import opened DList

  method main()
  {
    linear var l := Alloc<uint64>(3);
    var p;
    l, p := InsertAfter(l, 0, 100);
    l, p := InsertAfter(l, p, 200);
    l, p := InsertAfter(l, p, 300);
    var p3 := p;
    l, p := InsertAfter(l, p, 400);
    l, p := InsertAfter(l, p, 500);
    assert Seq(l) == [100, 200, 300, 400, 500];
    l := Remove(l, p3);
    assert Seq(l) == [100, 200, 400, 500];
    l, p := InsertAfter(l, p, 600);
    l, p := InsertAfter(l, p, 700);
    assert Seq(l) == [100, 200, 400, 500, 600, 700];
    Free(l);
  }
}
*/
