/*
If Z3 fails to verify this file, try these Dafny options:
  /noNLarith /proverOpt:OPTIMIZE_FOR_BV=true /z3opt:smt.PHASE_SELECTION=0 /z3opt:smt.RESTART_STRATEGY=0 /z3opt:smt.RESTART_FACTOR=1.5 /z3opt:smt.ARITH.RANDOM_INITIAL_VALUE=true /z3opt:smt.CASE_SPLIT=1
Explanation:
  Dafny/Boogie sets smt.CASE_SPLIT=3, which seems good in general, but makes this file unstable.
  Z3's default is smt.CASE_SPLIT=1.
  There's no direct way to override the smt.CASE_SPLIT=3, but /proverOpt:OPTIMIZE_FOR_BV=true blocks it,
  along with a bunch of other options (e.g. smt.PHASE_SELECTION=0);
  these other options then must be restored manually, as shown above.
*/

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

  predicate Invs<A>(nodes:seq<Node<A>>, freeStack:uint64, s:seq<A>, f:seq<int>, g:seq<int>)
  {
    && |f| == |s|
    && |g| == |nodes|
    && |nodes| > 0
    && g[0] == sentinel
    && 0 <= freeStack as int < |nodes|
    && (forall i :: 0 <= i < |f| ==> 0 < f[i] < |nodes|)
    && (forall i {:trigger g[f[i]]} :: 0 <= i < |f| ==> g[f[i]] == i)
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

  method BuildFreeStack<A>(linear a:seq<Node<A>>, k:uint64) returns(linear b:seq<Node<A>>)
    requires 0 < k as nat <= |a|
    ensures |b| == |a|
    ensures forall i :: 0 <= i < k as nat ==> b[i] == a[i]
    ensures forall i :: k as nat <= i < |a| <= 0xffff_ffff_ffff_ffff ==> b[i] == Node(None, i as uint64 - 1, 0)
  {
    b := a;
    var n := k;
    shared_seq_length_bound(b);
    while (n < seq_length(b))
      invariant k as int <= n as int <= |b|
      invariant |b| == |a|
      invariant forall i :: 0 <= i < k as nat ==> b[i] == a[i]
      invariant forall i :: k as nat <= i < n as nat ==> b[i] == Node(None, i as uint64 - 1, 0)
    {
      b := seq_set(b, n, Node(None, n - 1, 0));
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
    nodes := BuildFreeStack(nodes, 1);
    l := DList(nodes, initial_len - 1, [], [], seq(initial_len as nat, p => if p == 0 then sentinel else unused));
  }

  method Free<A>(linear l:DList<A>)
  {
    linear var DList(nodes, freeStack, s, f, g) := l;
    var _ := seq_free(nodes);
  }

  method Expand<A>(linear l:DList<A>) returns(linear l':DList<A>)
    requires Inv(l)
    ensures Inv(l')
    ensures l'.s == l.s
    ensures forall x :: ValidPtr(l, x) ==> ValidPtr(l', x) && l'.g[x] == l.g[x]
    ensures l'.freeStack != 0 && l'.nodes[l'.freeStack].data.None?
  {
    linear var DList(nodes, freeStack, s, f, g) := l;
    shared_seq_length_bound(nodes);
    var len := seq_length(nodes);
    shared_seq_length_bound(nodes);
    var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
    nodes := SeqResize(nodes, len', Node(None, freeStack, 0));
    nodes := BuildFreeStack(nodes, len + 1);
    l' := DList(nodes, len' - 1, s, f, seq(|nodes|,
      i requires 0 <= i < |nodes| => if i < |g| then g[i] else unused));
  }

  method Remove<A>(linear l:DList<A>, p:uint64) returns(linear l':DList<A>)
    requires Inv(l)
    requires ValidPtr(l, p)
    ensures Inv(l')
    ensures Seq(l') == Seq(l)[.. Index(l, p)] + Seq(l)[Index(l, p) + 1 ..]
    ensures forall x :: x != p && ValidPtr(l, x) ==>
      ValidPtr(l', x) && Index(l', x) == Index(l, x) - (if Index(l, x) < Index(l, p) then 0 else 1)
  {
    linear var DList(nodes, freeStack, s, f, g) := l;
    ghost var index := g[p];
    ghost var s' := s[.. index] + s[index + 1 ..];
    ghost var f' := f[.. index] + f[index + 1 ..];
    ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
      if g[x] == index then unused else if g[x] > index then g[x] - 1 else g[x]);

    var node := seq_get(nodes, p);
    var node_prev := seq_get(nodes, node.prev);
    nodes := seq_set(nodes, node.prev, node_prev.(next := node.next));
    var node_next := seq_get(nodes, node.next);
    nodes := seq_set(nodes, node.next, node_next.(prev := node.prev));
    nodes := seq_set(nodes, p, Node(None, freeStack, 0));
    l' := DList(nodes, p, s', f', g');
  }

  method InsertAfter<A>(linear l:DList<A>, p:uint64, a:A) returns(linear l':DList<A>, p':uint64)
    requires Inv(l)
    requires MaybePtr(l, p)
    ensures Inv(l')
    ensures Seq(l') == Seq(l)[.. Index(l, p) + 1] + [a] + Seq(l)[Index(l, p) + 1 ..]
    ensures ValidPtr(l', p') && Index(l', p') == Index(l, p) + 1
    ensures forall x :: ValidPtr(l, x) ==>
      ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) <= Index(l, p) then 0 else 1)
  {
    l' := l;
    p' := l'.freeStack;
    var freeNode := seq_get(l'.nodes, p');
    if (p' == 0 || freeNode.data.Some?) {
      l' := Expand(l');
      p' := l'.freeStack;
      freeNode := seq_get(l'.nodes, p');
    }

    linear var DList(nodes, freeStack, s, f, g) := l';
    ghost var index := g[p];
    ghost var index' := index + 1;
    ghost var s' := s[.. index'] + [a] + s[index' ..];
    ghost var f' := f[.. index'] + [p' as int] + f[index' ..];
    ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
      if x == p' as int then index' else if g[x] > index then g[x] + 1 else g[x]);
    var node := seq_get(nodes, p);
    var node' := Node(Some(a), node.next, p);
    nodes := seq_set(nodes, p, node.(next := p'));
    var node_next := seq_get(nodes, node.next);
    nodes := seq_set(nodes, node.next, node_next.(prev := p'));
    nodes := seq_set(nodes, p', node');
    l' := DList(nodes, freeNode.next, s', f', g');
  }

  method InsertBefore<A>(linear l:DList<A>, p:uint64, a:A) returns(linear l':DList<A>, p':uint64)
    requires Inv(l)
    requires MaybePtr(l, p)
    ensures Inv(l')
    ensures Seq(l') == Seq(l)[.. IndexHi(l, p)] + [a] + Seq(l)[IndexHi(l, p) ..]
    ensures ValidPtr(l', p') && Index(l', p') == IndexHi(l, p)
    ensures forall x :: ValidPtr(l, x) ==>
      ValidPtr(l', x) && Index(l', x) == Index(l, x) + (if Index(l, x) < IndexHi(l, p) then 0 else 1)
  {
    l' := l;
    p' := l'.freeStack;
    var freeNode := seq_get(l'.nodes, p');
    if (p' == 0 || freeNode.data.Some?) {
      l' := Expand(l');
      p' := l'.freeStack;
      freeNode := seq_get(l'.nodes, p');
    }

    linear var DList(nodes, freeStack, s, f, g) := l';
    ghost var index' := IndexHi(l, p);
    ghost var s' := s[.. index'] + [a] + s[index' ..];
    ghost var f' := f[.. index'] + [p' as int] + f[index' ..];
    ghost var g' := seq(|g|, x requires 0 <= x < |g| =>
      if x == p' as int then index' else if g[x] >= index' then g[x] + 1 else g[x]);
    var node := seq_get(nodes, p);
    var node' := Node(Some(a), p, node.prev);
    nodes := seq_set(nodes, p, node.(prev := p'));
    var node_prev := seq_get(nodes, node.prev);
    nodes := seq_set(nodes, node.prev, node_prev.(next := p'));
    nodes := seq_set(nodes, p', node');
    l' := DList(nodes, freeNode.next, s', f', g');
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
