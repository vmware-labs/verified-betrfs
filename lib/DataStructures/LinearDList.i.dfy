// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"

/*
In a test of 100 random seeds:
- this file, as is, succeeded 82 times
- with the (commented-out) PointerInRange edits, it succeeded 84 times
- with /proverOpt:O:smt.case_split=1, which had helped with earlier Dafny/Boogie/Z3, only 57 times
The problem seems to be with Z3 not instantiating quantifiers in some cases.
*/

module DList {
  import opened NativeTypes
  import opened Options
  import opened LinearSequence_s
  import opened LinearSequence_i
  export
    provides NativeTypes
    provides Options
    reveals Node
    // TODO "provides" DList once https://github.com/dafny-lang/dafny/issues/757 is fixed
    reveals DList
    provides DList.Inv, DList.Seq, DList.ValidPtr, DList.Index, DList.IndexHi
    reveals DList.MaybePtr
    provides DList.Get, DList.Next, DList.Prev
    provides DList.Alloc, DList.Free, DList.Remove, DList.InsertAfter, DList.InsertBefore, DList.Clone

  /*
  A DList<A> is a doubly-linked list that represents a sequence s of type seq<A>.
  It supports efficient insertion and removal but not efficient indexing.
  A pointer p of type int is a pointer to a node in the list.
  The DList is implemented as a mutable sequence of nodes, where nodes[0] is a sentinel.
  */
  datatype Node<A> = Node(data:Option<A>, next:uint64, prev:uint64)

  ghost const unused:int := -2
  ghost const sentinel:int := -1

//  predicate PointerInRange<A>(nodes:seq<Node<A>>, f:seq<int>, i:nat)
//  requires i < |f|
//  {
//    0 < f[i] < |nodes|
//  }
//
//  lemma RevealPointerInRange<A>(nodes:seq<Node<A>>, f:seq<int>)
//  requires forall i :: 0 <= i < |f| ==> PointerInRange(nodes, f, i)
//  ensures forall i :: 0 <= i < |f| ==> 0 < f[i] < |nodes|
//  {
//    forall i | 0 <= i < |f|
//    ensures 0 < f[i] < |nodes|
//    {
//      assert PointerInRange(nodes, f, i);
//    }
//  }

  predicate Invs<A>(nodes:seq<Node<A>>, freeStack:uint64, s:seq<A>, f:seq<int>, g:seq<int>)
  {
    && |f| == |s|
    && |g| == |nodes|
    && |nodes| > 0
    && g[0] == sentinel
    && 0 <= freeStack as int < |nodes|
    && (forall i {:trigger f[i]} :: 0 <= i < |f| ==> 0 < f[i] < |nodes|) // (forall i :: 0 <= i < |f| ==> PointerInRange(nodes, f, i))
    && (forall i {:trigger g[f[i]]} :: 0 <= i < |f| ==> (
//      assert PointerInRange(nodes, f, i);
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

  linear datatype DList<A> = DList(
    linear nodes:seq<Node<A>>, // sequence of nodes held by the list, indexed by pointer p
    freeStack:uint64, // pointer to singly-linked stack of free nodes
    ghost s:seq<A>, // sequence of data values held by the list, indexed by integer index i
    ghost f:seq<int>, // map index to pointer: f[i] = p (where p > 0)
    ghost g:seq<int>  // map pointer to index: g[p] = i (where g[p] == -2 means p is unused and g[0] == -1 (sentinel))
    )
  {
    predicate Inv()
    {
      Invs(this.nodes, this.freeStack, this.s, this.f, this.g)
    }

    function Seq():seq<A>
    {
      this.s
    }

    function ValidPtr(p:uint64):(b:bool)
      ensures b ==> p != 0
    {
      0 < p as int < |this.g| && this.g[p] >= 0
    }

    predicate MaybePtr(p:uint64)
    {
      p == 0 || this.ValidPtr(p)
    }

    function Index(p:uint64):(i:int)
      ensures this.Inv() && this.ValidPtr(p) ==> 0 <= i < |this.Seq()|
      ensures this.Inv() && p == 0 ==> i == -1
    {
      if this.Inv() && this.MaybePtr(p) then this.g[p] else 0
    }

    function IndexHi(p:uint64):(i:int)
      ensures this.Inv() && this.ValidPtr(p) ==> i == this.Index(p)
      ensures this.Inv() && p == 0 ==> i == |this.Seq()|
    {
      if this.Inv() && this.ValidPtr(p) then this.g[p] else |this.s|
    }

    shared function method Get(p:uint64):(a:A)
      requires this.Inv()
      requires this.ValidPtr(p)
      ensures a == this.Seq()[this.Index(p)]
    {
      seq_get(this.nodes, p).data.value
    }

    shared function method Next(p:uint64):(p':uint64)
      requires this.Inv()
      requires this.MaybePtr( p)
      ensures this.MaybePtr(p')
      ensures p == 0 && |this.Seq()| > 0 ==> this.Index(p') == 0
      ensures p == 0 && |this.Seq()| == 0 ==> p' == 0
      ensures p != 0 && this.Index(p) + 1 < |this.Seq()| ==> this.Index(p') == this.Index(p) + 1
      ensures p != 0 && this.Index(p) + 1 == |this.Seq()| ==> p' == 0
    {
      seq_get(this.nodes, p).next
    }

    shared function method Prev<A>(p:uint64):(p':uint64)
      requires this.Inv()
      requires this.MaybePtr(p)
      ensures this.MaybePtr(p')
      ensures p == 0 && |this.Seq()| > 0 ==> this.Index(p') == |this.Seq()| - 1
      ensures p == 0 && |this.Seq()| == 0 ==> p' == 0
      ensures p != 0 && this.Index(p) > 0 ==> this.Index(p') == this.Index(p) - 1
      ensures p != 0 && this.Index(p) == 0 == |this.Seq()| ==> p' == 0
    {
      seq_get(this.nodes, p).prev
    }

    static method BuildFreeStack(linear inout a:seq<Node<A>>, k:uint64)
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
    static method Alloc(initial_len:uint64) returns(linear l:DList<A>)
      requires initial_len > 0
      ensures l.Inv()
      ensures l.Seq() == []
    {
      linear var nodes := seq_alloc<Node>(initial_len, Node(None, 0, 0));
      BuildFreeStack(inout nodes, 1);
      l := DList(nodes, initial_len - 1, [], [], seq(initial_len as nat, p => if p == 0 then sentinel else unused));
    }

    linear method Free()
    {
      linear var DList(nodes, freeStack, s, f, g) := this;
      var _ := seq_free(nodes);
    }

    static predicate PointerToIndexUnchanged<A>(old_l: DList<A>, l: DList<A>, x: uint64)
    requires old_l.ValidPtr(x)
    {
      && l.ValidPtr(x)
      && l.g[x] == old_l.g[x]
    }

    // TODO(andrea) with new syntax: self -> this
    linear inout method Expand()
      requires old_self.Inv()
      ensures self.Inv()
      ensures self.s == old_self.s
      ensures forall x :: old_self.ValidPtr(x) ==> PointerToIndexUnchanged(old_self, self, x)
      ensures self.freeStack != 0 && self.nodes[self.freeStack].data.None?
    {
      shared_seq_length_bound(self.nodes);
      var len := seq_length(self.nodes);
      shared_seq_length_bound(self.nodes);
      var len' := if len < 0x7fff_ffff_ffff_ffff then len + len else len + 1;
      var s := self.freeStack;
      SeqResizeMut(inout self.nodes, len', Node(None, s, 0));
      BuildFreeStack(inout self.nodes, len + 1);
      
      inout self.freeStack := len' - 1;
      inout ghost self.g := seq(|self.nodes|, i requires 0 <= i < |self.nodes| => if i < |self.g| then self.g[i] else unused);

//      forall i | 0 <= i < |self.f|
//      ensures PointerInRange(self.nodes, self.f, i)
//      {
//        assert PointerInRange(old_self.nodes, old_self.f, i); // observe
//      }
//      
//      RevealPointerInRange(old_self.nodes, old_self.f);
//      RevealPointerInRange(self.nodes, self.f);
    }

    linear inout method Remove(p:uint64)
      requires old_self.Inv()
      requires old_self.ValidPtr(p)
      ensures self.Inv()
      ensures self.Seq() == old_self.Seq()[.. old_self.Index(p)] + old_self.Seq()[old_self.Index(p) + 1 ..]
      ensures forall x :: x != p && old_self.ValidPtr(x) ==>
        self.ValidPtr(x) && self.Index(x) == old_self.Index(x) - (if old_self.Index(x) < old_self.Index(p) then 0 else 1)
    {
      ghost var index := self.g[p];
      ghost var s' := self.s[.. index] + self.s[index + 1 ..];
      ghost var f' := self.f[.. index] + self.f[index + 1 ..];
      ghost var g' := seq(|self.g|, x requires 0 <= x < |self.g| =>
        if self.g[x] == index then unused else if self.g[x] > index then self.g[x] - 1 else self.g[x]);

      var freeStack := self.freeStack;

      var node := seq_get(self.nodes, p);
      var node_prev := seq_get(self.nodes, node.prev);
      mut_seq_set(inout self.nodes, node.prev, node_prev.(next := node.next));
      var node_next := seq_get(self.nodes, node.next);
      mut_seq_set(inout self.nodes, node.next, node_next.(prev := node.prev));
      mut_seq_set(inout self.nodes, p, Node(None, freeStack, 0));

      inout self.freeStack := p;
      inout ghost self.s := s';
      inout ghost self.f := f';
      inout ghost self.g := g';

//      forall i | 0 <= i < |self.f|
//      ensures PointerInRange(self.nodes, self.f, i)
//      ensures 0 < self.f[i] < |self.nodes|
//      {
//        if i < index {
//          assert PointerInRange(old_self.nodes, old_self.f, i); // observe
//        } else {
//          assert PointerInRange(old_self.nodes, old_self.f, i + 1); // observe
//        }
//      }
    }

    linear inout method InsertAfter(p:uint64, a:A) returns (p':uint64)
      requires old_self.Inv()
      requires old_self.MaybePtr(p)
      ensures self.Inv()
      ensures self.Seq() == old_self.Seq()[.. old_self.Index(p) + 1] + [a] + old_self.Seq()[old_self.Index(p) + 1 ..]
      ensures self.ValidPtr(p') && self.Index(p') == old_self.Index(p) + 1
      ensures forall x :: old_self.ValidPtr(x) ==>
        self.ValidPtr(x) && self.Index(x) == old_self.Index(x) + (if old_self.Index(x) <= old_self.Index(p) then 0 else 1)
    {
      p' := self.freeStack;
      var freeNode := seq_get(self.nodes, p');
      if (p' == 0 || freeNode.data.Some?) {
        inout self.Expand();
        p' := self.freeStack;
        freeNode := seq_get(self.nodes, p');
      }

      ghost var selfBefore := self;

//      forall i | 0 <= i < |selfBefore.f|
//      ensures PointerInRange(selfBefore.nodes, selfBefore.f, i)
//      {
//        assert PointerInRange(self.nodes, self.f, i); // observe
//      }

      // linear var DList(nodes, freeStack, s, f, g) := l';
      ghost var index := self.g[p];
      ghost var index' := index + 1;
      inout ghost self.s := selfBefore.s[.. index'] + [a] + selfBefore.s[index' ..];
      inout ghost self.f := selfBefore.f[.. index'] + [p' as int] + selfBefore.f[index' ..];
      inout ghost self.g := seq(|self.g|, x requires 0 <= x < |self.g| =>
        if x == p' as int then index' else if self.g[x] > index then self.g[x] + 1 else self.g[x]);
      var node := seq_get(self.nodes, p);
      var node' := Node(Some(a), node.next, p);
      mut_seq_set(inout self.nodes, p, node.(next := p'));
      var node_next := seq_get(self.nodes, node.next);
      mut_seq_set(inout self.nodes, node.next, node_next.(prev := p'));
      mut_seq_set(inout self.nodes, p', node');

//      forall i | 0 <= i < |self.f|
//      ensures PointerInRange(self.nodes, self.f, i)
//      {
//        if i < index {
//          assert PointerInRange(selfBefore.nodes, selfBefore.f, i); // observe
//        } else if i == index {
//        } else if (i as int - 1 >= 0) {
//          assert PointerInRange(selfBefore.nodes, selfBefore.f, i - 1); // observe
//        }
//      }
//
//      assert self.Inv() by {
//        RevealPointerInRange(selfBefore.nodes, selfBefore.f);
//        RevealPointerInRange(self.nodes, self.f);
//      }
    }

    linear inout method InsertBefore(p:uint64, a:A) returns(p':uint64)
      requires old_self.Inv()
      requires old_self.MaybePtr(p)
      ensures self.Inv()
      ensures self.Seq() == old_self.Seq()[.. old_self.IndexHi(p)] + [a] + old_self.Seq()[old_self.IndexHi(p) ..]
      ensures self.ValidPtr(p') && self.Index(p') == old_self.IndexHi(p)
      ensures forall x :: old_self.ValidPtr(x) ==>
        self.ValidPtr(x) && self.Index(x) == old_self.Index(x) + (if old_self.Index(x) < old_self.IndexHi(p) then 0 else 1)
    {
      //l' := l;
      p' := self.freeStack;
      var freeNode := seq_get(self.nodes, p');
      if (p' == 0 || freeNode.data.Some?) {
        inout self.Expand();
        p' := self.freeStack;
        freeNode := seq_get(self.nodes, p');
      }

      ghost var selfBefore := self;

//      forall i | 0 <= i < |selfBefore.f|
//      ensures PointerInRange(selfBefore.nodes, selfBefore.f, i)
//      {
//        assert PointerInRange(self.nodes, self.f, i); // observe
//      }

      //linear var DList(nodes, freeStack, s, f, g) := l';
      ghost var index' := self.IndexHi(p);
      inout ghost self.s := selfBefore.s[.. index'] + [a] + selfBefore.s[index' ..];
      inout ghost self.f := self.f[.. index'] + [p' as int] + self.f[index' ..];
      inout ghost self.g := seq(|self.g|, x requires 0 <= x < |self.g| =>
        if x == p' as int then index' else if self.g[x] >= index' then self.g[x] + 1 else self.g[x]);
      var node := seq_get(self.nodes, p);
      var node' := Node(Some(a), p, node.prev);
      mut_seq_set(inout self.nodes, p, node.(prev := p'));
      var node_prev := seq_get(self.nodes, node.prev);
      mut_seq_set(inout self.nodes, node.prev, node_prev.(next := p'));
      mut_seq_set(inout self.nodes, p', node');

//      forall i | 0 <= i < |self.f|
//      ensures PointerInRange(self.nodes, self.f, i)
//      {
//        if i < index' {
//          assert PointerInRange(selfBefore.nodes, selfBefore.f, i); // observe
//        } else if i == index' {
//        } else {
//          assert PointerInRange(selfBefore.nodes, selfBefore.f, i - 1); // observe
//        }
//      }
//
//      assert self.Inv() by {
//        forall i | 0 <= i < |self.f|
//        ensures (
//          assert PointerInRange(self.nodes, self.f, i);
//          self.g[self.f[i]] == i
//        )
//        {
//          if i == index' {
//          }
//        }
//      }
    }

    shared method Clone() returns(linear l':DList<A>)
      ensures l' == this
    {
      shared var DList(nodes, freeStack, s, f, g) := this;
      shared_seq_length_bound(nodes);
      linear var nodes' := AllocAndCopy(nodes, 0, seq_length(nodes));
      l' := DList(nodes', freeStack, s, f, g);
    }
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
