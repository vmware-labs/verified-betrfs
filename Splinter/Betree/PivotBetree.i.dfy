// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"
include "../../lib/Base/total_order.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"

module PivotBetree
{
  import opened Options
  import opened KeyType
  import opened StampedMapMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import PagedBetree
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
//  import opened Lexicographic_Byte_Order
  import opened BoundedPivotsLib

  datatype TransitionLabel =
  
    QueryLabel(endLsn: LSN, key: Key, value: Value)
  | PutLabel(puts: MsgHistory)
  | QueryEndLsnLabel(endLsn: LSN)
  | FreezeAsLabel(/*stampedBetree: StampedBetree*/)
  | InternalLabel()

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  // end is exclusive
  datatype Domain = EmptyDomain | Domain(start: Element, end: Element)
  {
    predicate WF() {
      && (!EmptyDomain? ==>
          && lt(start, end)
          && start.Element?
          && ElementIsKey(start)
          && (end.Element? ==> ElementIsKey(end))
        )
    }

    predicate Contains(key: Key) {
      && !EmptyDomain?
      && lte(start, Element(key))
      && lt(Element(key), end)
    }

    function IntersectInner(r2: Domain) : Domain
      requires Domain?
      requires r2.Domain?
      requires lte(start, r2.start)
    {
      if lte(end, r2.start)
      then EmptyDomain
      else if lt(end, r2.end)
      then Domain(r2.start, end)
      else Domain(r2.start, r2.end)
    }

    function Intersect(r2: Domain) : Domain
    {
      if EmptyDomain? || r2.EmptyDomain?
      then this
      else if lte(start, r2.start)
      then this.IntersectInner(r2)
      else r2.IntersectInner(this)
    }
  }

  datatype Buffer = Buffer(filter: Domain, mapp: map<Key, Message>)
  {
    predicate WF() {
      true  // TODO Gonna need fancier filter here, and that'll need WF
    }

    function Query(key: Key) : Message
    {
      if filter.Contains(key) && key in mapp
      then mapp[key]
      else Update(NopDelta())
    }

    function ApplyFilter(accept: Domain) : Buffer
    {
      Buffer(filter.Intersect(accept), mapp)
    }
  }
 
  predicate AnyKey(key: Key) { true }

  // TODO(jonh): Much of this module is identical copy-paste from PagedBetree.
  // Is there a non-fonky way to avoid it? Would fonky (module refinement) be so bad?
  // (Generics isn't sufficient, because BufferStack needs to know certain
  // methods exist inside Buffer.)
  datatype BufferStack = BufferStack(buffers: seq<Buffer>)
  {
    predicate WF() {
      forall i | 0<=i<|buffers| :: buffers[i].WF()
    }

    function QueryUpTo(key: Key, count: nat) : Message
      requires count <= |buffers|
    {
      if count == 0 then Update(NopDelta())
      else Merge(QueryUpTo(key, count-1), buffers[count-1].Query(key))
    }

    function Query(key: Key) : Message
    {
      QueryUpTo(key, |buffers|)
    }

    function ApplyFilter(accept: Domain) : BufferStack
    {
      BufferStack(seq(|buffers|, i requires 0<=i<|buffers| => buffers[i].ApplyFilter(accept)))
    }

    function PrependBufferStack(newBuffers: BufferStack) : BufferStack
    {
      BufferStack(newBuffers.buffers + this.buffers)
    }

    predicate Equivalent(other: BufferStack)
    {
      forall k | AnyKey(k) :: Query(k) == other.Query(k)
    }
  }

  datatype BetreeNode = Nil | BetreeNode(
    buffers: BufferStack,
    pivotTable: PivotTable,
    children: seq<BetreeNode>)
  {
    predicate WF() {
      && (BetreeNode? ==>
          && buffers.WF()
          && WFPivots(pivotTable)
          && |children| == NumBuckets(pivotTable)
          && (forall i:nat | i<|children| :: children[i].WF())
        )
    }

    function PrependBufferStack(bufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers.PrependBufferStack(bufferStack), pivotTable, children)
    }

    function ApplyFilter(filter: Domain) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      if Nil? then Nil else
      var out := BetreeNode(buffers.ApplyFilter(filter), pivotTable, children);
      out
    }

    // TODO(jonh): Split shouldn't also Grow; that's a separate operation.
    function Split(childIdx: nat, splitKey: Key) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      requires PivotInsertable(pivotTable, childIdx, splitKey)
      requires 0 < childIdx < NumBuckets(pivotTable) // Can't extend domain of this node via split.
      requires BetreeNode?
      ensures out.WF()
    {
      var oldChild := children[childIdx];
      var newLeftChild := oldChild.ApplyFilter(Domain(pivotTable[childIdx-1], Element(splitKey)));
      var newRightChild := oldChild.ApplyFilter(Domain(Element(splitKey), pivotTable[childIdx]));

      // TODO(jonh): BucketsLib suggests this is a timeout trap?
      var newChildren := replace1with2(children, newLeftChild, newRightChild, childIdx);
      assert forall i:nat | i<|newChildren| :: newChildren[i].WF() by { reveal_replace1with2(); }
      WFPivotsInsert(pivotTable, childIdx, splitKey);
      BetreeNode(buffers, InsertPivot(pivotTable, childIdx, splitKey), newChildren)
    }

    function Promote(domain: Domain) : (out: BetreeNode)
      requires WF()
      requires domain.WF()
      requires domain.Domain?
      ensures out.WF()
    {
      if Nil? then EmptyRoot(domain) else this
    }

    function ChildDomain(childIdx: nat) : (out: Domain)
      requires WF()
      requires BetreeNode?
      requires childIdx < NumBuckets(pivotTable)
      ensures out.WF()
    {
      reveal_IsStrictlySorted();
      Domain(pivotTable[childIdx], pivotTable[childIdx+1])
    }

    function Flush(childIdx: nat) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      requires childIdx < NumBuckets(pivotTable)
      ensures out.WF()
    {
      var keepKeys := /*placeholder*/ ChildDomain(childIdx);
      var keptBuffers := buffers.ApplyFilter(keepKeys); // OOF!
      var movedBuffers := buffers.ApplyFilter(ChildDomain(childIdx));
      var newChild := children[childIdx].Promote(ChildDomain(childIdx)).PrependBufferStack(movedBuffers);
      BetreeNode(keptBuffers, pivotTable, children[childIdx := newChild])
    }

    function Buffers() : BufferStack
    {
      if Nil? then BufferStack([]) else buffers
    }

    function Children() : seq<BetreeNode>
    {
      if Nil? then [] else children
    }

    predicate EquivalentBufferCompaction(other: BetreeNode)
    {
      && WF()
      && other.WF()
      && Buffers().Equivalent(other.Buffers())
      // Can only make a local change; entirety of children subtrees are identical.
      && Children() == other.Children()
    }
  }

  function EmptyRoot(domain: Domain) : (out: BetreeNode)
    requires domain.WF()
    requires domain.Domain?
    ensures out.WF()
  {
    var pivotTable := [domain.start, domain.end];
    assert Keyspace.IsStrictlySorted(pivotTable) by { reveal_IsStrictlySorted(); }
    BetreeNode(BufferStack([]), pivotTable, [Nil])
  }
}
