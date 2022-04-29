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
  import opened Buffers
  import opened MemtableMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
//  import opened Lexicographic_Byte_Order
  import opened BoundedPivotsLib

  datatype TransitionLabel =
    QueryLabel(endLsn: LSN, key: Key, value: Value)
  | PutLabel(puts: MsgHistory)
  | QueryEndLsnLabel(endLsn: LSN)
  | FreezeAsLabel(stampedBetree: StampedBetree)
  | InternalLabel()

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  // end is exclusive
  datatype Domain = EmptyDomain | Domain(start: Element, end: Element)
  {
    // Key comparisons are a trigger party
    predicate {:opaque} SaneKeys()
    {
      && (!EmptyDomain? ==>
          && lt(start, end)
          && start.Element?
          && ElementIsKey(start)
          && (end.Element? ==> ElementIsKey(end))
        )
    }

    predicate WF() {
      && SaneKeys()
    }

    predicate {:opaque} Contains(key: Key) {
      && !EmptyDomain?
//      && lte(start, Element(key)) XXX
//      && lt(Element(key), end) XXX
    }

    // TODO(jonh): Why are these unused?
//    function IntersectInner(r2: Domain) : Domain
//      requires Domain?
//      requires r2.Domain?
//      requires lte(start, r2.start)
//    {
//      if lte(end, r2.start)
//      then EmptyDomain
//      else if lt(end, r2.end)
//      then Domain(r2.start, end)
//      else Domain(r2.start, r2.end)
//    }
//
//    function Intersect(r2: Domain) : Domain
//    {
//      if EmptyDomain? || r2.EmptyDomain?
//      then this
//      else if lte(start, r2.start)
//      then this.IntersectInner(r2)
//      else r2.IntersectInner(this)
//    }

    // Interpret a domain for use with an abstract Buffer.
    function KeySet() : iset<Key>
    {
      iset key | Contains(key)
    }
  }

  function TotalDomain() : (out: Domain)
    ensures out.WF()
  {
    Domain(Upperbounded_Lexicographic_Byte_Order_Impl.Ord.GetSmallestElement(), Max_Element)
  }

  predicate WFChildren(children: seq<BetreeNode>)
  {
    (forall i:nat | i<|children| :: children[i].WF())
  }

  datatype BetreeNode = Nil | BetreeNode(
    buffers: BufferStack,
    pivotTable: PivotTable,
    children: seq<BetreeNode>)
  {
    predicate WF() {
      && (BetreeNode? ==>
          && WFPivots(pivotTable)
          && |children| == NumBuckets(pivotTable)
          && WFChildren(children)
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
      var out := BetreeNode(buffers.ApplyFilter(filter.KeySet()), pivotTable, children);
      out
    }

    predicate CanSplit(childIdx: nat, splitKey: Key)
    {
      && WF()
      && BetreeNode?
      && PivotInsertable(pivotTable, childIdx, splitKey)
      && 0 < childIdx < NumBuckets(pivotTable) // Can't extend domain of this node via split.
    }

    // TODO(jonh): Split shouldn't also Grow; that's a separate operation.
    function Split(childIdx: nat, splitKey: Key) : (out: BetreeNode)
      requires CanSplit(childIdx, splitKey)
      requires BetreeNode?
      ensures out.WF()
    {
      var oldChild := children[childIdx];
      assert WFChildren(children);  // trigger
      var newLeftChild := oldChild.ApplyFilter(Domain(pivotTable[childIdx-1], Element(splitKey)));
      var newRightChild := oldChild.ApplyFilter(Domain(Element(splitKey), pivotTable[childIdx]));

      // TODO(jonh): BucketsLib suggests this is a timeout trap?
      var newChildren := replace1with2(children, newLeftChild, newRightChild, childIdx);
//      assert forall i:nat | i<|newChildren| :: newChildren[i].WF() by { reveal_replace1with2(); }
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
//      reveal_IsStrictlySorted();
      Domain(pivotTable[childIdx], pivotTable[childIdx+1])
    }

    predicate CanFlush(childIdx: nat)
    {
      && WF()
      && BetreeNode?
      && childIdx < NumBuckets(pivotTable)
    }

    function Flush(childIdx: nat) : (out: BetreeNode)
      requires CanFlush(childIdx)
      ensures out.WF()
    {
      var keepKeys := AllKeys() - ChildDomain(childIdx).KeySet();
      var keptBuffers := buffers.ApplyFilter(keepKeys);
      var movedBuffers := buffers.ApplyFilter(ChildDomain(childIdx).KeySet());
      assert WFChildren(children);  // trigger
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

    predicate {:opaque} KeyInDomain(key: Key)
    {
      && WF()
      && BetreeNode?
//      && BoundedKey(pivotTable, key)  XXX
    }

    // Redundant; should equal domain.KeySet() for the domain specified by the pivotTable.
    function KeySet() : iset<Key>
      requires WF()
      requires BetreeNode?  // TODO(jonh): trouble for Nils?
    {
      iset key | KeyInDomain(key)
    }

    function Child(key: Key) : BetreeNode
      requires WF()
      requires BetreeNode?
      requires KeyInDomain(key)
    {
      assert WFChildren(children);  // trigger
      children[Route(pivotTable, key)]
    }
  }

  function EmptyRoot(domain: Domain) : (out: BetreeNode)
    requires domain.WF()
    requires domain.Domain?
    ensures out.WF()
  {
    var pivotTable := [domain.start, domain.end];
//    assert Keyspace.IsStrictlySorted(pivotTable) by { reveal_IsStrictlySorted(); }
    BetreeNode(BufferStack([]), pivotTable, [Nil])
  }

  // TODO(jonh): sooooo much copy-paste. Maybe pull some of this logic, like the idea
  // of a QueryReciept, out into a library?
  datatype QueryReceiptLine = QueryReceiptLine(
    node: BetreeNode,
    result: Message)
  {
    predicate WF()
    {
      && node.WF()
      && result.Define?
    }
  }

  datatype QueryReceipt = QueryReceipt(
    key: Key,
    root: BetreeNode,
    lines: seq<QueryReceiptLine>)
  {
    predicate Structure()
    {
      && 0 < |lines|
      && lines[0].node == root
      && (forall i:nat | i < |lines| :: lines[i].node.BetreeNode? <==> i < |lines|-1)
      && Last(lines).result == Define(DefaultValue())
    }

    predicate AllLinesWF()
    {
      && (forall i:nat | i < |lines| :: lines[i].WF())
      && (forall i:nat | i < |lines|-1 :: lines[i].node.KeyInDomain(key))
    }

    function ChildAt(i: nat) : BetreeNode
      requires AllLinesWF()
      requires Structure()
      requires i < |lines|-1
    {
      lines[i].node.Child(key)
    }

    predicate ChildLinkedAt(i: nat)
      requires AllLinesWF()
      requires Structure()
      requires i < |lines|-1
    {
      lines[i+1].node == ChildAt(i)
    }

    function ResultAt(i: nat) : Message
      requires i < |lines|
    {
      lines[i].result
    }

    predicate ResultLinkedAt(i: nat)
      requires Structure()
      requires AllLinesWF()
      requires i < |lines| - 1
    {
      && lines[i].result == Merge(lines[i].node.buffers.Query(key), ResultAt(i+1))
    }

    predicate Valid()
    {
      && Structure()
      && AllLinesWF()
      && (forall i:nat | i < |lines| - 1 :: ChildLinkedAt(i))
      && (forall i:nat | i < |lines| - 1 :: ResultLinkedAt(i))
    }

    function Result() : Message
      requires Structure()
    {
      ResultAt(0)
    }

    predicate ValidFor(root: BetreeNode, key: Key)
    {
      && Valid()
      && this.root == root
      && this.key == key
    }
  }

  datatype StampedBetree = StampedBetree(
    root: BetreeNode,
    seqEnd: LSN
    )
  {
    predicate WF()
    {
      root.WF()
    }

    function PrependMemtable(memtable: Memtable) : StampedBetree
      requires WF()
    {
      var newBuffer := Buffer(memtable.mapp);
      StampedBetree(root.Promote(TotalDomain()).PrependBufferStack(BufferStack([newBuffer])), memtable.seqEnd)
    }
  }

  datatype Variables = Variables(
    memtable: Memtable,
    stampedBetree: StampedBetree)
  {
    predicate WF() {
      && stampedBetree.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && receipt.ValidFor(v.stampedBetree.root, lbl.key)
    && Define(lbl.value) == Merge(v.memtable.Query(lbl.key), receipt.Result())
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.PutLabel?
    && lbl.puts.WF()
    && lbl.puts.seqStart == v.memtable.seqEnd
    && v' == v.(
        memtable := v.memtable.ApplyPuts(lbl.puts)
      )
  }

  predicate QueryEndLsn(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.QueryEndLsnLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && v' == v
  }

  predicate FreezeAs(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.FreezeAsLabel?
    && v.WF()
    && lbl.stampedBetree == v.stampedBetree
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && var newBuffer := Buffer(v.memtable.mapp);
    && var rootBase := if v.stampedBetree.root.Nil? then EmptyRoot(TotalDomain()) else v.stampedBetree.root;
    && v' == v.(
        memtable := v.memtable.Drain(),
        stampedBetree := v.stampedBetree.PrependMemtable(v.memtable)
      )
  }
  
  datatype Path = Path(node: BetreeNode, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires node.KeyInDomain(key)
    {
      Path(node.Child(key), key, depth-1)
    }

    predicate Valid()
      decreases depth
    {
      && node.KeyInDomain(key)
      && (0 < depth ==> Subpath().Valid())
    }

    function Target() : (out: BetreeNode)
      requires Valid()
      ensures out.WF()
      ensures out.BetreeNode?
      decreases depth
    {
      if 0 == depth
      then node
      else Subpath().Target()
    }

    function ReplacedChildren(replacement: BetreeNode) : (out: seq<BetreeNode>)
      requires Valid()
      requires replacement.WF()
      requires 0 < depth
      ensures WFChildren(out)
      decreases depth, 0
    {
      var out := node.children[Route(node.pivotTable, key) := Subpath().Substitute(replacement)];
      assert Subpath().Substitute(replacement).WF();  // trigger
      assert WFChildren(node.children);  // trigger
      out
    }

    function Substitute(replacement: BetreeNode) : (out: BetreeNode)
      requires Valid()
      requires replacement.WF()
      decreases depth, 1
    {
      if 0 == depth
      then replacement
      else
        BetreeNode(node.buffers, node.pivotTable, ReplacedChildren(replacement))
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalLabel?
    && step.InternalGrowStep?
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := EmptyRoot(TotalDomain()).(children := [v.stampedBetree.root])
        )
      )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalSplitStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && step.path.Target().CanSplit(step.childIdx, step.splitKey)
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.path.Target().Split(step.childIdx, step.splitKey))
        )
      )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && step.path.Target().CanFlush(step.childIdx)
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.path.Target().Flush(step.childIdx))
        )
      )
  }

  // NB we tell you exactly how to Split and Flush, but leave lots of
  // nondetermistic freedom in the description of Compact.
  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.path.Valid()
    && step.path.node == v.stampedBetree.root
    && step.compactedNode.WF()
    && step.path.Target().EquivalentBufferCompaction(step.compactedNode)
    && v' == v.(
        stampedBetree := v.stampedBetree.(
          root := step.path.Substitute(step.compactedNode)
        )
      )
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && stampedBetree.WF()
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep()
    | InternalSplitStep(path: Path, childIdx: nat, splitKey: Key)
    | InternalFlushStep(path: Path, childIdx: nat)
    | InternalCompactStep(path: Path, compactedNode: BetreeNode)

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    match step {
      case QueryStep(receipt) => Query(v, v', lbl, receipt)
      case PutStep() => Put(v, v', lbl)
      case QueryEndLsnStep() => QueryEndLsn(v, v', lbl)
      case FreezeAsStep() => FreezeAs(v, v', lbl)
      case InternalGrowStep() => InternalGrow(v, v', lbl, step)
      case InternalSplitStep(_, _, _) => InternalSplit(v, v', lbl, step)
      case InternalFlushStep(_, _) => InternalFlush(v, v', lbl, step)
      case InternalCompactStep(_, _) => InternalCompact(v, v', lbl, step)
    }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
