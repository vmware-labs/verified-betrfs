// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedBetree.i.dfy"
include "../../lib/Base/total_order.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "Domain.i.dfy"

module PivotBetree
{
  import opened Options
  import opened KeyType
  import opened StampedMod
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
  import opened DomainMod

  datatype TransitionLabel =
    QueryLabel(endLsn: LSN, key: Key, value: Value)
  | PutLabel(puts: MsgHistory)
  | QueryEndLsnLabel(endLsn: LSN)
  | FreezeAsLabel(stampedBetree: StampedBetree)
  | InternalLabel()

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

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

    predicate ValidChildIndex(childIdx: nat)
    {
      && BetreeNode?
      && childIdx < NumBuckets(pivotTable)
    }

    function PushBufferStack(bufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers.PushBufferStack(bufferStack), pivotTable, children)
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
      // Note that pivot indices are one-off of child indices.
      // Note that we will never generate a pivot of 0 or |pivotTable|
      && PivotInsertable(pivotTable, childIdx+1, splitKey)
      && childIdx < NumBuckets(pivotTable)
    }

    function Split(childIdx: nat, splitKey: Key) : (out: BetreeNode)
      requires CanSplit(childIdx, splitKey)
      requires BetreeNode?
      ensures out.WF()
    {
      var oldChild := children[childIdx];
      assert WFChildren(children);  // trigger
      var DomainRoutedToChild := DomainRoutedToChild(childIdx);
      var newLeftChild := oldChild.ApplyFilter(Domain(DomainRoutedToChild.start, Element(splitKey)));
      var newRightChild := oldChild.ApplyFilter(Domain(Element(splitKey), DomainRoutedToChild.end));

      var newChildren := replace1with2(children, newLeftChild, newRightChild, childIdx);

      assert forall i:nat | i<|newChildren| :: newChildren[i].WF() by {
        forall i:nat | i<|newChildren| ensures newChildren[i].WF() {
          if childIdx+1 < i { // sequence math trigger
            assert newChildren[i] == children[i-1];
          }
        }
      }
      WFPivotsInsert(pivotTable, childIdx+1, splitKey);
      BetreeNode(buffers, InsertPivot(pivotTable, childIdx+1, splitKey), newChildren)
    }

    function Promote(domain: Domain) : (out: BetreeNode)
      requires WF()
      requires domain.WF()
      requires domain.Domain?
      ensures out.WF()
    {
      if Nil? then EmptyRoot(domain) else this
    }

    function MyDomain() : (out: Domain)
      requires WF()
      requires BetreeNode?
    { 
      Domain(pivotTable[0], Last(pivotTable))
    }

    function DomainRoutedToChild(childIdx: nat) : (out: Domain)
      requires WF()
      requires BetreeNode?
      requires ValidChildIndex(childIdx)
      ensures out.WF()
    {
      var out := Domain(pivotTable[childIdx], pivotTable[childIdx+1]);
      reveal_IsStrictlySorted();  /* jonh suspicious lt leak */
      out.reveal_SaneKeys();  /* jonh suspicious lt leak */
      out
    }

    predicate CanFlush(childIdx: nat)
    {
      && WF()
      && BetreeNode?
      && ValidChildIndex(childIdx)
    }

    function Flush(childIdx: nat) : (out: BetreeNode)
      requires CanFlush(childIdx)
      ensures out.WF()
    {
      var keepKeys := AllKeys() - DomainRoutedToChild(childIdx).KeySet();
      var keptBuffers := buffers.ApplyFilter(keepKeys);
      var movedBuffers := buffers.ApplyFilter(DomainRoutedToChild(childIdx).KeySet());
      assert WFChildren(children);  // trigger
      var newChild := children[childIdx].Promote(DomainRoutedToChild(childIdx)).PushBufferStack(movedBuffers);
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

    predicate KeyInDomain(key: Key)
    {
      && WF()
      && BetreeNode?
      && BoundedKey(pivotTable, key)
    }

    // Redundant; should equal domain.KeySet() for the domain specified by the pivotTable.
    function KeySet() : iset<Key>
      requires WF()
      requires BetreeNode?
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
    domain.reveal_SaneKeys();  /* jonh suspicious lt leak */
    assert Keyspace.IsStrictlySorted(pivotTable) by { reveal_IsStrictlySorted(); }  /* jonh suspicious lt leak */
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

  // TODO(tony): replace with Stamped(BetreeNode). Change .root to .value everywhere; update broken triggers
  type StampedBetree = Stamped<BetreeNode>

  function EmptyImage() : StampedBetree
  {
    Stamped(Nil, 0)
  }

  function PushMemtable(root: BetreeNode, memtable: Memtable) : StampedBetree
    requires root.WF()
  {
    var newBuffer := Buffer(memtable.mapp);
    Stamped(root.Promote(TotalDomain()).PushBufferStack(BufferStack([newBuffer])), memtable.seqEnd)
  }

  datatype Variables = Variables(
    memtable: Memtable,
    root: BetreeNode)
  {
    predicate WF() {
      && root.WF()
    }
  }

  predicate Query(v: Variables, v': Variables, lbl: TransitionLabel, receipt: QueryReceipt)
  {
    && lbl.QueryLabel?
    && lbl.endLsn == v.memtable.seqEnd
    && receipt.ValidFor(v.root, lbl.key)
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
    && lbl.stampedBetree == PushMemtable(v.root, v.memtable)
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && var newBuffer := Buffer(v.memtable.mapp);
    && var rootBase := if v.root.Nil? then EmptyRoot(TotalDomain()) else v.root;
    && v' == v.(
        memtable := v.memtable.Drain(),
        root := PushMemtable(v.root, v.memtable).value
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
      && node.WF()
      && node.KeyInDomain(key)
      && node.BetreeNode?
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
    && v' == v.(root := EmptyRoot(TotalDomain()).(children := [v.root]))
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalSplitStep?
    && step.WF()
    && step.path.node == v.root
    && v' == v.(
        root := step.path.Substitute(step.path.Target().Split(step.childIdx, step.splitKey))
      )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.path.Valid()
    && step.path.node == v.root
    && step.path.Target().CanFlush(step.childIdx)
    && v' == v.(
          root := step.path.Substitute(step.path.Target().Flush(step.childIdx))
      )
  }

  function CompactedNode(original: BetreeNode, newBufs: BufferStack) : BetreeNode 
    requires original.BetreeNode?
    requires original.buffers.Equivalent(newBufs)
  {
    BetreeNode(newBufs, original.pivotTable, original.children)
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
    requires step.WF()
  {
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.path.node == v.root
    && v' == v.(
          root := step.path.Substitute(CompactedNode(step.path.Target(), step.compactedBuffers))
      )
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && stampedBetree.value.WF()
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.value)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep()
    | InternalSplitStep(path: Path, childIdx: nat, splitKey: Key)
    | InternalFlushStep(path: Path, childIdx: nat)
    | InternalCompactStep(path: Path, compactedBuffers: BufferStack)
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalSplitStep(path, childIdx, splitKey) =>
          && path.Valid()
          && path.Target().ValidChildIndex(childIdx)
          && path.Target().CanSplit(childIdx, splitKey) // This should be an enabling condition, not a WF, really?
        case InternalFlushStep(path, childIdx) =>
          && path.Valid()
          && path.Target().ValidChildIndex(childIdx)
        case InternalCompactStep(path, compactedBuffers) =>
          && path.Valid()
          && path.Target().BetreeNode?  // no point compacting a nil node
                                        // todo(tony): but this is implied by path.Valid(), I think
          && path.Target().buffers.Equivalent(compactedBuffers)
        case _ => true
      }
    }
  }

  predicate NextStep(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && step.WF()
    && match step {
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