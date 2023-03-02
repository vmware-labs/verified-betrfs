// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetree.i.dfy"
include "../../lib/Base/total_order.i.dfy"
include "../../lib/Buckets/BoundedPivotsLib.i.dfy"
include "Domain.i.dfy"
include "SplitRequest.i.dfy"
include "BufferOffsets.i.dfy"

// In contrast to the PivotBetree above, upon flushing a buffer down the tree, 
// the FilteredBetree keeps the entire buffer but notes that it should filter out the keys in 
// that buffer for the child to which it was flushed.

module FilteredBetree
{
  import opened Options
  import opened KeyType
  import opened StampedMod
  import TotalKMMapMod
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import opened BufferMod
  import opened BufferSeqMod
  import opened MemtableMod
  import opened Upperbounded_Lexicographic_Byte_Order_Impl
  import opened Upperbounded_Lexicographic_Byte_Order_Impl.Ord
//  import opened Lexicographic_Byte_Order
  import opened BoundedPivotsLib
  import opened DomainMod
  import opened SplitRequestMod
  import opened BufferOffsetsMod
  import opened OffsetMapMod

  datatype TransitionLabel =
    QueryLabel(endLsn: LSN, key: Key, value: Value)
  | PutLabel(puts: MsgHistory)
  | QueryEndLsnLabel(endLsn: LSN)
  | FreezeAsLabel(stampedBetree: StampedBetree)
  | InternalLabel()

  type Element = Upperbounded_Lexicographic_Byte_Order_Impl.Ord.Element

  predicate WFChildren(children: seq<BetreeNode>)
  {
    && (forall i:nat | i<|children| :: children[i].WF())
  }

  datatype BetreeNode = Nil | BetreeNode(
    buffers: BufferSeq,
    pivotTable: PivotTable,
    children: seq<BetreeNode>,
    // # of buffers flushed to each child
    // active buffers = [0, |buffers|-activeBufferRanges[i])
    flushedOffsets: BufferOffsets 
  )
  {
    predicate LocalStructure()
    {
      && (BetreeNode? ==>
          && WFPivots(pivotTable)
          && |children| == NumBuckets(pivotTable)
          && |children| == flushedOffsets.Size()
          && flushedOffsets.BoundedBy(buffers.Length())
        )
    }

    predicate ValidChildIndex(childIdx: nat)
    {
      && BetreeNode?
      && childIdx < NumBuckets(pivotTable)
    }

    predicate LinkedChildren()
      requires LocalStructure()
    {
      BetreeNode? ==>
        (forall i:nat |
            && ValidChildIndex(i)
            && children[i].BetreeNode?
            && children[i].LocalStructure() // WF will always give this, but we can't assume it yet without ending up recursive.
          :: children[i].MyDomain() == DomainRoutedToChild(i))
    }

    predicate WF() {
      && LocalStructure()
      && (BetreeNode? ==>
          && WFChildren(children)
          && LinkedChildren()
        )
    }

    function ExtendBufferSeq(bufferStack: BufferSeq) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers.Extend(bufferStack), pivotTable, children, flushedOffsets)
    }

    function ActiveBuffersForKey(key: Key) : (i: nat)
      requires KeyInDomain(key)
      requires flushedOffsets.BoundedBy(buffers.Length())
    {
      flushedOffsets.Get(Route(pivotTable, key))
    }
  
    predicate IsLeaf()
    {
      && BetreeNode?
      && |children|==1
      && children[0]==Nil
      && flushedOffsets==BufferOffsets([0]) 
    }

    predicate IsIndex()
    {
      && BetreeNode?
      && (forall i | 0 <= i < |children| :: children[i].BetreeNode?)
    }

    // Called on leaf; creates a new pivot
    function SplitLeaf(splitKey: Key) : (out: (BetreeNode, BetreeNode))
      requires WF()
      requires IsLeaf()
      requires MyDomain().Contains(splitKey)
      requires splitKey != MyDomain().start.e
      ensures out.0.WF() && out.1.WF()
    {
      var newLeft := BetreeNode(buffers, [pivotTable[0], Element(splitKey)], [Nil], BufferOffsets([0]));
      var newRight := BetreeNode(buffers, [Element(splitKey), pivotTable[1]], [Nil], BufferOffsets([0]));
      assert newLeft.WF() by { Keyspace.reveal_IsStrictlySorted(); }
      assert newRight.WF() by { Keyspace.reveal_IsStrictlySorted(); }
      (newLeft, newRight)
    }

    // Called on index; lifts an existing pivot from the child
    function SplitIndex(pivotIdx: nat) : (out: (BetreeNode, BetreeNode))
      requires WF()
      requires IsIndex()
      requires 0 < pivotIdx < |pivotTable|-1
      ensures out.0.WF() && out.1.WF()
    {
      var newLeft := BetreeNode(buffers, pivotTable[..pivotIdx+1], children[..pivotIdx], flushedOffsets.Slice(0, pivotIdx));
      var newRight := BetreeNode(buffers, pivotTable[pivotIdx..], children[pivotIdx..], flushedOffsets.Slice(pivotIdx, flushedOffsets.Size()));
      WFSlice(pivotTable, 0, pivotIdx+1);
      WFSuffix(pivotTable, pivotIdx);
      assert WFChildren(children);  // trigger
      assert newLeft.WF();
      assert newRight.WF();
      (newLeft, newRight)
    }

    predicate CanSplitParent(request: SplitRequest)
    {
      && WF()
      && BetreeNode?
      && ValidChildIndex(request.childIdx)
      && var child := children[request.childIdx];
      && match request {
        case SplitLeaf(_, splitKey) => child.SplitLeaf.requires(splitKey)
        case SplitIndex(_, childPivotIdx) => child.SplitIndex.requires(childPivotIdx)
      }
    }

    function SplitKey(request: SplitRequest) : (out: Key)
      requires WF()
      requires CanSplitParent(request)
      ensures PivotInsertable(pivotTable, request.childIdx+1, out)
    {
      var oldChild := children[request.childIdx];
      var out := if request.SplitLeaf? then request.splitKey else oldChild.pivotTable[request.childPivotIdx].e;

      assert PivotInsertable(pivotTable, request.childIdx+1, out) by {
        Keyspace.reveal_IsStrictlySorted();
      }
      WFPivotsInsert(pivotTable, request.childIdx+1, out);

      out
    }

    function SplitParentDefn(request: SplitRequest) : (out: BetreeNode)
      requires WF()
      requires CanSplitParent(request)
    {
      var oldChild := children[request.childIdx];
      var (newLeftChild, newRightChild) := if request.SplitLeaf? then oldChild.SplitLeaf(request.splitKey) else oldChild.SplitIndex(request.childPivotIdx);
      var newChildren := replace1with2(children, newLeftChild, newRightChild, request.childIdx);
      var newflushedOffsets := flushedOffsets.Split(request.childIdx);
      BetreeNode(buffers, InsertPivot(pivotTable, request.childIdx+1, SplitKey(request)), newChildren, newflushedOffsets)
    }

    lemma SplitParentWF(request: SplitRequest)
      requires WF()
      requires CanSplitParent(request)
      ensures SplitParentDefn(request).WF()
    {
      var oldChild := children[request.childIdx];
      assert WFChildren(children);  // trigger
      var (newLeftChild, newRightChild) := if request.SplitLeaf? then oldChild.SplitLeaf(request.splitKey) else oldChild.SplitIndex(request.childPivotIdx);
      var newChildren := replace1with2(children, newLeftChild, newRightChild, request.childIdx);

      assert forall i:nat | i<|newChildren| :: newChildren[i].WF() by {
        forall i:nat | i<|newChildren| ensures newChildren[i].WF() {
          if request.childIdx+1 < i { // sequence math trigger
            assert newChildren[i] == children[i-1];
          }
        }
      }

      var childFlushedBuffer := flushedOffsets.Get(request.childIdx);
      var newflushedOffsets := BufferOffsets(replace1with2(flushedOffsets.offsets, childFlushedBuffer, childFlushedBuffer, request.childIdx));
      forall i:nat | i < newflushedOffsets.Size()
        ensures newflushedOffsets.Get(i) <= buffers.Length() {
          if request.childIdx+1 < i { // sequence math trigger
            assert newflushedOffsets.Get(i) == flushedOffsets.Get(i-1);
          }
      }

      WFPivotsInsert(pivotTable, request.childIdx+1, SplitKey(request));
      var out := SplitParentDefn(request);

      // seq trigger for offset existing children
      assert forall i:nat | && out.ValidChildIndex(i) :: i>request.childIdx+1 ==> out.children[i] == children[i-1];
    }

    // this is a parent in a Split operation
    function SplitParent(request: SplitRequest) : (out: BetreeNode)
      requires SplitParentDefn.requires(request)
      ensures out.WF()
    {
      SplitParentWF(request);
      SplitParentDefn(request)
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
      requires LocalStructure()
      requires BetreeNode?
    { 
      Domain(pivotTable[0], Last(pivotTable))
    }

    function DomainRoutedToChild(childIdx: nat) : (out: Domain)
      requires LocalStructure()
      requires BetreeNode?
      requires ValidChildIndex(childIdx)
      ensures out.WF()
    {
      var out := Domain(pivotTable[childIdx], pivotTable[childIdx+1]);
      reveal_IsStrictlySorted();  /* jonh suspicious lt leak */
      out.reveal_SaneKeys();  /* jonh suspicious lt leak */
      out
    }

    function ActiveBufferKeysForChild(childIdx: nat, bufferIdx: nat) : iset<Key>
    requires WF()
    requires BetreeNode?
    requires childIdx < |children|
    requires bufferIdx < buffers.Length()
    {
      if bufferIdx >= flushedOffsets.Get(childIdx)
      then DomainRoutedToChild(childIdx).KeySet()
      else iset{}
    }

    function ActiveBufferKeys(bufferIdx: nat) : iset<Key>
      requires WF()
      requires BetreeNode?
      requires bufferIdx < buffers.Length()
    {
      iset k, i | 0 <= i < |children| && k in ActiveBufferKeysForChild(i, bufferIdx) :: k
    }

    // retruns the requested active slice of a buffer
    function ActiveBufferSlice(start: nat, end: nat) : BufferSeq
      requires WF()
      requires BetreeNode?
      requires start <= end <= buffers.Length()
    {
      var activeBuffers := seq (end-start, i requires 0 <= i < end-start 
                            => buffers.buffers[i+start].ApplyFilter(ActiveBufferKeys(i+start)));
      BufferSeq(activeBuffers)
    }

    predicate CanFlush(childIdx: nat)
    {
      && WF()
      && BetreeNode?
      && ValidChildIndex(childIdx)
    }

    function Flush(childIdx: nat, bufferGCCount: nat) : (out: BetreeNode)
      requires CanFlush(childIdx)
      // requires bufferGCCount <= buffers.Length()
      requires flushedOffsets.AdvanceIndex(childIdx, buffers.Length()).CanCollectGarbage(bufferGCCount)
      ensures out.WF()
    {
      var flushUpTo := buffers.Length();
      var newFlushedOffsets := flushedOffsets.AdvanceIndex(childIdx, flushUpTo);
      var movedBuffers := buffers.Slice(flushedOffsets.Get(childIdx), flushUpTo); // buffers flushed to child

      assert bufferGCCount <= buffers.Length() by {
        var i:nat :| i < newFlushedOffsets.Size();
        assert newFlushedOffsets.Get(i) <= buffers.Length();
      } 

      assert WFChildren(children);  // trigger
      var newChild := children[childIdx].Promote(DomainRoutedToChild(childIdx)).ExtendBufferSeq(movedBuffers);

      // new parent, with updated num flushed buffers for children and truncate buffers that are flushed to all children
      var gcFlushedOffsets := newFlushedOffsets.CollectGarbage(bufferGCCount);


      var newRoot := BetreeNode(buffers.Slice(bufferGCCount, flushUpTo), pivotTable, children[childIdx := newChild], gcFlushedOffsets);
      assert newRoot.WF();
      newRoot
    }

    function Buffers() : BufferSeq
    {
      if Nil? then BufferSeq([]) else buffers
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

    function MakeOffsetMap() : OffsetMap 
      requires WF()
      requires BetreeNode?
    {
      OffsetMap(imap k | AnyKey(k) 
      :: if BoundedKey(pivotTable, k) then flushedOffsets.Get(Route(pivotTable, k))
          else buffers.Length())
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
    BetreeNode(BufferSeq([]), pivotTable, [Nil], BufferOffsets([0]))
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
      && var node := lines[i].node;
      && var start := node.ActiveBuffersForKey(key);
      && lines[i].result == Merge(node.buffers.QueryFrom(key, start), ResultAt(i+1))
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
    Stamped(root.Promote(TotalDomain()).ExtendBufferSeq(BufferSeq([memtable.buffer])), memtable.seqEnd)
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
    && v.memtable.IsEmpty()
    && lbl.stampedBetree == Stamped(v.root, v.memtable.seqEnd)
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
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
      && (0 < depth ==> node.IsIndex())
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

    predicate ChildrenHaveMatchingDomains(otherChildren: seq<BetreeNode>)
      requires Valid()
      requires 0 < depth  // my children are all non-Nil
    {
      assert WFChildren(node.children); // trigger
      && WFChildren(otherChildren)
      && |otherChildren| == |node.children|
      && (forall i:nat | node.ValidChildIndex(i) ::
          && otherChildren[i].WF()
          && otherChildren[i].BetreeNode?
          && otherChildren[i].MyDomain() == node.children[i].MyDomain()
        )
    }

    function ReplacedChildren(replacement: BetreeNode) : (out: seq<BetreeNode>)
      requires Valid()
      requires ValidReplacement(replacement)
      requires 0 < depth
      ensures ChildrenHaveMatchingDomains(out)
      decreases depth, 0
    {
      var newChild := Subpath().Substitute(replacement);

      assert WFChildren(Subpath().node.children);  // trigger to newChild.WF()
      assert WFChildren(node.children);  // trigger
      node.children[Route(node.pivotTable, key) := newChild]
    }
    
    predicate ValidReplacement(replacement: BetreeNode)
      requires Valid()
    {
      && replacement.WF()
      && replacement.BetreeNode?
      && replacement.MyDomain() == Target().MyDomain()
    }

    function Substitute(replacement: BetreeNode) : (out: BetreeNode)
      requires Valid()
      requires ValidReplacement(replacement)
      decreases depth, 1
    {
      if 0 == depth
      then replacement
      else
        BetreeNode(node.buffers, node.pivotTable, ReplacedChildren(replacement), node.flushedOffsets)
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
        root := step.path.Substitute(step.path.Target().SplitParent(step.request))
      )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.WF()
    // && step.path.Valid()
    && step.path.node == v.root
    && step.path.Target().CanFlush(step.childIdx)
    && v' == v.(
          root := step.path.Substitute(step.path.Target().Flush(step.childIdx, step.bufferGCCount))
      )
  }

  function CompactedNode(original: BetreeNode, compactStart: nat, compactEnd: nat, compactedBuffer: Buffer) : BetreeNode 
    requires original.BetreeNode?  
    requires original.WF()
    requires compactStart < compactEnd <= original.buffers.Length()
  {
    var compactedBuffers := BufferSeq(original.buffers.buffers[0..compactStart] + [ compactedBuffer ] + original.buffers.buffers[compactEnd..]);
    var compactedflushedOffsets:= original.flushedOffsets.OffSetsAfterCompact(compactStart, compactEnd);
    var newRoot := BetreeNode(compactedBuffers, original.pivotTable, original.children, compactedflushedOffsets);
    newRoot
  }

  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.WF()
    && step.path.node == v.root

    && v' == v.(
          root := step.path.Substitute(CompactedNode(step.path.Target(), step.compactStart, step.compactEnd, step.compactedBuffer))
      )
  }

  predicate InternalNoOp(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && lbl.InternalLabel?
    && v.WF()
    && v' == v
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
    | InternalSplitStep(path: Path, request: SplitRequest)
    | InternalFlushMemtableStep()
    | InternalFlushStep(path: Path, childIdx: nat, bufferGCCount: nat)
    | InternalCompactStep(path: Path, compactStart: nat, compactEnd: nat, compactedBuffer: Buffer)
    | InternalNoOpStep()
  {
    predicate WF() {
      match this {
        case QueryStep(receipt) => receipt.Valid()
        case InternalSplitStep(path, request) =>
          && path.Valid()
          && path.Target().ValidChildIndex(request.childIdx)
          && path.Target().CanSplitParent(request)
        case InternalFlushStep(path, childIdx, bufferGCCount) =>
          && path.Valid()
          && path.Target().ValidChildIndex(childIdx)
          && path.Target().flushedOffsets.AdvanceIndex(childIdx, path.Target().buffers.Length()).CanCollectGarbage(bufferGCCount)
        case InternalCompactStep(path, compactStart, compactEnd, comapctedBuffer) =>
          && path.Valid()
          && path.Target().BetreeNode?  // no point compacting a nil node
          && compactStart < compactEnd <= path.Target().buffers.Length()
          // New notion of equivalience between old buffer stack slice and comapctedBuffer
          && var offsetMap := path.Target().MakeOffsetMap().Decrement(compactStart);
          && path.Target().buffers.Slice(compactStart, compactEnd).IFiltered(offsetMap) == compactedBuffer
        case _ => true
      }
    }

    function SplitKey() : Key
      requires WF()
      requires InternalSplitStep?
    {
      path.Target().SplitKey(request)
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
        case InternalSplitStep(_, _) => InternalSplit(v, v', lbl, step)
        case InternalFlushStep(_, _, _) => InternalFlush(v, v', lbl, step)
        case InternalFlushMemtableStep() => InternalFlushMemtable(v, v', lbl)
        case InternalCompactStep(_, _, _, _) => InternalCompact(v, v', lbl, step)
        case InternalNoOpStep() => InternalNoOp(v, v', lbl)
      }
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel) {
    exists step: Step :: NextStep(v, v', lbl, step)
  }
}
