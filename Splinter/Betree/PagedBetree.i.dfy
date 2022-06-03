// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractMap.i.dfy"
include "Buffers.i.dfy"
include "Memtable.i.dfy"

// This is a functional model of a Betree, but it doesn't require that child
// maps be stored as contiguous ranges separated by a finite sets of pivots.
// That's complexity that we push down a layer, to the PivotBetree. Here,
// instead, we have a child for every possible key, as though every key is a
// pivot. That's not *exactly* right, since adjacent children
// (in fact, infinite ranges of adjacent children) will be identical:
// children for keys 40..70 may all carry (identical) buffers including
// keys in [40..70), since of course they're represented by the same node
// in PivotBetree, the next layer down the refinement stack.
//
// This trickiness mostly appears in the Path Substitution code, which has
// to decide which of the infinity children are getting replaced -- the answer
// depends on how the PivotBetree has decided to divvy up the child pointers.
module PagedBetree
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

  datatype TransitionLabel =
      QueryLabel(endLsn: LSN, key: Key, value: Value)
    | PutLabel(puts: MsgHistory)
    | QueryEndLsnLabel(endLsn: LSN)
    | FreezeAsLabel(stampedBetree: StampedBetree)
    | InternalLabel()

  datatype ChildMap = ChildMap(mapp: imap<Key, BetreeNode>) {
    predicate WF() {
      && Total(mapp.Keys)
      && (forall k | AnyKey(k) :: mapp[k].WF())
    }
  }
  
  function ConstantChildMap(target: BetreeNode) : (out: ChildMap)
    requires target.WF()
    ensures out.WF()
  {
    var mapp := imap key | AnyKey(key) :: target;
    ChildMap(mapp)
  }
  
  function EmptyChildMap() : (out: ChildMap)
  {
    ConstantChildMap(Nil)
  }

  datatype BetreeNode = Nil | BetreeNode(
    buffers: BufferStack,
    children: ChildMap)
  {
    predicate WF() {
      && (BetreeNode? ==> children.WF())
    }

    function Child(key: Key) : BetreeNode
      requires WF()
      requires BetreeNode?
    {
      assert children.WF(); // trigger
      children.mapp[key]
    }

    function PushMemtable(memtable: Memtable) : StampedBetree
      requires WF()
    {
      var newBuffer := Buffer(memtable.mapp);
      StampedBetree(this.Promote().PushBufferStack(BufferStack([newBuffer])), memtable.seqEnd)
    }

    function PushBufferStack(bufferStack: BufferStack) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      BetreeNode(buffers.PushBufferStack(bufferStack), children)
    }

    function ApplyFilter(filter: iset<Key>) : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      if Nil? then Nil else
      var out := BetreeNode(buffers.ApplyFilter(filter), children);
      out
    }

    function Split(leftKeys: iset<Key>, rightKeys: iset<Key>) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      // We suppose that a lower layer will use this when leftKeys+rightKeys are all
      // identical, so that the first two branches of the if expression each produce
      // a single BetreeNode (with a shared representation below).
      assert children.WF(); // trigger
      var mapp := imap key | AnyKey(key)
        :: if key in leftKeys
            then Child(key).ApplyFilter(leftKeys)
            else if key in rightKeys
            then Child(key).ApplyFilter(rightKeys)
            else Child(key);
      BetreeNode(buffers, ChildMap(mapp))
    }

    // TODO(jonh): side-quest: We don't need Nil, do we? Wait, that's dumb, the
    // infinity of child pointers have to point to something.
    function Promote() : (out: BetreeNode)
      requires WF()
      ensures out.WF()
    {
      if Nil? then EmptyRoot() else this
    }

    function Flush(downKeys: iset<Key>) : (out: BetreeNode)
      requires WF()
      requires BetreeNode?
      ensures out.WF()
    {
      var keptBuffers := buffers.ApplyFilter(AllKeys() - downKeys);
      var movedBuffers := buffers.ApplyFilter(downKeys);
      assert children.WF();
      // TODO(jonh): NB the Promote() never happens: all the downKeys have to be non-Nil
      var outChildren := ChildMap(imap key | AnyKey(key)
        :: if key in downKeys
          then Child(key).Promote().PushBufferStack(movedBuffers)
          else Child(key));
      assert outChildren.WF();
      BetreeNode(keptBuffers, outChildren)
    }

    predicate EquivalentBufferCompaction(other: BetreeNode)
    {
      && WF()
      && other.WF()
      && Promote().buffers.Equivalent(other.Promote().buffers)
      // Can only make a local change; entirety of children subtrees are identical.
      && Promote().children == other.Promote().children
    }
  }

  function EmptyRoot() : (out: BetreeNode)
    ensures out.WF()
  {
    BetreeNode(BufferStack([]), ConstantChildMap(Nil))
  }

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

  // NB the top line is the line for the root node; hence Result()==ResultAt(0)
  // The bottom line is always Nil
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
    }

    function ChildAt(i: nat) : BetreeNode
      requires AllLinesWF()
      requires Structure()
      requires i < |lines|-1
    {
      assert lines[i].node.children.WF();  // trigger
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
    // betree needs its own lsn so we remember it for freeze time without
    // having to drain the membuffer:
    seqEnd: LSN
    )
  {
    predicate WF()
    {
      root.WF()
    }
  }

  function EmptyStampedBetree() : StampedBetree
  {
    StampedBetree(Nil, 0)
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
    // Implementation expected to perform this action only when memtable is empty
    && lbl.FreezeAsLabel?
    && v.WF()
    && lbl.stampedBetree == v.root.PushMemtable(v.memtable)
    && v' == v
  }

  predicate InternalFlushMemtable(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    && v.WF()
    && var newBuffer := Buffer(v.memtable.mapp);
    && v' == v.(
        memtable := v.memtable.Drain(),
        root := v.root.PushMemtable(v.memtable).root
      )
  }
  
  datatype Path = Path(node: BetreeNode, key: Key, depth: nat)
  {
    function Subpath() : (out: Path)
      requires 0 < depth
      requires node.WF()
      requires node.BetreeNode?
    {
      assert node.children.WF();  // trigger
      Path(node.Child(key), key, depth-1)
    }

    function MatchingChildren() : iset<Key>
      requires node.WF()
      requires node.BetreeNode?
    {
      assert node.children.WF();
      iset k2 | node.Child(k2)==node.Child(key)
    }

    predicate Valid()
      decreases depth
    {
      && node.WF()
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

    // opaque: these imap comprehensions cause some trigger mischief!
    function {:opaque} ReplacedChildren(replacement: BetreeNode) : (out: ChildMap)
      requires Valid()
      requires replacement.WF()
      requires 0 < depth
      ensures out.WF()
      decreases depth, 0
    {
      assert node.children.WF();  // trigger
      var replacedChildren := Subpath().Substitute(replacement);
      ChildMap(imap k | AnyKey(k) :: if k in MatchingChildren() then replacedChildren else node.Child(k))
    }

    function Substitute(replacement: BetreeNode) : (out: BetreeNode)
      requires Valid()
      requires replacement.WF()
      decreases depth, 1
    {
      if 0 == depth
      then replacement
      else
        BetreeNode(node.buffers, ReplacedChildren(replacement))
    }
  }

  predicate InternalGrow(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && v.WF()
    && lbl.InternalLabel?
    && v' == v.(
        root := BetreeNode(BufferStack([]), ConstantChildMap(v.root))
      )
  }

  predicate InternalSplit(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalSplitStep?
    && step.path.Valid()
    && step.path.node == v.root
    && v' == v.(
        root := step.path.Substitute(step.path.Target().Split(step.leftKeys, step.rightKeys))
      )
  }

  predicate InternalFlush(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalFlushStep?
    && step.path.Valid()
    && step.path.node == v.root
    && v' == v.(
        root := step.path.Substitute(step.path.Target().Flush(step.downKeys))
      )
  }

  // NB we tell you exactly how to Split and Flush, but leave lots of
  // nondetermistic freedom in the description of Compact.
  predicate InternalCompact(v: Variables, v': Variables, lbl: TransitionLabel, step: Step)
  {
    && lbl.InternalLabel?
    && step.InternalCompactStep?
    && step.path.Valid()
    && step.path.node == v.root
    && step.compactedNode.WF()
    && step.path.Target().EquivalentBufferCompaction(step.compactedNode)
    && v' == v.(
        root := step.path.Substitute(step.compactedNode)
      )
  }

  // public:

  predicate Init(v: Variables, stampedBetree: StampedBetree)
  {
    && stampedBetree.WF()
    && v == Variables(EmptyMemtable(stampedBetree.seqEnd), stampedBetree.root)
  }

  datatype Step =
      QueryStep(receipt: QueryReceipt)
    | PutStep()
    | QueryEndLsnStep()
    | FreezeAsStep()
    | InternalGrowStep()
    | InternalSplitStep(path: Path, leftKeys: iset<Key>, rightKeys: iset<Key>)
    | InternalFlushStep(path: Path, downKeys: iset<Key>)
    | InternalCompactStep(path: Path, compactedNode: BetreeNode)
  {
    predicate WF() {
      match this {
        case InternalSplitStep(path, _, _) => path.Valid()
        case InternalFlushStep(path, _) => path.Valid()
        case InternalCompactStep(path, _) => path.Valid()
        case _ => true
      }
    }
  }

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
