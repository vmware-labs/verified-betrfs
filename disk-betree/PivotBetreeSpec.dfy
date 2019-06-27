include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../tla-tree/MissingLibrary.dfy"
include "Message.dfy"
include "BetreeSpec.dfy"
include "Betree.dfy"
include "BetreeInv.dfy"

module PivotBetreeGraph refines Graph {
  import BG = BetreeGraph

  import MS = MapSpec
  import opened MissingLibrary
  import M = Message

  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element
  type Value = BG.Value

  type Reference = BG.Reference
  function Root() : Reference { BG.Root() }
  type Message = M.Message

  type PivotTable = seq<Key>
  type Bucket = map<Key, Message>
  datatype Node = Node(
      pivotTable: PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<Bucket>)

  function Successors(node: Node) : iset<Reference>
  {
    if node.children.Some? then (
      iset i | 0 <= i < |node.children.value| :: node.children.value[i]
    ) else (
      iset{}
    )
  }
}

module PivotBetreeBlockInterface refines BlockInterface {
  import G = PivotBetreeGraph
}

module PivotBetreeSpec {
  import MS = MapSpec
  import opened G = PivotBetreeGraph
  import opened Sequences
  import opened Maps
  import opened MissingLibrary

  export Spec provides *
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  function PivotTableSize(pivotTable: PivotTable) : int
  {
    |pivotTable| + 1
  }

  predicate WFPivotTable(pivotTable: PivotTable)
  {
    Keyspace.IsStrictlySorted(pivotTable)
  }

  function Route(pivotTable: PivotTable, key: Key) : int
  requires WFPivotTable(pivotTable)
  ensures 0 <= Route(pivotTable, key) < PivotTableSize(pivotTable)
  {
    Keyspace.LargestLte(pivotTable, key) + 1
  }

  predicate WFNode(node: Node)
  {
    && PivotTableSize(node.pivotTable) == |node.buckets|
    && (node.children.Some? ==> PivotTableSize(node.pivotTable) == |node.children.value|)
    && WFPivotTable(node.pivotTable)
  }

  // Adding messages to buffers

  function BucketLookup(bucket: Bucket, key: Key) : Message {
    if key in bucket then bucket[key] else M.IdentityMessage()
  }

  function AddMessageToBucket(bucket: Bucket, key: Key, msg: Message) : Bucket {
    bucket[key := M.Merge(msg, BucketLookup(bucket, key))]
  }

  function AddMessageToNode(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  ensures WFNode(AddMessageToNode(node, key, msg))
  {
    node.(
      buckets := node.buckets[
        Route(node.pivotTable, key) := AddMessageToBucket(node.buckets[Route(node.pivotTable, key)], key, msg)
      ]
    )
  }

  function AddMessagesToBucket(pivotTable: PivotTable, i: int, childBucket: map<Key, Message>, parentBucket: map<Key, Message>) : Bucket
  requires WFPivotTable(pivotTable)
  {
    map key
    | && (key in (childBucket.Keys + parentBucket.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Route(pivotTable, key) == i
      && M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key)) != M.IdentityMessage()
    :: M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key))
  }

  function AddMessagesToBuckets(pivotTable: PivotTable, i: int, buckets: seq<map<Key, Message>>, parentBucket: map<Key, Message>) : seq<Bucket>
  requires WFPivotTable(pivotTable)
  requires 0 <= i <= |buckets|;
  {
    if i == 0 then [] else (
      AddMessagesToBuckets(pivotTable, i-1, buckets, parentBucket) + [AddMessagesToBucket(pivotTable, i-1, buckets[i-1], parentBucket)]
    )
  }

  function AddMessagesToNode(node: Node, buffer: map<Key, Message>) : Node
  requires WFNode(node)
  {
    Node(
      node.pivotTable,
      node.children,
      AddMessagesToBuckets(node.pivotTable, |node.buckets|, node.buckets, buffer)
    )
  }

  //// Insert

  datatype MessageInsertion = MessageInsertion(key: Key, msg: Message, oldroot: Node)

  predicate ValidInsertion(ins: MessageInsertion) {
    && WFNode(ins.oldroot)
  }

  function InsertionReads(ins: MessageInsertion): seq<ReadOp>
  requires ValidInsertion(ins)
  {
    [G.ReadOp(Root(), ins.oldroot)]
  }

  function InsertionOps(ins: MessageInsertion) : seq<Op>
  requires ValidInsertion(ins)
  {
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var writeop := G.WriteOp(Root(), newroot);
    [writeop]
  }

  //// Flush

  datatype NodeFlush = NodeFlush(parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, newchild: Node, slotIndex: int)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
    && 0 <= flush.slotIndex < |flush.parent.buckets|
    && flush.parent.children.Some?
    && flush.parent.children.value[flush.slotIndex] == flush.childref
  }

  function FlushReads(flush: NodeFlush) : seq<ReadOp>
  requires ValidFlush(flush)
  {
    [
      G.ReadOp(flush.parentref, flush.parent),
      G.ReadOp(flush.childref, flush.child)
    ]
  }

  function FlushOps(flush: NodeFlush) : seq<Op>
  requires ValidFlush(flush)
  {
    var newparent := flush.parent.(buckets := flush.parent.buckets[flush.slotIndex := map[]]);
    var newchild := AddMessagesToNode(flush.child, flush.parent.buckets[flush.slotIndex]);
    var allocop := G.AllocOp(flush.newchildref, newchild);
    var writeop := G.WriteOp(flush.parentref, newparent);
    [allocop, writeop]
  }

  //// Grow

  datatype RootGrowth = RootGrowth(oldroot: Node, newchildref: Reference)

  predicate ValidGrow(growth: RootGrowth)
  {
    WFNode(growth.oldroot)
  }

  function GrowReads(growth: RootGrowth) : seq<ReadOp>
  requires ValidGrow(growth)
  {
    [G.ReadOp(Root(), growth.oldroot)]
  }

  function GrowOps(growth: RootGrowth) : seq<Op>
  requires ValidGrow(growth)
  {
    var newroot := Node([], Some([growth.newchildref]), [map[]]);
    var allocop := G.AllocOp(growth.newchildref, growth.oldroot);
    var writeop := G.WriteOp(Root(), newroot);
    [allocop, writeop]
  }

  //// Split

  datatype NodeFusion = NodeFusion(
    parentref: Reference,
    fused_childref: Reference,
    left_childref: Reference,
    right_childref: Reference,
    fused_parent: Node,
    split_parent: Node,
    fused_child: Node,
    left_child: Node,
    right_child: Node,
    
    slot_idx: int
  )

  predicate BucketFusion(
      fusedBucket: Bucket,
      leftBucket: Bucket,
      rightBucket: Bucket,
      pivot: Key)
  {
    && (forall key | Keyspace.lt(key, pivot) :: MapsAgreeOnKey(fusedBucket, leftBucket, key))
    && (forall key | Keyspace.lte(pivot, key) :: MapsAgreeOnKey(fusedBucket, rightBucket, key))
  }

  predicate PivotTableFusion(table: PivotTable, left: PivotTable, right: PivotTable, pivot: Key)
  {
    && table == concat3(left, pivot, right)
  }

  predicate ChildFusion(child: Node, left: Node, right: Node, pivot: Key)
  {
    && left.buckets + right.buckets == child.buckets
    && (child.children.Some? ==>
      && left.children.Some?
      && right.children.Some?
      && child.children.value == left.children.value + right.children.value
     )
    && (child.children.None? ==>
      && left.children.None?
      && right.children.None?
     )
    && PivotTableFusion(child.pivotTable, left.pivotTable, right.pivotTable, pivot)
  }

  predicate ValidFusion(fusion: NodeFusion)
  {
    && WFNode(fusion.split_parent)
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)

    && 0 <= fusion.slot_idx < |fusion.fused_parent.buckets|
    && |fusion.split_parent.buckets| == |fusion.fused_parent.buckets| + 1

    && fusion.fused_parent.children.Some?
    && fusion.split_parent.children.Some?

    && fusion.fused_parent.children.value[fusion.slot_idx] == fusion.fused_childref
    && fusion.split_parent.children.value[fusion.slot_idx] == fusion.left_childref
    && fusion.split_parent.children.value[fusion.slot_idx + 1] == fusion.right_childref
    && BucketFusion(
        fusion.fused_parent.buckets[fusion.slot_idx],
        fusion.split_parent.buckets[fusion.slot_idx],
        fusion.split_parent.buckets[fusion.slot_idx + 1],
        fusion.split_parent.pivotTable[fusion.slot_idx])

    && (forall i | 0 <= i < fusion.slot_idx :: fusion.fused_parent.children.value[i] == fusion.split_parent.children.value[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.children.value| :: fusion.fused_parent.children.value[i] == fusion.split_parent.children.value[i+1])

    && (forall i | 0 <= i < fusion.slot_idx :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.buckets| :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i+1])

    && (forall i | 0 <= i < fusion.slot_idx :: fusion.fused_parent.pivotTable[i] == fusion.split_parent.pivotTable[i])
    && (forall i | fusion.slot_idx <= i < |fusion.fused_parent.pivotTable| :: fusion.fused_parent.pivotTable[i] == fusion.split_parent.pivotTable[i+1])

    && ChildFusion(
        fusion.fused_child,
        fusion.left_child,
        fusion.right_child,
        fusion.split_parent.pivotTable[fusion.slot_idx])
  }

  predicate ValidSplit(fusion: NodeFusion)
  {
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)
    && ValidFusion(fusion)
  }

  function SplitReads(fusion: NodeFusion) : seq<ReadOp>
  requires ValidSplit(fusion)
  {
    [
      ReadOp(fusion.parentref, fusion.fused_parent),
      ReadOp(fusion.fused_childref, fusion.fused_child)
    ]
  }

  function SplitOps(fusion: NodeFusion) : seq<Op>
  requires ValidSplit(fusion)
  {
    [
      G.AllocOp(fusion.left_childref, fusion.left_child),
      G.AllocOp(fusion.right_childref, fusion.right_child),
      G.WriteOp(fusion.parentref, fusion.split_parent)
    ]
  }

  //// Merge

  predicate ValidMerge(fusion: NodeFusion)
  {
    ValidFusion(fusion)
  }

  function MergeReads(fusion: NodeFusion) : seq<ReadOp>
  requires ValidMerge(fusion)
  {
    [
      ReadOp(fusion.parentref, fusion.split_parent),
      ReadOp(fusion.left_childref, fusion.left_child),
      ReadOp(fusion.right_childref, fusion.right_child)
    ]
  }

  function MergeOps(fusion: NodeFusion) : seq<Op>
  requires ValidMerge(fusion)
  {
    [
      G.AllocOp(fusion.fused_childref, fusion.fused_child),
      G.WriteOp(fusion.parentref, fusion.fused_parent)
    ]
  }


  //// Put it all together

  datatype BetreeStep =
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeSplit(fusion: NodeFusion)
    | BetreeMerge(fusion: NodeFusion)

  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
      case BetreeInsert(ins) => ValidInsertion(ins)
      case BetreeFlush(flush) => ValidFlush(flush)
      case BetreeGrow(growth) => ValidGrow(growth)
      case BetreeSplit(fusion) => ValidSplit(fusion)
      case BetreeMerge(fusion) => ValidMerge(fusion)
    }
  }

  function BetreeStepReads(step: BetreeStep) : seq<ReadOp>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeInsert(ins) => InsertionReads(ins)
      case BetreeFlush(flush) => FlushReads(flush)
      case BetreeGrow(growth) => GrowReads(growth)
      case BetreeSplit(fusion) => SplitReads(fusion)
      case BetreeMerge(fusion) => MergeReads(fusion)
    }
  }

  function BetreeStepOps(step: BetreeStep) : seq<Op>
  requires ValidBetreeStep(step)
  {
    match step {
      case BetreeInsert(ins) => InsertionOps(ins)
      case BetreeFlush(flush) => FlushOps(flush)
      case BetreeGrow(growth) => GrowOps(growth)
      case BetreeSplit(fusion) => SplitOps(fusion)
      case BetreeMerge(fusion) => MergeOps(fusion)
    }
  }

  predicate BetreeStepUI(step: BetreeStep, uiop: MS.UI.Op<Value>) {
    match step {
      case BetreeInsert(ins) => ins.msg.Define? && uiop == MS.UI.PutOp(ins.key, ins.msg.value)
      case BetreeFlush(flush) => uiop.NoOp?
      case BetreeGrow(growth) => uiop.NoOp?
      case BetreeSplit(fusion) => uiop.NoOp?
      case BetreeMerge(fusion) => uiop.NoOp?
    }
  }
}

module PivotBetreeSpecRefinement {
  import B = BetreeSpec`Internal
  import P = PivotBetreeSpec`Internal
  import opened Message
  import MS = MapSpec
  import Keyspace = MS.Keyspace
  import opened Maps
  import opened Sequences
  import opened MissingLibrary

  type Node = B.G.Node
  type PNode = P.G.Node

  type Key = B.G.Key
  type Value = B.G.Value
  type Reference = B.G.Reference
  type Buffer = B.G.Buffer
  type PivotTable = P.G.PivotTable

  function IChildren(node: PNode) : imap<Key, Reference>
  requires P.WFNode(node);
  {
    if node.children.Some? then (
      imap key :: node.children.value[P.Route(node.pivotTable, key)]
    ) else (
      imap[]
    )
  }

  function IBufferInternal(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: P.BucketLookup(node.buckets[P.Route(node.pivotTable, key)], key)
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    imap key :: Merge(
      P.BucketLookup(node.buckets[P.Route(node.pivotTable, key)], key),
      Define(DefaultValue())
    )
  }

  function IBuffer(node: PNode) : Buffer
  requires P.WFNode(node);
  {
    if node.children.Some? then
      IBufferInternal(node)
    else
      IBufferLeaf(node)
  }

  function INode(node: PNode) : Node
  requires P.WFNode(node);
  {
    B.G.Node(IChildren(node), IBuffer(node))
  }

  lemma WFNodeRefinesWFNode(node: PNode)
  requires P.WFNode(node)
  ensures B.WFNode(INode(node))
  {
  }

  function IInsertion(ins: P.MessageInsertion) : B.MessageInsertion
  requires P.ValidInsertion(ins)
  {
    B.MessageInsertion(ins.key, ins.msg, INode(ins.oldroot))
  }

  function KeysForSlot(node: PNode, slotIndex: int) : iset<Key>
  requires P.WFPivotTable(node.pivotTable)
  {
    iset key | P.Route(node.pivotTable, key) == slotIndex
  }

  function IFlush(flush: P.NodeFlush) : B.NodeFlush
  requires P.ValidFlush(flush)
  {
    B.NodeFlush(flush.parentref, INode(flush.parent), flush.childref, INode(flush.child), flush.newchildref, KeysForSlot(flush.parent, flush.slotIndex))
  }

  function IGrow(growth: P.RootGrowth) : B.RootGrowth
  requires P.ValidGrow(growth)
  {
    B.RootGrowth(INode(growth.oldroot), growth.newchildref)
  }

  function leftKeys(fusion: P.NodeFusion) : iset<Key>
  requires P.ValidFusion(fusion)
  {
    iset key |
      && Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx])
      && (fusion.slot_idx == 0 || Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx - 1], key))
  }

  function rightKeys(fusion: P.NodeFusion) : iset<Key>
  requires P.ValidFusion(fusion)
  {
    iset key |
      && Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx], key)
      && (fusion.slot_idx == |fusion.split_parent.pivotTable| - 1 ||
          Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx + 1]))
  }

  function IFusion(fusion: P.NodeFusion) : B.NodeFusion
  requires P.ValidFusion(fusion)
  {
    B.NodeFusion(
      fusion.parentref,
      fusion.fused_childref,
      fusion.left_childref,
      fusion.right_childref,
      INode(fusion.fused_parent),
      INode(fusion.split_parent),
      INode(fusion.fused_child),
      INode(fusion.left_child),
      INode(fusion.right_child),
      leftKeys(fusion),
      rightKeys(fusion)
    )
  }

  function IStep(betreeStep: P.BetreeStep) : B.BetreeStep
  requires P.ValidBetreeStep(betreeStep)
  {
    match betreeStep {
      case BetreeInsert(ins) => B.BetreeInsert(IInsertion(ins))
      case BetreeFlush(flush) => B.BetreeFlush(IFlush(flush))
      case BetreeGrow(growth) => B.BetreeGrow(IGrow(growth))
      case BetreeSplit(fusion) => B.BetreeSplit(IFusion(fusion))
      case BetreeMerge(fusion) => B.BetreeMerge(IFusion(fusion))
    }
  }

  lemma RefinesValidInsertion(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  ensures B.ValidInsertion(IInsertion(ins))
  {
  }

  lemma RefinesValidFlush(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  ensures B.ValidFlush(IFlush(flush))
  {
  }

  lemma RefinesValidGrow(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  ensures B.ValidGrow(IGrow(growth))
  {
  }

  lemma RouteIs(pivots: PivotTable, key: Key, idx: int)
  requires P.WFPivotTable(pivots)
  requires 0 <= idx <= |pivots|
  requires idx > 0 ==> Keyspace.lte(pivots[idx-1], key);
  requires idx < |pivots| ==> Keyspace.lt(key, pivots[idx]);
  ensures P.Route(pivots, key) == idx;
  {
  }

  lemma RefinesValidFusion(fusion: P.NodeFusion)
  requires P.ValidFusion(fusion)
  ensures B.ValidFusion(IFusion(fusion))
  {
    forall key | key in IFusion(fusion).left_keys
    ensures IMapsTo(IFusion(fusion).fused_parent.children, key, IFusion(fusion).fused_childref)
    {
      //assert Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx]);
      //assert (fusion.slot_idx == 0 || Keyspace.lte(fusion.split_parent.pivotTable[fusion.slot_idx - 1], key));

      /*
      if (fusion.slot_idx > 0) {
        assert fusion.split_parent.pivotTable[fusion.slot_idx - 1]
            == fusion.fused_parent.pivotTable[fusion.slot_idx - 1];
      }
      */
      if (fusion.slot_idx < |fusion.fused_parent.pivotTable|) {
        //assert fusion.fused_parent.pivotTable[fusion.slot_idx] == fusion.split_parent.pivotTable[fusion.slot_idx + 1];
        Keyspace.IsStrictlySortedImpliesLt(fusion.split_parent.pivotTable, fusion.slot_idx, fusion.slot_idx + 1);
        /*
        assert Keyspace.lt(
                fusion.split_parent.pivotTable[fusion.slot_idx],
                fusion.split_parent.pivotTable[fusion.slot_idx + 1]);
        assert Keyspace.lt(
                fusion.split_parent.pivotTable[fusion.slot_idx],
                fusion.fused_parent.pivotTable[fusion.slot_idx]);
        */
      }

      /*
      assert fusion.slot_idx > 0 ==> Keyspace.lte(fusion.fused_parent.pivotTable[fusion.slot_idx-1], key);
      assert fusion.slot_idx < |fusion.fused_parent.pivotTable| ==> Keyspace.lt(key, fusion.fused_parent.pivotTable[fusion.slot_idx]);
      */

      RouteIs(fusion.fused_parent.pivotTable, key, fusion.slot_idx);
      /*
      assert P.Route(fusion.fused_parent.pivotTable, key) == fusion.slot_idx;
      assert fusion.fused_parent.children.value[fusion.slot_idx] == fusion.fused_childref;
      assert fusion.fused_parent.children.value[P.Route(fusion.fused_parent.pivotTable, key)] == fusion.fused_childref;
      assert IMapsTo(IChildren(fusion.fused_parent), key, fusion.fused_childref);
      */
    }

    forall key | key in IFusion(fusion).right_keys
    ensures IMapsTo(IFusion(fusion).fused_parent.children, key, IFusion(fusion).fused_childref)
    {
      if (fusion.slot_idx > 0) {
        Keyspace.IsStrictlySortedImpliesLt(fusion.split_parent.pivotTable, fusion.slot_idx - 1, fusion.slot_idx);
      }
      RouteIs(fusion.fused_parent.pivotTable, key, fusion.slot_idx);
    }

    /*
    forall key | (key !in IFusion(fusion).left_keys) && (key !in IFusion(fusion).right_keys)
    ensures IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key)
    {
      var r := P.Route(fusion.fused_parent.pivotTable, key);
      if (r < fusion.slot_idx) {
        //assert fusion.split_parent.children.Some?;
        RouteIs(fusion.split_parent.pivotTable, key, r);
        /*
        assert r == P.Route(fusion.split_parent.pivotTable, key);
        assert IChildren(fusion.split_parent)[key] == fusion.split_parent.children.value[r];
        assert IChildren(fusion.split_parent)[key] == fusion.split_parent.children.value[r];
        assert IChildren(fusion.fused_parent)[key] == fusion.fused_parent.children.value[r];
        assert fusion.split_parent.children.value[r] == fusion.fused_parent.children.value[r];
        */

        assert IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key);
      } else if (r == fusion.slot_idx) {
        var pivot := fusion.split_parent.pivotTable[fusion.slot_idx];
        if (Keyspace.lte(pivot, key)) {
          if (fusion.slot_idx + 1 < |fusion.split_parent.pivotTable|) {
            assert fusion.split_parent.pivotTable[r + 1] == fusion.fused_parent.pivotTable[r];
            //assert Keyspace.lt(key, fusion.split_parent.pivotTable[r + 1]);
            //assert Keyspace.lt(key, fusion.split_parent.pivotTable[fusion.slot_idx + 1]);
          }
          assert key in IFusion(fusion).right_keys;
        } else {
          //assert Keyspace.lt(key, pivot);
          assert key in IFusion(fusion).left_keys;
        }
      } else {
        assert fusion.fused_parent.pivotTable[r-1] == fusion.split_parent.pivotTable[r];
        //assert Keyspace.lte(fusion.fused_parent.pivotTable[r-1], key);
        //assert Keyspace.lte(fusion.split_parent.pivotTable[r], key);

        if (r+1 < |fusion.split_parent.pivotTable|) {
          assert fusion.fused_parent.pivotTable[r] == fusion.split_parent.pivotTable[r + 1];
          //assert Keyspace.lt(key, fusion.fused_parent.pivotTable[r]);
          //assert Keyspace.lt(key, fusion.split_parent.pivotTable[r + 1]);
        }

        RouteIs(fusion.split_parent.pivotTable, key, r + 1);
        assert IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key);
      }
    }
    */

    forall key
    ensures P.BucketLookup(fusion.split_parent.buckets[P.Route(fusion.split_parent.pivotTable, key)], key)
         == P.BucketLookup(fusion.fused_parent.buckets[P.Route(fusion.fused_parent.pivotTable, key)], key)
    ensures (key !in IFusion(fusion).left_keys) && (key !in IFusion(fusion).right_keys) ==> IMapsAgreeOnKey(IFusion(fusion).split_parent.children, IFusion(fusion).fused_parent.children, key)
    {
      var r := P.Route(fusion.fused_parent.pivotTable, key);
      if (r < fusion.slot_idx) {
        RouteIs(fusion.split_parent.pivotTable, key, r);
      } else if (r == fusion.slot_idx) {
        var pivot := fusion.split_parent.pivotTable[fusion.slot_idx];
        if (Keyspace.lte(pivot, key)) {
          if (fusion.slot_idx + 1 < |fusion.split_parent.pivotTable|) {
            assert fusion.split_parent.pivotTable[r + 1] == fusion.fused_parent.pivotTable[r];
          }
          assert key in IFusion(fusion).right_keys;
        } else {
          assert key in IFusion(fusion).left_keys;
        }
      } else {
        assert fusion.fused_parent.pivotTable[r-1] == fusion.split_parent.pivotTable[r];

        if (r+1 < |fusion.split_parent.pivotTable|) {
          assert fusion.fused_parent.pivotTable[r] == fusion.split_parent.pivotTable[r + 1];
        }

        RouteIs(fusion.split_parent.pivotTable, key, r + 1);
      }
    }

    var child := fusion.fused_child;
    var left := fusion.left_child;
    var right := fusion.right_child;

    forall key | key in IFusion(fusion).left_keys
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.children, IFusion(fusion).left_child.children, key)
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.buffer, IFusion(fusion).left_child.buffer, key)
    {
      var r := P.Route(left.pivotTable, key);
      RouteIs(child.pivotTable, key, r);
    }

    forall key | key in IFusion(fusion).right_keys
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.children, IFusion(fusion).right_child.children, key)
    ensures IMapsAgreeOnKey(IFusion(fusion).fused_child.buffer, IFusion(fusion).right_child.buffer, key)
    {
      var r := P.Route(right.pivotTable, key);
      if (r > 0) {
        assert right.pivotTable[r-1] == child.pivotTable[r + |left.buckets| - 1];
      }
      if (r < |right.pivotTable|) {
        assert right.pivotTable[r] == child.pivotTable[r + |left.buckets|];
      }
      RouteIs(child.pivotTable, key, r + |left.buckets|);
    }
  }

  lemma RefinesValidBetreeStep(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  ensures B.ValidBetreeStep(IStep(betreeStep))
  {
    match betreeStep {
      case BetreeInsert(ins) => RefinesValidInsertion(ins);
      case BetreeFlush(flush) => RefinesValidFlush(flush);
      case BetreeGrow(growth) => RefinesValidGrow(growth);
      case BetreeSplit(fusion) => RefinesValidFusion(fusion);
      case BetreeMerge(fusion) => RefinesValidFusion(fusion);
    }
  }

  function IReadOp(readOp: P.G.ReadOp) : B.G.ReadOp
  requires P.WFNode(readOp.block)
  {
    B.G.ReadOp(readOp.ref, INode(readOp.block))
  }

  function IReadOps(readOps: seq<P.G.ReadOp>) : seq<B.G.ReadOp>
  requires forall i | 0 <= i < |readOps| :: P.WFNode(readOps[i].block)
  {
    if |readOps| == 0 then [] else
      IReadOps(readOps[..|readOps|-1]) + [IReadOp(readOps[|readOps|-1])]
  }

  lemma {:fuel IReadOps,3} RefinesReadOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);
    /*
    match betreeStep {
      case BetreeInsert(ins) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeFlush(flush) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeGrow(growth) => {
        assert IReadOps(P.BetreeStepReads(betreeStep))
            == IReadOps([P.G.ReadOp(P.G.Root(), growth.oldroot)])
            == [B.G.ReadOp(P.G.Root(), INode(growth.oldroot))]
            == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeSplit(fusion) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
      case BetreeMerge(fusion) => {
        assert IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep));
      }
    }
    */
  }

  function IOp(op: P.G.Op) : B.G.Op
  requires P.WFNode(op.block)
  {
    match op {
      case AllocOp(ref, block) => B.G.AllocOp(ref, INode(block))
      case WriteOp(ref, block) => B.G.WriteOp(ref, INode(block))
    }
  }

  function IOps(ops: seq<P.G.Op>) : seq<B.G.Op>
  requires forall i | 0 <= i < |ops| :: P.WFNode(ops[i].block)
  {
    if |ops| == 0 then [] else
      IOps(ops[..|ops|-1]) + [IOp(ops[|ops|-1])]
  }

  lemma InsertRefinesOps(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires B.ValidInsertion(IInsertion(ins))
  ensures forall i | 0 <= i < |P.InsertionOps(ins)| ::
      P.WFNode(P.InsertionOps(ins)[i].block)
  ensures IOps(P.InsertionOps(ins)) == B.InsertionOps(IInsertion(ins))
  {
    var newroot := P.AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var newroot' := B.AddMessageToNode(INode(ins.oldroot), ins.key, ins.msg);

    forall key
    ensures INode(newroot).buffer[key] == newroot'.buffer[key]
    {
      if (key == ins.key) {
        var oldroot := ins.oldroot;
        var oldroot' := IInsertion(ins).oldroot;
        // IBuffer splits into cases based on whether a node is a leaf
        // so we have to split into cases here.
        if (oldroot.children.Some?) {
          assert INode(newroot).buffer[key] == newroot'.buffer[key];
        } else {
          MergeIsAssociative(
            ins.msg,
            P.BucketLookup(oldroot.buckets[P.Route(oldroot.pivotTable, ins.key)], ins.key),
            Define(DefaultValue())
          );
          assert INode(newroot).buffer[key] == newroot'.buffer[key];
        }
      } else {
        assert INode(newroot).buffer[key] == newroot'.buffer[key];
      }
    }

    assert INode(newroot).children == newroot'.children;
    assert INode(newroot).buffer == newroot'.buffer;

    assert INode(newroot) == newroot';
  }

  lemma FlushRefinesOps(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires B.ValidFlush(IFlush(flush))
  ensures forall i | 0 <= i < |P.FlushOps(flush)| ::
      P.WFNode(P.FlushOps(flush)[i].block)
  ensures IOps(P.FlushOps(flush)) == B.FlushOps(IFlush(flush))
  {
  }

  lemma {:fuel IOps,3} GrowRefinesOps(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires B.ValidGrow(IGrow(growth))
  ensures forall i | 0 <= i < |P.GrowOps(growth)| ::
      P.WFNode(P.GrowOps(growth)[i].block)
  ensures IOps(P.GrowOps(growth)) == B.GrowOps(IGrow(growth))
  {
    var newroot := P.G.Node([], Some([growth.newchildref]), [map[]]);
    var newroot' := B.G.Node(
        imap key | MS.InDomain(key) :: IGrow(growth).newchildref,
        imap key | MS.InDomain(key) :: B.G.M.Update(B.G.M.NopDelta()));
    assert INode(newroot) == newroot';
    //assert INode(growth.oldroot) == IGrow(growth).oldroot;

    //assert B.GrowOps(IGrow(growth))[0] 
    //    == B.G.AllocOp(IGrow(growth).newchildref, IGrow(growth).oldroot);

    // observe: (I don't know really know why this is necessary)
    assert B.GrowOps(IGrow(growth))[1] 
        == B.G.WriteOp(B.G.Root(), newroot');

    /*
    assert IOps(P.GrowOps(growth))
        == IOps([P.G.AllocOp(growth.newchildref, growth.oldroot), P.G.WriteOp(P.G.Root(), newroot)])
        == [B.G.AllocOp(growth.newchildref, INode(growth.oldroot)), B.G.WriteOp(B.G.Root(), INode(newroot))]
        == [B.G.AllocOp(IGrow(growth).newchildref, IGrow(growth).oldroot), B.G.WriteOp(B.G.Root(), newroot')]
        == B.GrowOps(IGrow(growth));
    */
  }

  lemma {:fuel IOps,3} RefinesOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
      P.WFNode(P.BetreeStepOps(betreeStep)[i].block)
  ensures IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);

    match betreeStep {
      case BetreeInsert(ins) => {
        InsertRefinesOps(ins);
      }
      case BetreeFlush(flush) => {
        FlushRefinesOps(flush);
      }
      case BetreeGrow(growth) => {
        GrowRefinesOps(growth);
      }
      case BetreeSplit(fusion) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.WFNode(P.BetreeStepOps(betreeStep)[i].block);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
      case BetreeMerge(fusion) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.WFNode(P.BetreeStepOps(betreeStep)[i].block);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
    }
  }
}

module PivotBetree {
  import opened PivotBetreeSpec`Internal

  import BI = PivotBetreeBlockInterface
  import MS = MapSpec
  import opened Maps
  import opened MissingLibrary

  import opened G = PivotBetreeGraph

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)
  type UIOp = MS.UI.Op<Value>

  function EmptyNode() : Node
  {
    Node([], None, [map[]])
  }

  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv, EmptyNode())
  }

  predicate GC(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>) {
    && uiop.NoOp? 
    && BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(k.bck, s.bcv, s'.bcv, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, uiop)
  }
 
  datatype Step =
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)
    | StutterStep

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step) {
    match step {
      case BetreeStep(betreeStep) => Betree(k, s, s', uiop, betreeStep)
      case GCStep(refs) => GC(k, s, s', uiop, refs)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step: Step :: NextStep(k, s, s', uiop, step)
  }
}

module PivotBetreeInvAndRefinement {
  import opened PivotBetreeSpec`Spec
  import PB = PivotBetree
  import PBI = PivotBetreeBlockInterface
  import B = Betree
  import BInv = BetreeInv
  import BG = BetreeGraph
  import PG = PivotBetreeGraph
  import BI = BetreeBlockInterface
  import SpecRef = PivotBetreeSpecRefinement

  type Constants = PB.Constants
  type Variables = PB.Variables
  type Reference = BG.Reference
  type PNode = PG.Node
  type Node = BG.Node
  type UIOp = B.UIOp

  function Ik(k: Constants) : B.Constants
  {
    B.Constants(BI.Constants())
  }

  predicate ViewHasWFNodes(view: imap<Reference, PNode>)
  {
    forall ref | ref in view :: WFNode(view[ref])
  }

  function IView(view: imap<Reference, PNode>) : imap<Reference, Node>
  requires ViewHasWFNodes(view)
  {
    imap ref | ref in view :: SpecRef.INode(view[ref])
  }
  
  function I(k: Constants, s: Variables) : B.Variables
  requires ViewHasWFNodes(s.bcv.view)
  {
    B.Variables(BI.Variables(IView(s.bcv.view)))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && ViewHasWFNodes(s.bcv.view)
    && BInv.Inv(Ik(k), I(k, s))
  }

  lemma OpRefines(k: Constants, s: Variables, s': Variables, op: PG.Op)
  requires WFNode(op.block)
  requires ViewHasWFNodes(s.bcv.view)
  requires PBI.OpStep(k.bck, s.bcv, s'.bcv, op)
  ensures ViewHasWFNodes(s'.bcv.view)
  ensures BI.OpStep(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOp(op))
  {
    //BI.OpStepPreservesInv(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOp(op));
  }

  lemma IOpsAdditive(ops1: seq<PG.Op>, ops2: seq<PG.Op>)
  requires forall i | 0 <= i < |ops1| :: WFNode(ops1[i].block)
  requires forall i | 0 <= i < |ops2| :: WFNode(ops2[i].block)
  ensures SpecRef.IOps(ops1 + ops2) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2)
  {
    if (|ops2| == 0) {
      assert ops2 == [];
      assert SpecRef.IOps(ops2) == [];
      assert ops1 + ops2 == ops1;
      assert SpecRef.IOps(ops1 + ops2) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2);
    } else {
      IOpsAdditive(ops1, ops2[..|ops2|-1]);
      assert (ops1 + ops2)[..|ops1 + ops2|-1] == ops1 + ops2[..|ops2|-1];
      assert SpecRef.IOps(ops1 + ops2)
          == SpecRef.IOps((ops1 + ops2)[..|ops1 + ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1 + ops2[..|ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2[..|ops2|-1]) + [SpecRef.IOp((ops1 + ops2)[|ops1 + ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2[..|ops2|-1]) + [SpecRef.IOp(ops2[|ops2| - 1])]
          == SpecRef.IOps(ops1) + SpecRef.IOps(ops2);
    }
  }

  lemma TransactionRefines(k: Constants, s: Variables, s': Variables, ops: seq<PG.Op>)
  requires forall i | 0 <= i < |ops| :: WFNode(ops[i].block)
  requires ViewHasWFNodes(s.bcv.view)
  requires PBI.Transaction(k.bck, s.bcv, s'.bcv, ops)
  ensures ViewHasWFNodes(s'.bcv.view)
  ensures BI.Transaction(Ik(k).bck, I(k, s).bcv, I(k, s').bcv, SpecRef.IOps(ops))
  decreases |ops|
  {
    if (|ops| == 1) {
      OpRefines(k, s, s', ops[0]);
    } else {
      var ops1, mid, ops2 := PBI.SplitTransaction(k.bck, s.bcv, s'.bcv, ops);
      var smid := PB.Variables(mid);

      forall i | 0 <= i < |ops1| ensures WFNode(ops1[i].block)
      {
        assert ops1[i].block == ops[i].block;
      }
      forall i | 0 <= i < |ops2| ensures WFNode(ops2[i].block)
      {
        assert ops2[i].block == ops[i + |ops1|].block;
      }

      TransactionRefines(k, s, smid, ops1);
      TransactionRefines(k, smid, s', ops2);
      BI.JoinTransactions(Ik(k).bck, I(k, s).bcv, I(k, smid).bcv, I(k, s').bcv, SpecRef.IOps(ops1), SpecRef.IOps(ops2));
      IOpsAdditive(ops1, ops2);
      //assert SpecRef.IOps(ops) == SpecRef.IOps(ops1) + SpecRef.IOps(ops2); // TODO
    }
  }

  lemma BetreeStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  requires Inv(k, s)
  requires PB.NextStep(k, s, s', uiop, PB.BetreeStep(betreeStep))
  ensures Inv(k, s')
  ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)))
  {
    SpecRef.RefinesValidBetreeStep(betreeStep);
    SpecRef.RefinesReadOps(betreeStep);
    SpecRef.RefinesOps(betreeStep);
    TransactionRefines(k, s, s', BetreeStepOps(betreeStep));
    assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.BetreeStep(SpecRef.IStep(betreeStep)));
    BInv.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma GCStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>)
  requires Inv(k, s)
  requires PB.NextStep(k, s, s', uiop, PB.GCStep(refs))
  ensures Inv(k, s')
  ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.GCStep(refs))
  {
    assert B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.GCStep(refs));
    BInv.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma StutterStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires PB.NextStep(k, s, s', uiop, PB.StutterStep)
  ensures Inv(k, s')
  ensures B.NextStep(Ik(k), I(k,s), I(k,s'), uiop, B.StutterStep)
  {
  }

  lemma PivotBetreeRefinesBetreeNextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: PB.Step)
    requires Inv(k, s)
    requires PB.NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case BetreeStep(betreeStep) => BetreeStepRefines(k, s, s', uiop, betreeStep);
      case GCStep(refs) => GCStepRefines(k, s, s', uiop, refs);
      case StutterStep => StutterStepRefines(k, s, s', uiop);
    }
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires PB.Init(k, s)
    ensures Inv(k, s)
  {
    PivotBetreeRefinesBetreeInit(k, s);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires PB.Next(k, s, s', uiop)
    ensures Inv(k, s')
  {
    var step :| PB.NextStep(k, s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(k, s, s', uiop, step);
  }

  lemma PivotBetreeRefinesBetreeInit(k: Constants, s: Variables)
    requires PB.Init(k, s)
    ensures Inv(k, s)
    ensures B.Init(Ik(k), I(k, s))
  {
    assert SpecRef.INode(PB.EmptyNode()) == B.EmptyNode();
    BInv.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma PivotBetreeRefinesBetreeNext(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires PB.Next(k, s, s', uiop)
    ensures Inv(k, s')
    ensures B.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| PB.NextStep(k, s, s', uiop, step);
    PivotBetreeRefinesBetreeNextStep(k, s, s', uiop, step);
  }
}
