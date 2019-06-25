include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../tla-tree/MissingLibrary.dfy"

module PivotBetreeGraph refines Graph {
  import MS = MapSpec
  import opened MissingLibrary

  type Message
  function DefaultMessage() : Message
  function Merge(a: Message, b: Message) : Message

  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element
  type Value(!new)

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

module PivotBetreeSpec {
  import MS = MapSpec
  import opened G = PivotBetreeGraph
  import opened Sequences
  import opened Maps
  import opened MissingLibrary

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, G
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
    if key in bucket then bucket[key] else DefaultMessage()
  }

  function AddMessageToBucket(bucket: Bucket, key: Key, msg: Message) : Bucket {
    bucket[key := Merge(msg, BucketLookup(bucket, key))]
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
      && Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key)) != DefaultMessage()
    :: Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key))
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
    true
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
    && PivotTableFusion(child.pivotTable, left.pivotTable, right.pivotTable, pivot)
  }

  predicate ValidFusion(fusion: NodeFusion)
  {
    && WFNode(fusion.split_parent)
    && WFNode(fusion.fused_parent)

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

    && (forall i | 0 < i < fusion.slot_idx :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.buckets| :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i+1])

    && (forall i | 0 < i < fusion.slot_idx ::
        fusion.fused_parent.pivotTable[i] == fusion.split_parent.pivotTable[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.pivotTable| ::
        fusion.fused_parent.pivotTable[i] == fusion.split_parent.pivotTable[i+1])

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

}
