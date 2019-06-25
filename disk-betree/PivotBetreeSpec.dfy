include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../tla-tree/MissingLibrary.dfy"

module PivotBetreeGraph refines Graph {
  import MS = MapSpec
  import opened MissingLibrary

  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element
  type Value(!new)

  datatype BufferEntry = Insertion(value: Value) // TODO duplication

  datatype PivotTable = PivotTable(pivots: seq<Key>)
  datatype BufferPair = BufferPair(key: Key, entry: BufferEntry)

  datatype Bucket = Bucket(
      child: Option<Reference>,
      buffer: seq<BufferPair>)

  datatype Node = Node(
      pivotTable: PivotTable,
      buckets: seq<Bucket>)

  function Successors(node: Node) : iset<Reference>
  {
    iset i | 0 <= i < |node.buckets| && node.buckets[i].child.Some? :: node.buckets[i].child.value
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
    |pivotTable.pivots| + 1
  }

  predicate WFPivotTable(pivotTable: PivotTable)
  {
    Keyspace.IsStrictlySorted(pivotTable.pivots)
  }

  function Route(pivotTable: PivotTable, key: Key) : int
  requires WFPivotTable(pivotTable)
  {
    Keyspace.LargestLte(pivotTable.pivots, key) + 1
  }

  predicate WFNode(node: Node)
  {
    && PivotTableSize(node.pivotTable) == |node.buckets|
    && WFPivotTable(node.pivotTable)
    && (|node.buckets| > 1 ==> forall i | 0 <= i < |node.buckets| :: node.buckets[i].child.Some?)
  }

  // Adding messages to buffers

  function AddMessageToNode(node: Node, key: Key, msg: BufferEntry) : Node
  requires WFNode(node)
  ensures WFNode(AddMessageToNode(node, key, msg))
  {
    node.(
      buckets := node.buckets[
        Route(node.pivotTable, key) := Bucket(
          node.buckets[Route(node.pivotTable, key)].child,
          [BufferPair(key, msg)] + node.buckets[Route(node.pivotTable, key)].buffer
        )
      ]
    )
  }

  function AddMessagesToNode(node: Node, pairs: seq<BufferPair>) : Node
  requires WFNode(node)
  {
    if |pairs| == 0 then (
      node
    ) else (
      AddMessageToNode(AddMessagesToNode(node, pairs[1..]), pairs[0].key, pairs[0].entry)
    )
  }

  //// Insert

  datatype MessageInsertion = MessageInsertion(key: Key, msg: BufferEntry, oldroot: Node)

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

  datatype NodeFlush = NodeFlush(parentref: Reference, parent: Node, childref: Reference, child: Node, newchildref: Reference, slotIndex: int)

  predicate ValidFlush(flush: NodeFlush)
  {
    && WFNode(flush.parent)
    && WFNode(flush.child)
    && 0 <= flush.slotIndex < |flush.parent.buckets|
    && flush.parent.buckets[flush.slotIndex].child == Some(flush.childref)
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
    var newparent := flush.parent.(buckets := flush.parent.buckets[flush.slotIndex := Bucket(Some(flush.newchildref), [])]);
    var newchild := AddMessagesToNode(flush.child, flush.parent.buckets[flush.slotIndex].buffer);
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
    var newroot := Node(PivotTable([]), [Bucket(Some(growth.newchildref), [])]);
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

  predicate BufferFusion(
      fusedBuffer: seq<BufferPair>,
      leftBuffer: seq<BufferPair>,
      rightBuffer: seq<BufferPair>,
      pivot: Key)
  {
    if |fusedBuffer| == 0 then
      |leftBuffer| == 0 && |rightBuffer| == 0
    else (
      var key := fusedBuffer[0].key;
      if Keyspace.lt(key, pivot) then (
        && |leftBuffer| > 0
        && leftBuffer[0] == fusedBuffer[0]
        && BufferFusion(fusedBuffer[1..], leftBuffer[1..], rightBuffer, pivot)
      ) else (
        && |rightBuffer| > 0
        && rightBuffer[0] == rightBuffer[0]
        && BufferFusion(fusedBuffer[1..], leftBuffer, rightBuffer[1..], pivot)
      )
    )
  }

  predicate PivotTableFusion(table: PivotTable, left: PivotTable, right: PivotTable, pivot: Key)
  {
    && table.pivots == concat3(left.pivots, pivot, right.pivots)
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

    && fusion.fused_parent.buckets[fusion.slot_idx].child == Some(fusion.fused_childref)
    && fusion.split_parent.buckets[fusion.slot_idx].child == Some(fusion.left_childref)
    && fusion.split_parent.buckets[fusion.slot_idx + 1].child == Some(fusion.right_childref)
    && BufferFusion(
        fusion.fused_parent.buckets[fusion.slot_idx].buffer,
        fusion.split_parent.buckets[fusion.slot_idx].buffer,
        fusion.split_parent.buckets[fusion.slot_idx + 1].buffer,
        fusion.split_parent.pivotTable.pivots[fusion.slot_idx])

    && (forall i | 0 < i < fusion.slot_idx :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.buckets| :: fusion.fused_parent.buckets[i] == fusion.split_parent.buckets[i+1])

    && (forall i | 0 < i < fusion.slot_idx ::
        fusion.fused_parent.pivotTable.pivots[i] == fusion.split_parent.pivotTable.pivots[i])
    && (forall i | fusion.slot_idx < i < |fusion.fused_parent.pivotTable.pivots| ::
        fusion.fused_parent.pivotTable.pivots[i] == fusion.split_parent.pivotTable.pivots[i+1])

    && ChildFusion(
        fusion.fused_child,
        fusion.left_child,
        fusion.right_child,
        fusion.split_parent.pivotTable.pivots[fusion.slot_idx])
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
