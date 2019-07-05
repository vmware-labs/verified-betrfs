include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "../lib/Sets.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../tla-tree/MissingLibrary.dfy"
include "Message.dfy"
include "BetreeSpec.dfy"
include "Betree.dfy"
include "PivotsLib.dfy"

module PivotBetreeGraph refines Graph {
  import BG = BetreeGraph

  import MS = MapSpec
  import opened MissingLibrary
  import M = ValueMessage

  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element
  type Value = BG.Value

  //type Reference = BG.Reference
  //function Root() : Reference { BG.Root() }
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
  import Pivots = PivotsLib

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, WFNode
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  // We require that all keys in a bucket map actually fit into that bucket
  // according to the pivot table.
  predicate WFBucket(bucket: Bucket, pivotTable: Pivots.PivotTable, i: int)
  requires Pivots.WFPivots(pivotTable)
  {
    && (forall key | key in bucket :: Pivots.Route(pivotTable, key) == i)
    && (forall key | key in bucket :: bucket[key] != M.IdentityMessage())
  }

  predicate NodeHasWFBucketAt(node: Node, i: int)
  requires Pivots.WFPivots(node.pivotTable)
  requires 0 <= i < |node.buckets|
  {
    WFBucket(node.buckets[i], node.pivotTable, i)
  }

  predicate NodeHasWFBuckets(node: Node)
  requires Pivots.WFPivots(node.pivotTable)
  {
    (forall i | 0 <= i < |node.buckets| :: NodeHasWFBucketAt(node, i))
  }

  // TODO it would be reasonable to impose additional constraints like:
  //  - No deltas at leaves
  //  - No default values at leaves
  predicate WFNode(node: Node)
  {
    && Pivots.NumBuckets(node.pivotTable) == |node.buckets|
    && (node.children.Some? ==> |node.buckets| == |node.children.value|)
    && Pivots.WFPivots(node.pivotTable)
    && NodeHasWFBuckets(node)
  }

  // Adding messages to buffers

  // TODO it might be a good idea to factor out the conept of "bucket" so that it has
  // a more imap-like interface (while still being backed by a finite map) so that we don't
  // have to deal with all the identity-message special cases in here.

  function method BucketLookup(bucket: Bucket, key: Key) : Message {
    if key in bucket then bucket[key] else M.IdentityMessage()
  }

  function method AddMessageToBucket(bucket: Bucket, key: Key, msg: Message) : Bucket
  {
    var msg := M.Merge(msg, BucketLookup(bucket, key));
    if msg == M.IdentityMessage() then
      MapRemove(bucket, {key})
    else
      bucket[key := msg]
  }

  function method AddMessageToNode(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  ensures WFNode(AddMessageToNode(node, key, msg))
  {
    var newnode := node.(
      buckets := node.buckets[
        Pivots.Route(node.pivotTable, key) := AddMessageToBucket(node.buckets[Pivots.Route(node.pivotTable, key)], key, msg)
      ]
    );
    assert forall i | 0 <= i < |newnode.buckets| :: NodeHasWFBucketAt(node, i) ==> NodeHasWFBucketAt(newnode, i);
    newnode
  }

  function AddMessagesToBucket(pivotTable: PivotTable, i: int, childBucket: map<Key, Message>, parentBucket: map<Key, Message>) : Bucket
  requires Pivots.WFPivots(pivotTable)
  ensures forall key | key in AddMessagesToBucket(pivotTable, i, childBucket, parentBucket) :: Pivots.Route(pivotTable, key) == i
  {
    map key
    | && (key in (childBucket.Keys + parentBucket.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Pivots.Route(pivotTable, key) == i
      && M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key)) != M.IdentityMessage()
    :: M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key))
  }

  function AddMessagesToBuckets(pivotTable: PivotTable, i: int, buckets: seq<map<Key, Message>>, parentBucket: map<Key, Message>) : seq<Bucket>
  requires Pivots.WFPivots(pivotTable)
  requires 0 <= i <= |buckets|;
  ensures |AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)| == i
  ensures forall j | 0 <= j < i :: forall key | key in AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[j] :: Pivots.Route(pivotTable, key) == j
  ensures forall j | 0 <= j < i :: forall key | key in AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[j] :: AddMessagesToBuckets(pivotTable, i, buckets, parentBucket)[j][key] != M.IdentityMessage()
  {
    if i == 0 then [] else (
      AddMessagesToBuckets(pivotTable, i-1, buckets, parentBucket) + [AddMessagesToBucket(pivotTable, i-1, buckets[i-1], parentBucket)]
    )
  }

  function AddMessagesToNode(node: Node, buffer: map<Key, Message>) : Node
  requires WFNode(node)
  ensures WFNode(AddMessagesToNode(node, buffer))
  {
    Node(
      node.pivotTable,
      node.children,
      AddMessagesToBuckets(node.pivotTable, |node.buckets|, node.buckets, buffer)
    )
  }

  //// Query

  type Layer = G.ReadOp
  type Lookup = seq<Layer>

  datatype LookupQuery = LookupQuery(key: Key, value: Value, lookup: Lookup)

  predicate BufferIsDefining(entry: M.Message) {
    && entry.Define?
  }

  predicate BufferDefinesValue(log: M.Message, value: Value) {
    && BufferIsDefining(log)
    && log.value == value
  }

  predicate ValidLayerIndex(lookup: Lookup, idx: int) {
    && 0 <= idx < |lookup|
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate LookupFollowsChildRefAtLayer(key: Key, lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx)
  requires idx < |lookup| - 1;
  requires WFNode(lookup[idx].node)
  {
    && lookup[idx].node.children.Some?
    && lookup[idx].node.children.value[Pivots.Route(lookup[idx].node.pivotTable, key)] == lookup[idx+1].ref
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(key, lookup, idx))
  }

  function NodeLookup(node: Node, key: Key) : Message
  requires WFNode(node)
  {
    BucketLookup(node.buckets[Pivots.Route(node.pivotTable, key)], key)
  }

  function InterpretLookup(lookup: Lookup, key: Key) : G.M.Message
  requires LookupVisitsWFNodes(lookup)
  {
    if |lookup| == 0 then
      G.M.Update(G.M.NopDelta())
    else
      G.M.Merge(InterpretLookup(DropLast(lookup), key), NodeLookup(Last(lookup).node, key))
  }

  function InterpretLookupAccountingForLeaf(lookup: Lookup, key: Key) : G.M.Message
  requires |lookup| > 0
  requires LookupVisitsWFNodes(lookup)
  {
    if Last(lookup).node.children.Some? then
      InterpretLookup(lookup, key)
    else
      G.M.Merge(InterpretLookup(lookup, key), M.DefineDefault())
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupVisitsWFNodes(lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  predicate ValidQuery(q: LookupQuery) {
    && WFLookupForKey(q.lookup, q.key)
    && BufferDefinesValue(InterpretLookupAccountingForLeaf(q.lookup, q.key), q.value)
  }

  function QueryReads(q: LookupQuery): seq<ReadOp> {
    q.lookup
  }

  function QueryOps(q: LookupQuery): seq<Op> {
    []
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
    var newparent := Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := map[]]
      );
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
    
    slot_idx: int,
    num_children_left: int,
    pivot: Key
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

  // TODO get rid of this from the spec (or keep it around to use as proof tool?)
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

  function SplitBucketLeft(bucket: map<Key, Message>, pivot: Key) : map<Key, Message>
  {
    map key | key in bucket && Keyspace.lt(key, pivot) :: bucket[key]
  }

  function SplitBucketRight(bucket: map<Key, Message>, pivot: Key) : map<Key, Message>
  {
    map key | key in bucket && Keyspace.lte(pivot, key) :: bucket[key]
  }

  predicate ValidSplit(fusion: NodeFusion)
  {
    && WFNode(fusion.fused_parent)
    && WFNode(fusion.fused_child)
    && fusion.fused_parent.children.Some?
    && 0 <= fusion.slot_idx < |fusion.fused_parent.buckets|
    && 1 <= fusion.num_children_left < |fusion.fused_child.buckets|
    && fusion.fused_parent.children.value[fusion.slot_idx] == fusion.fused_childref
    && fusion.fused_child.pivotTable[fusion.num_children_left - 1] == fusion.pivot
    // TODO add condition that pivot fits in the slot_idx bucket

    // TODO consider requiring that the bucket being split is simply empty already

    && fusion.split_parent == Node(
      insert(fusion.fused_parent.pivotTable, fusion.pivot, fusion.slot_idx),
      Some(replace1with2(fusion.fused_parent.children.value, fusion.left_childref, fusion.right_childref, fusion.slot_idx)),
      replace1with2(fusion.fused_parent.buckets, SplitBucketLeft(fusion.fused_parent.buckets[fusion.slot_idx], fusion.pivot), SplitBucketRight(fusion.fused_parent.buckets[fusion.slot_idx], fusion.pivot), fusion.slot_idx)
    )

    && fusion.left_child == Node(
      fusion.fused_child.pivotTable[ .. fusion.num_children_left - 1 ],
      if fusion.fused_child.children.Some? then Some(fusion.fused_child.children.value[ .. fusion.num_children_left ]) else None,
      fusion.fused_child.buckets[ .. fusion.num_children_left ]
    )

    && fusion.right_child == Node(
      fusion.fused_child.pivotTable[ fusion.num_children_left .. ],
      if fusion.fused_child.children.Some? then Some(fusion.fused_child.children.value[ fusion.num_children_left .. ]) else None,
      fusion.fused_child.buckets[ fusion.num_children_left .. ]
    )
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
    && WFNode(fusion.split_parent)
    && WFNode(fusion.left_child)
    && WFNode(fusion.right_child)
    && 0 <= fusion.slot_idx < |fusion.split_parent.buckets| - 1
    && fusion.num_children_left == |fusion.left_child.buckets|
    && fusion.split_parent.pivotTable[fusion.slot_idx] == fusion.pivot
    && fusion.split_parent.children.Some?
    && fusion.split_parent.children.value[fusion.slot_idx] == fusion.left_childref
    && fusion.split_parent.children.value[fusion.slot_idx + 1] == fusion.right_childref

    // TODO require bucket to be empty before merge?
    /*
    && fusion.fused_parent == Node(
      remove(fusion.split_parent.pivotTable, fusion.slot_idx),
      Some(replace2with1(fusion.split_parent.children.value, fusion.split_childref, fusion.slot_idx)),
      replace2with1(fusion.split_parent.buckets, MergeBuckets(fusion.split_parent.buckets[fusion.slot_idx], fusion.split_parent.buckets[fusion.slot_idx + 1], fusion.pivot))
    )
    */

    // this is actually an invariant which follows from fixed height of the tree,
    // but we currently don't track that as an invariant... should we?
    && (fusion.left_child.children.Some? ==> fusion.right_child.children.Some?)
    && (fusion.left_child.children.None? ==> fusion.right_child.children.None?)

    // TODO this isn't quite right:
    // we need to cut out every key > pivot in leftChild
    // and likewise cut out every key < pivot in rightChild
    && fusion.fused_child == Node(
      concat3(fusion.left_child.pivotTable, fusion.pivot, fusion.right_child.pivotTable),
      if fusion.left_child.children.Some? then Some(fusion.left_child.children.value + fusion.right_child.children.value) else None,
      fusion.left_child.buckets + fusion.right_child.buckets
    )
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
    | BetreeQuery(q: LookupQuery)
    | BetreeInsert(ins: MessageInsertion)
    | BetreeFlush(flush: NodeFlush)
    | BetreeGrow(growth: RootGrowth)
    | BetreeSplit(fusion: NodeFusion)
    | BetreeMerge(fusion: NodeFusion)

  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
      case BetreeQuery(q) => ValidQuery(q)
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
      case BetreeQuery(q) => QueryReads(q)
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
      case BetreeQuery(q) => QueryOps(q)
      case BetreeInsert(ins) => InsertionOps(ins)
      case BetreeFlush(flush) => FlushOps(flush)
      case BetreeGrow(growth) => GrowOps(growth)
      case BetreeSplit(fusion) => SplitOps(fusion)
      case BetreeMerge(fusion) => MergeOps(fusion)
    }
  }

  predicate BetreeStepUI(step: BetreeStep, uiop: MS.UI.Op) {
    match step {
      case BetreeQuery(q) => uiop == MS.UI.GetOp(q.key, q.value)
      case BetreeInsert(ins) => ins.msg.Define? && uiop == MS.UI.PutOp(ins.key, ins.msg.value)
      case BetreeFlush(flush) => uiop.NoOp?
      case BetreeGrow(growth) => uiop.NoOp?
      case BetreeSplit(fusion) => uiop.NoOp?
      case BetreeMerge(fusion) => uiop.NoOp?
    }
  }
}

module PivotBetreeSpecWFNodes {
  import P = PivotBetreeSpec

  // This lemma is useful for BetreeBlockCache
  lemma ValidStepWritesWFNodes(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  ensures forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| :: P.WFNode(P.BetreeStepOps(betreeStep)[i].node)
  {
    // TODO
  }
}
