include "BlockInterface.i.dfy"  
include "../lib/sequences.s.dfy"
include "../lib/Maps.s.dfy"
include "MapSpec.s.dfy"
include "Graph.i.dfy"
include "../lib/Option.s.dfy"
include "Message.i.dfy"
include "BetreeSpec.i.dfy"
include "Betree.i.dfy"
include "PivotsLib.i.dfy"
include "BucketsLib.i.dfy"
include "Bounds.i.dfy"
include "BucketWeights.i.dfy"

module PivotBetreeGraph refines Graph {
  import BG = BetreeGraph

  import MS = MapSpec
  import opened Options
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
  import opened Options
  import opened Bounds
  import Pivots = PivotsLib
  import Buckets = BucketsLib
  import opened BucketWeights

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, WFNode
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  predicate BoundedNode(node: Node)
  {
    && |node.buckets| <= MaxNumChildren()
    && WeightBucketList(node.buckets) <= MaxTotalBucketWeight()
  }

  // TODO it would be reasonable to impose additional constraints like:
  //  - No deltas at leaves
  //  - No default values at leaves
  predicate WFNode(node: Node)
  {
    && Pivots.NumBuckets(node.pivotTable) == |node.buckets|
    && (node.children.Some? ==> |node.buckets| == |node.children.value|)
    && Pivots.WFPivots(node.pivotTable)
    && Buckets.WFBucketList(node.buckets, node.pivotTable)
    && BoundedNode(node)
  }

  function AddMessageToNode(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  {
    var newnode := node.(
      buckets := Buckets.BucketListInsert(node.buckets, node.pivotTable, key, msg)
    );
    newnode
  }

  function AddMessagesToNode(node: Node, buffer: map<Key, Message>) : Node
  requires WFNode(node)
  {
    Buckets.WFBucketListFlush(buffer, node.buckets, node.pivotTable);

    Node(
      node.pivotTable,
      node.children,
      Buckets.BucketListFlush(buffer, node.buckets, node.pivotTable)
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
  requires Buckets.WFBucketList(node.buckets, node.pivotTable)
  {
    Buckets.BucketListGet(node.buckets, node.pivotTable, key)
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
    && WeightBucketList(ins.oldroot.buckets) + WeightKey(ins.key) + WeightMessage(ins.msg)
        <= MaxTotalBucketWeight()
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
    && WeightBucketList(flush.child.buckets) + WeightBucket(flush.parent.buckets[flush.slotIndex]) <= MaxTotalBucketWeight()
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

  //// Datatype for Split and Merge

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

  //// Useful functions and lemmas for Split, Merge (other redirects)

  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures |node'.pivotTable| > 0 ==> Keyspace.lt(Last(node'.pivotTable), pivot)
  ensures forall key | key in Last(node'.buckets) :: Keyspace.lt(key, pivot)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var leftBuckets := Buckets.SplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    Buckets.WFSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    WeightSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    Node(leftPivots, leftChildren, leftBuckets)
  }

  function {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures |node'.pivotTable| > 0 ==> Keyspace.lt(pivot, node'.pivotTable[0])
  ensures forall key | key in node'.buckets[0] :: Keyspace.lte(pivot, key)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var rightBuckets := Buckets.SplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    Buckets.WFSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
    WeightSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    Node(rightPivots, rightChildren, rightBuckets)
  }

  lemma CutoffNodeCorrect(node: Node, node1: Node, node2: Node, lpivot: Key, rpivot: Key)
  requires WFNode(node)
  requires node1 == CutoffNodeAndKeepLeft(node, rpivot);
  requires node2 == CutoffNodeAndKeepRight(node1, lpivot);
  ensures |node2.pivotTable| > 0 ==> Keyspace.lt(lpivot, node2.pivotTable[0])
  ensures |node2.pivotTable| > 0 ==> Keyspace.lt(Last(node2.pivotTable), rpivot)
  ensures forall key | key in node2.buckets[0] :: Keyspace.lte(lpivot, key)
  ensures forall key | key in Last(node2.buckets) :: Keyspace.lt(key, rpivot)
  {
    reveal_CutoffNodeAndKeepLeft();
    reveal_CutoffNodeAndKeepRight();
    if (|node2.pivotTable| > 0) {
      assert node2.pivotTable[0]
          == node1.pivotTable[|node1.pivotTable| - |node2.pivotTable|];
      Keyspace.IsStrictlySortedImpliesLte(node1.pivotTable, 0, |node1.pivotTable| - |node2.pivotTable|);
    }
  }

  function {:opaque} CutoffNode(node: Node, lpivot: Option<Key>, rpivot: Option<Key>) : (node' : Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures lpivot.Some? && |node'.pivotTable| > 0 ==> Keyspace.lt(lpivot.value, node'.pivotTable[0])
  ensures rpivot.Some? && |node'.pivotTable| > 0 ==> Keyspace.lt(Last(node'.pivotTable), rpivot.value)
  ensures lpivot.Some? ==> forall key | key in node'.buckets[0] :: Keyspace.lte(lpivot.value, key)
  ensures rpivot.Some? ==> forall key | key in Last(node'.buckets) :: Keyspace.lt(key, rpivot.value)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    match lpivot {
      case None => (
        match rpivot {
          case None => (
            node
          )
          case Some(rpivot) => (
            CutoffNodeAndKeepLeft(node, rpivot)
          )
        }
      )
      case Some(lpivot) => (
        match rpivot {
          case None => (
            CutoffNodeAndKeepRight(node, lpivot)
          )
          case Some(rpivot) => (
            var node1 := CutoffNodeAndKeepLeft(node, rpivot);
            var node' := CutoffNodeAndKeepRight(node1, lpivot);

            CutoffNodeCorrect(node, node1, node', lpivot, rpivot);

            node'
          )
        }
      )
    }
  }

  //// Split

  function SplitChildLeft(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function SplitChildRight(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  function SplitParent(fused_parent: Node, pivot: Key, slot_idx: int, left_childref: Reference, right_childref: Reference) : Node
  requires 0 <= slot_idx <= |fused_parent.pivotTable|
  requires fused_parent.children.Some?
  requires fused_parent.children.Some? ==> 0 <= slot_idx < |fused_parent.children.value|
  requires 0 <= slot_idx < |fused_parent.buckets|
  {
    Node(
      insert(fused_parent.pivotTable, pivot, slot_idx),
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      Buckets.SplitBucketInList(fused_parent.buckets, slot_idx, pivot)
    )
  }

  predicate ValidSplit(f: NodeFusion)
  {
    && WFNode(f.fused_parent)
    && WFNode(f.fused_child)

    && f.fused_parent.children.Some?
    && 0 <= f.slot_idx < |f.fused_parent.buckets|
    && |f.fused_parent.buckets| <= MaxNumChildren() - 1

    && var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    && var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    && var child := CutoffNode(f.fused_child, lbound, ubound);

    && 1 <= f.num_children_left < |child.buckets|
    && f.fused_parent.children.value[f.slot_idx] == f.fused_childref
    && child.pivotTable[f.num_children_left - 1] == f.pivot
    && Pivots.Route(f.fused_parent.pivotTable, f.pivot) == f.slot_idx

    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    && f.split_parent == SplitParent(f.fused_parent, f.pivot, f.slot_idx, f.left_childref, f.right_childref)

    && f.left_child == SplitChildLeft(child, f.num_children_left)
    && f.right_child == SplitChildRight(child, f.num_children_left)
  }

  function SplitReads(f: NodeFusion) : seq<ReadOp>
  requires ValidSplit(f)
  {
    [
      ReadOp(f.parentref, f.fused_parent),
      ReadOp(f.fused_childref, f.fused_child)
    ]
  }

  function SplitOps(f: NodeFusion) : seq<Op>
  requires ValidSplit(f)
  {
    [
      G.AllocOp(f.left_childref, f.left_child),
      G.AllocOp(f.right_childref, f.right_child),
      G.WriteOp(f.parentref, f.split_parent)
    ]
  }

  //// Merge

  predicate ValidMerge(f: NodeFusion)
  {
    && WFNode(f.split_parent)
    && WFNode(f.left_child)
    && WFNode(f.right_child)
    && 0 <= f.slot_idx < |f.split_parent.buckets| - 1
    && f.num_children_left == |f.left_child.buckets|
    && f.split_parent.pivotTable[f.slot_idx] == f.pivot
    && f.split_parent.children.Some?
    && f.split_parent.children.value[f.slot_idx] == f.left_childref
    && f.split_parent.children.value[f.slot_idx + 1] == f.right_childref
    && WeightBucketList(f.left_child.buckets) + WeightBucketList(f.right_child.buckets) <= MaxTotalBucketWeight()
    && |f.left_child.buckets| + |f.right_child.buckets| <= MaxNumChildren()

    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    && f.fused_parent == Node(
      remove(f.split_parent.pivotTable, f.slot_idx),
      Some(replace2with1(f.split_parent.children.value, f.fused_childref, f.slot_idx)),
      Buckets.MergeBucketsInList(f.split_parent.buckets, f.slot_idx)
    )

    // this is actually an invariant which follows from fixed height of the tree,
    // but we currently don't track that as an invariant... should we?
    && (f.left_child.children.Some? ==> f.right_child.children.Some?)
    && (f.left_child.children.None? ==> f.right_child.children.None?)

    && var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    && var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);

    && var left := CutoffNode(f.left_child, lbound, Some(f.pivot));
    && var right := CutoffNode(f.right_child, Some(f.pivot), ubound);

    && f.fused_child == Node(
      concat3(left.pivotTable, f.pivot, right.pivotTable),
      if left.children.Some? then Some(left.children.value + right.children.value) else None,
      left.buckets + right.buckets
    )
  }

  function MergeReads(f: NodeFusion) : seq<ReadOp>
  requires ValidMerge(f)
  {
    [
      ReadOp(f.parentref, f.split_parent),
      ReadOp(f.left_childref, f.left_child),
      ReadOp(f.right_childref, f.right_child)
    ]
  }

  function MergeOps(f: NodeFusion) : seq<Op>
  requires ValidMerge(f)
  {
    [
      G.AllocOp(f.fused_childref, f.fused_child),
      G.WriteOp(f.parentref, f.fused_parent)
    ]
  }

  //// Repivot

  datatype Repivot = Repivot(ref: Reference, leaf: Node, pivots: seq<Key>)

  predicate ValidRepivot(r: Repivot)
  {
    && WFNode(r.leaf)
    && r.leaf.children.None?
    && Pivots.WFPivots(r.pivots)
    && |r.pivots| <= MaxNumChildren() - 1
  }

  function RepivotReads(r: Repivot) : seq<ReadOp>
  requires ValidRepivot(r)
  {
    [
      ReadOp(r.ref, r.leaf)
    ]
  }

  function ApplyRepivot(leaf: Node, pivots: seq<Key>) : (leaf': Node)
  requires WFNode(leaf)
  requires leaf.children.None?
  requires Pivots.WFPivots(pivots)
  {
    Node(pivots, None, Buckets.SplitBucketOnPivots(Buckets.JoinBucketList(leaf.buckets), pivots))
  }

  function RepivotOps(r: Repivot) : seq<Op>
  requires ValidRepivot(r)
  {
    [
      G.WriteOp(r.ref, ApplyRepivot(r.leaf, r.pivots))
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
    | BetreeRepivot(repivot: Repivot)

  predicate ValidBetreeStep(step: BetreeStep)
  {
    match step {
      case BetreeQuery(q) => ValidQuery(q)
      case BetreeInsert(ins) => ValidInsertion(ins)
      case BetreeFlush(flush) => ValidFlush(flush)
      case BetreeGrow(growth) => ValidGrow(growth)
      case BetreeSplit(fusion) => ValidSplit(fusion)
      case BetreeMerge(fusion) => ValidMerge(fusion)
      case BetreeRepivot(r) => ValidRepivot(r)
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
      case BetreeRepivot(r) => RepivotReads(r)
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
      case BetreeRepivot(r) => RepivotOps(r)
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
      case BetreeRepivot(r) => uiop.NoOp?
    }
  }
}

module PivotBetreeSpecWFNodes {
  import opened Options
  import opened PivotBetreeSpec`Internal
  import opened Maps
  import opened Sequences
  import opened BucketWeights
  import opened BucketsLib
  import opened Bounds
  import Pivots = PivotsLib
  import M = ValueMessage

  import MS = MapSpec
  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element

  lemma ValidFlushWritesWFNodes(flush: NodeFlush)
  requires ValidFlush(flush)
  ensures forall i | 0 <= i < |FlushOps(flush)| :: WFNode(FlushOps(flush)[i].node)
  ensures WFNode(FlushOps(flush)[0].node)
  ensures WFNode(FlushOps(flush)[1].node)
  {
    var newparent := G.Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := map[]]
      );
    WFBucketListFlush(flush.parent.buckets[flush.slotIndex], flush.child.buckets, flush.child.pivotTable);
    WeightBucketListFlush(flush.parent.buckets[flush.slotIndex], flush.child.buckets, flush.child.pivotTable);
    WeightBucketListClearEntry(flush.parent.buckets, flush.slotIndex);
    var newchild := AddMessagesToNode(flush.child, flush.parent.buckets[flush.slotIndex]);

    /*forall i | 0 <= i < |newparent.buckets|
    ensures NodeHasWFBucketAt(newparent, i)
    {
      //if (i == flush.slotIndex) {
      //  assert NodeHasWFBucketAt(newparent, i);
      //} else {
      assert NodeHasWFBucketAt(flush.parent, i);
      //  assert NodeHasWFBucketAt(newparent, i);
      //}
    }*/

    assert WFNode(newparent);
    assert WFNode(newchild);
  }

  lemma ValidSplitWritesWFNodes(f: NodeFusion)
  requires ValidSplit(f)
  ensures WFNode(f.split_parent);
  ensures WFNode(f.left_child);
  ensures WFNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: WFNode(SplitOps(f)[i].node)
  {
    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;

    var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    var child := CutoffNode(f.fused_child, lbound, ubound);

    var left_child := f.left_child;
    var right_child := f.right_child;
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    Pivots.PivotNotMinimum(child.pivotTable, f.num_children_left - 1);
    Pivots.WFPivotsInsert(fused_parent.pivotTable, slot_idx, pivot);

    Buckets.WFSplitBucketInList(fused_parent.buckets, slot_idx, pivot, fused_parent.pivotTable);
    WeightSplitBucketInList(fused_parent.buckets, slot_idx, pivot);

    assert WFNode(split_parent);

    Pivots.WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, f.num_children_left);

    Buckets.BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, left_child.buckets, left_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    Buckets.BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, right_child.buckets, right_child.pivotTable, 0, |right_child.buckets| - 1, -f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert WFNode(left_child);
    assert WFNode(right_child);
  }

  lemma ValidMergeWritesWFNodes(f: NodeFusion)
  requires ValidMerge(f)
  ensures WFNode(f.fused_parent);
  ensures WFNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: WFNode(MergeOps(f)[i].node)
  {
    var split_parent := f.split_parent;
    var fused_parent := f.fused_parent;
    var fused_child := f.fused_child;
    var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);
    var left_child := CutoffNode(f.left_child, lbound, Some(f.pivot));
    var right_child := CutoffNode(f.right_child, Some(f.pivot), ubound);
    var slot_idx := f.slot_idx;
    var pivot := f.pivot;

    WeightBucketListConcat(left_child.buckets, right_child.buckets);

    Pivots.WFPivotsRemoved(split_parent.pivotTable, slot_idx);
    
    reveal_MergeBucketsInList();

    Buckets.BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, 0, slot_idx - 1, 0);
    Buckets.BucketListHasWFBucketAtIdenticalSlice(split_parent.buckets, split_parent.pivotTable, fused_parent.buckets, fused_parent.pivotTable, slot_idx + 1, |fused_parent.buckets| - 1, -1);

    WFMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
    WeightMergeBucketsInList(split_parent.buckets, slot_idx, split_parent.pivotTable);
    assert WFNode(fused_parent);
    Pivots.PivotNotMinimum(split_parent.pivotTable, slot_idx);
    Pivots.WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

    Buckets.BucketListHasWFBucketAtIdenticalSlice(left_child.buckets, left_child.pivotTable, fused_child.buckets, fused_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    Buckets.BucketListHasWFBucketAtIdenticalSlice(right_child.buckets, right_child.pivotTable, fused_child.buckets, fused_child.pivotTable, |left_child.buckets|, |fused_child.buckets| - 1, |left_child.buckets|);

    assert WFNode(fused_child);
  }

  lemma WFApplyRepivot(leaf: G.Node, pivots: seq<Key>)
  requires WFNode(leaf)
  requires leaf.children.None?
  requires Pivots.WFPivots(pivots)
  requires |pivots| <= MaxNumChildren() - 1
  ensures WFNode(ApplyRepivot(leaf, pivots))
  {
    var j := Buckets.JoinBucketList(leaf.buckets);
    var s := Buckets.SplitBucketOnPivots(j, pivots);
    Buckets.WFBucketsOfWFBucketList(leaf.buckets, leaf.pivotTable);
    Buckets.WFJoinBucketList(leaf.buckets);
    Buckets.JoinBucketsSplitBucketOnPivotsCancel(j, pivots);
    WeightJoinBucketList(leaf.buckets);
    WeightSplitBucketOnPivots(j, pivots);
  }

  lemma ValidRepivotWFNodes(r: Repivot)
  requires ValidRepivot(r)
  ensures forall i | 0 <= i < |RepivotOps(r)| :: WFNode(RepivotOps(r)[i].node)
  {
    WFApplyRepivot(r.leaf, r.pivots);
  }

  lemma ValidInsertWritesWFNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: WFNode(InsertionOps(ins)[i].node)
  {
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    WeightBucketListInsert(ins.oldroot.buckets, ins.oldroot.pivotTable, ins.key, ins.msg);
    assert WFNode(newroot);
  }

  lemma ValidGrowWritesWFNodes(g: RootGrowth)
  requires ValidGrow(g)
  ensures forall i | 0 <= i < |GrowOps(g)| :: WFNode(GrowOps(g)[i].node)
  ensures WFNode(GrowOps(g)[0].node)
  ensures WFNode(GrowOps(g)[1].node)
  {
    var newroot := G.Node([], Some([g.newchildref]), [map[]]);
    WeightBucketListOneEmpty();
    assert WFNode(newroot);
  }

  // This lemma is useful for BetreeBlockCache
  lemma ValidStepWritesWFNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: WFNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeInsert(ins) => {
        ValidInsertWritesWFNodes(ins);
      }
      case BetreeFlush(flush) => {
        ValidFlushWritesWFNodes(flush);
      }
      case BetreeGrow(growth) => {
        ValidGrowWritesWFNodes(growth);
      }
      case BetreeSplit(fusion) => {
        ValidSplitWritesWFNodes(fusion);
      }
      case BetreeMerge(fusion) => {
        ValidMergeWritesWFNodes(fusion);
      }
      case BetreeRepivot(r) => {
        ValidRepivotWFNodes(r);
      }
    }
  }

}
