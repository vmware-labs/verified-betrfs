include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
include "../Betree/Betree.i.dfy"
include "../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../lib/Buckets/BucketsLib.i.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "../lib/Buckets/BucketWeights.i.dfy"
//
// A PivotBetree refines a Betree, carrying forward the tree structure
// but refining the abstract infinite key maps with key ranges separated
// by pivot keys.
//

module PivotBetreeGraph refines Graph {
  import BG = BetreeGraph

  import MS = MapSpec
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened BucketsLib
  import opened BoundedPivotsLib

  import Keyspace = Lexicographic_Byte_Order
  import KeyspaceImpl = Lexicographic_Byte_Order_Impl

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
  import opened BucketsLib
  import opened BucketWeights
  import UI
  import opened KeyType
  import opened ValueMessage
  import opened bpl = BoundedPivotsLib

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, WFNode, InvNode
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
    && NumBuckets(node.pivotTable) == |node.buckets|
    && (node.children.Some? ==> |node.buckets| == |node.children.value|)
    && WFPivots(node.pivotTable)
    && WFBucketList(node.buckets, node.pivotTable)
    && BoundedNode(node)
  }

  predicate InvNode(node: Node)
  {
    && WFNode(node)
    && WFBucketListProper(node.buckets, node.pivotTable)
    && BucketListWellMarshalled(node.buckets)
  }

  function AddMessageToNode(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  requires BoundedKey(node.pivotTable, key)
  {
    var newnode := node.(
      buckets := BucketListInsert(node.buckets, node.pivotTable, key, msg)
    );
    newnode
  }

  function AddMessagesToNode(node: Node, msgs: Bucket) : Node
  requires WFNode(node)
  {
    Node(
      node.pivotTable,
      node.children,
      BucketListFlush(msgs, node.buckets, node.pivotTable)
    )
  }

  //// Query

  type Layer = G.ReadOp
  type Lookup = seq<Layer>

  datatype LookupQuery = LookupQuery(key: Key, value: Value, lookup: Lookup)

  predicate BufferIsDefining(entry: Message)
  {
    && entry.Define?
  }

  predicate BufferDefinesValue(log: Message, value: Value)
  {
    && BufferIsDefining(log)
    && log.value == value
  }

  predicate ValidLayerIndex(lookup: Lookup, idx: int)
  {
    && 0 <= idx < |lookup|
  }

  predicate LookupVisitsWFNodes(lookup: Lookup)
  {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate LookupVisitsWellMarshalledBuckets(lookup: Lookup, key: Key)
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(key, lookup)
  {
    forall i :: 0 <= i < |lookup| ==> BucketWellMarshalled(lookup[i].node.buckets[Route(lookup[i].node.pivotTable, key)])
  }

  predicate LookupBoundedKey(key: Key, lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) ==> BoundedKey(lookup[idx].node.pivotTable, key))
  }

  predicate LookupFollowsChildRefAtLayer(key: Key, lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx)
  requires idx < |lookup| - 1;
  requires WFNode(lookup[idx].node)
  requires BoundedKey(lookup[idx].node.pivotTable, key)
  {
    && lookup[idx].node.children.Some?
    && lookup[idx].node.children.value[Route(lookup[idx].node.pivotTable, key)] == lookup[idx+1].ref
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(key, lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(key, lookup, idx))
  }

  function NodeLookup(node: Node, key: Key) : Message
  requires WFBucketList(node.buckets, node.pivotTable)
  requires BoundedKey(node.pivotTable, key)
  {
    BucketListGet(node.buckets, node.pivotTable, key)
  }

  function InterpretLookup(lookup: Lookup, key: Key) : Message
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(key, lookup)
  {
    if |lookup| == 0 then
      Update(NopDelta())
    else
      Merge(InterpretLookup(DropLast(lookup), key), NodeLookup(Last(lookup).node, key))
  }

  function InterpretLookupAccountingForLeaf(lookup: Lookup, key: Key) : Message
  requires |lookup| > 0
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(key, lookup)
  {
    if Last(lookup).node.children.Some? then
      InterpretLookup(lookup, key)
    else
      Merge(InterpretLookup(lookup, key), DefineDefault())
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupVisitsWFNodes(lookup)
    && LookupBoundedKey(key, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  predicate ValidQuery(q: LookupQuery) {
    && WFLookupForKey(q.lookup, q.key)
    && (LookupVisitsWellMarshalledBuckets(q.lookup, q.key) ==>
        BufferDefinesValue(InterpretLookupAccountingForLeaf(q.lookup, q.key), q.value)
    )
  }

  function QueryReads(q: LookupQuery): seq<ReadOp> {
    q.lookup
  }

  function QueryOps(q: LookupQuery): seq<Op> {
    []
  }

  //// Succ

  datatype SuccQuery = SuccQuery(
      start: UI.RangeStart,
      results: seq<UI.SuccResult>,
      end: UI.RangeEnd,
      buckets: seq<Bucket>,
      lookup: Lookup)

  function LookupUpperBoundAtLayer(layer: Layer, key: Key) : Option<Key>
  requires WFNode(layer.node)
  requires BoundedKey(layer.node.pivotTable, key)
  {
    var r := Route(layer.node.pivotTable, key);
    if layer.node.pivotTable[r+1].Element? 
    then Some(GetKey(layer.node.pivotTable, r+1))
    else None
  }

  function OptionKeyMin(k1: Option<Key>, k2: Option<Key>) : Option<Key>
  {
    match k1 {
      case Some(key1) => match k2 {
        case Some(key2) => if G.Keyspace.lt(k1.value, k2.value) then Some(k1.value) else Some(k2.value)
        case None => k1
      }
      case None => k2
    }
  }

  function {:opaque} LookupUpperBound(lookup: Lookup, key: Key) : Option<Key>
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(key, lookup)
  {
    if lookup == []
    then None
    else OptionKeyMin(
        LookupUpperBound(DropLast(lookup), key),
        LookupUpperBoundAtLayer(Last(lookup), key)
      )
  }

  predicate BufferDefinesEmptyValue(m: Message)
  {
    Merge(m, DefineDefault()).value == DefaultValue()
  }

  predicate ValidSuccQuery(sq: SuccQuery)
  {
    && var startKey := if sq.start.NegativeInf? then [] else sq.start.key;
    && WFLookupForKey(sq.lookup, startKey)

    && var lookupUpperBound := LookupUpperBound(sq.lookup, startKey);
    && Last(sq.lookup).node.children.None?

    && |sq.lookup| == |sq.buckets|
    && (forall i | 0 <= i < |sq.lookup| :: sq.buckets[i] == sq.lookup[i].node.buckets[Route(sq.lookup[i].node.pivotTable, startKey)])

    // what if sq.end is positive infinity?
    && (BucketListWellMarshalled(sq.buckets) ==> (
      && MS.NonEmptyRange(sq.start, sq.end)
      && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, sq.end))
      && sq.results ==
        SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampRange(ComposeSeq(sq.buckets), sq.start, sq.end)))
    ))
  }

  function SuccQueryReads(q: SuccQuery): seq<ReadOp> {
    q.lookup
  }

  function SuccQueryOps(q: SuccQuery): seq<Op> {
    []
  }

  //// Insert
  datatype MessageInsertion = MessageInsertion(key: Key, msg: Message, oldroot: Node)

  predicate ValidInsertion(ins: MessageInsertion) {
    && WFNode(ins.oldroot)
    && BoundedKey(ins.oldroot.pivotTable, ins.key)
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

  function {:opaque} NodeInsertKeyValue(node: Node, key: Key, msg: Message) : Node
  requires WFNode(node)
  requires BoundedKey(node.pivotTable, key)
  {
    var r := Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var newBucket := BucketInsert(bucket, key, msg);
    node.(buckets := node.buckets[r := newBucket])
  }

  //// Flush
  datatype NodeFlush = NodeFlush(
    parentref: Reference,
    parent: Node,
    childref: Reference,
    child: Node,
    newchildref: Reference,
    newchild: Node,
    ghost slotIndex: int,
    keys: set<Key>,
    newParentBucket: Bucket,
    newChildBuckets: seq<Bucket>
  )

  predicate ValidFlush(f: NodeFlush)
  {
    && WFNode(f.parent)
    && WFNode(f.child)
    && 0 <= f.slotIndex < |f.parent.buckets|
    && f.parent.children.Some?
    && f.parent.children.value[f.slotIndex] == f.childref
    && WFBucketList(f.newChildBuckets, f.child.pivotTable)
    && WFBucket(f.newParentBucket)
    && (forall key | key in f.keys :: BoundedKey(f.child.pivotTable, key))
    && WeightBucketList(f.newChildBuckets) <= MaxTotalBucketWeight()
    && WeightBucket(f.newParentBucket) <= WeightBucket(f.parent.buckets[f.slotIndex])
    && (BucketListWellMarshalled(f.child.buckets)
          && BucketWellMarshalled(f.parent.buckets[f.slotIndex])
          && WFBucketListProper(f.child.buckets, f.child.pivotTable)
        ==>
      && f.newParentBucket == BucketComplement(f.parent.buckets[f.slotIndex], f.keys)
      && f.newChildBuckets == BucketListFlush(
          BucketIntersect(f.parent.buckets[f.slotIndex], f.keys),
          f.child.buckets, f.child.pivotTable)
    )
  }

  function FlushReads(f: NodeFlush) : seq<ReadOp>
  requires ValidFlush(f)
  {
    [
      G.ReadOp(f.parentref, f.parent),
      G.ReadOp(f.childref, f.child)
    ]
  }

  function FlushOps(f: NodeFlush) : seq<Op>
  requires ValidFlush(f)
  {
    var newparent := Node(
        f.parent.pivotTable,
        Some(f.parent.children.value[f.slotIndex := f.newchildref]),
        f.parent.buckets[f.slotIndex := f.newParentBucket]
      );
    var newchild := f.child.(buckets := f.newChildBuckets);
    var allocop := G.AllocOp(f.newchildref, newchild);
    var writeop := G.WriteOp(f.parentref, newparent);
    [allocop, writeop]
  }

  //// Grow

  datatype RootGrowth = RootGrowth(oldroot: Node, newchildref: Reference)

  predicate ValidGrow(growth: RootGrowth)
  {
    && WFNode(growth.oldroot)
    && ContainsAllKeys(growth.oldroot.pivotTable)
  }

  function GrowReads(growth: RootGrowth) : seq<ReadOp>
  requires ValidGrow(growth)
  {
    [G.ReadOp(Root(), growth.oldroot)]
  }

  function GrowOps(growth: RootGrowth) : seq<Op>
  requires ValidGrow(growth)
  {
    var newroot := Node(InitPivotTable(), Some([growth.newchildref]), [B(map[])]);
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

    ghost slot_idx: int,
    ghost num_children_left: int,
    pivot: Key
  )

  //// Useful functions and lemmas for Split, Merge (other redirects)

  // theses things needs additional proof to prove boundedness 
  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  requires ValidLeftCutOffKey(node.pivotTable, pivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures node'.pivotTable[0] == node.pivotTable[0]
  ensures Last(node'.pivotTable) == KeyToElement(pivot)
  ensures forall key | key in Last(node'.buckets).b :: Lexicographic_Byte_Order.lt(key, pivot)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    reveal_SplitBucketLeft();
    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    var bplleftPivots := SplitLeft(node.pivotTable, pivot);

    reveal_CutoffForLeft();
  
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft+1]) else None;
    var leftBuckets := SplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    WFSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    WeightSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    Node(bplleftPivots, leftChildren, leftBuckets)
  }

  function {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  requires BoundedKey(node.pivotTable, pivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures pivot == node'.pivotTable[0].e
  ensures forall key | key in node'.buckets[0].b :: G.Keyspace.lte(pivot, key)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    reveal_SplitBucketRight();
    var cRight := CutoffForRight(node.pivotTable, pivot);
    var bplrightPivots := SplitRight(node.pivotTable, pivot);

    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var rightBuckets := SplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    WFSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
    WeightSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    Node(bplrightPivots, rightChildren, rightBuckets)
  }

  predicate ValidSplitKey(node: Node, lpivot: Key, rpivot: Option<Key>)
  requires WFNode(node)
  {
    && BoundedKey(node.pivotTable, lpivot)
    && (rpivot.Some? ==> ValidLeftCutOffKey(node.pivotTable, rpivot.value))
    && (rpivot.Some? ==> G.Keyspace.lt(node.pivotTable[0].e, rpivot.value))
    && (rpivot.Some? ==> G.Keyspace.lt(lpivot, rpivot.value))
    && (rpivot.None? ==> Last(node.pivotTable) == bpl.Keyspace.Max_Element)
  }

  function {:opaque} CutoffNode(node: Node, lpivot: Key, rpivot: Option<Key>) : (node' : Node)
  requires WFNode(node)
  requires ValidSplitKey(node, lpivot, rpivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures lpivot == node'.pivotTable[0].e
  ensures forall key | key in node'.buckets[0].b :: G.Keyspace.lte(lpivot, key)
  ensures rpivot.Some? ==> Last(node'.pivotTable) == KeyToElement(rpivot.value)
  ensures rpivot.Some? ==> forall key | key in Last(node'.buckets).b :: G.Keyspace.lt(key, rpivot.value)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
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
  }

  lemma CutoffNodeCorrect(node: Node, node1: Node, node2: Node, lpivot: Key, rpivot: Key)
  requires WFNode(node)
  requires ValidLeftCutOffKey(node.pivotTable, rpivot)
  requires node1 == CutoffNodeAndKeepLeft(node, rpivot);
  requires BoundedKey(node1.pivotTable, lpivot)
  requires node2 == CutoffNodeAndKeepRight(node1, lpivot);
  ensures lpivot == node2.pivotTable[0].e
  ensures Last(node2.pivotTable) == KeyToElement(rpivot)
  ensures forall key | key in node2.buckets[0].b :: G.Keyspace.lte(lpivot, key)
  ensures forall key | key in Last(node2.buckets).b :: G.Keyspace.lt(key, rpivot)
  {
    reveal_CutoffNodeAndKeepLeft();
    reveal_CutoffNodeAndKeepRight();
  }

  //// Split
  function SplitChildLeft(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable| - 2
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    Node(
      child.pivotTable[ .. num_children_left + 1],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function SplitChildRight(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left <= |child.pivotTable| - 1
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
  requires 0 <= slot_idx < NumBuckets(fused_parent.pivotTable)
  requires fused_parent.children.Some?
  requires fused_parent.children.Some? ==> 0 <= slot_idx < |fused_parent.children.value|
  requires 0 <= slot_idx < |fused_parent.buckets|
  {
    Node(
      insert(fused_parent.pivotTable, KeyToElement(pivot), slot_idx+1),
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      SplitBucketInList(fused_parent.buckets, slot_idx, pivot)
    )
  }

  function getlbound(parent: Node, slot: int) : Key
  requires WFNode(parent)
  requires parent.children.Some?
  requires 0 <= slot < |parent.children.value|
  {
    GetKey(parent.pivotTable, slot)
  }

  function getubound(parent: Node, slot: int) : Option<Key>
  requires WFNode(parent)
  requires parent.children.Some?
  requires 0 <= slot < |parent.children.value|
  {
    if parent.pivotTable[slot+1].Element? 
    then Some(GetKey(parent.pivotTable, slot+1)) 
    else None
  }

  // a defined set of lock ordering, what counts as smaller, only things that go down the same node has a notion of ordering
  predicate ValidSplit(f: NodeFusion)
  {
    && WFNode(f.fused_parent)
    && WFNode(f.fused_child)

    && f.fused_parent.children.Some?
    && 0 <= f.slot_idx < |f.fused_parent.buckets|
    && |f.fused_parent.buckets| <= MaxNumChildren() - 1
  
    && var lbound :=  getlbound(f.fused_parent, f.slot_idx);
    && var ubound :=  getubound(f.fused_parent, f.slot_idx);

    && ValidSplitKey(f.fused_child, lbound, ubound)
    && ValidSplitKey(f.fused_parent, lbound, ubound)
    && var child := CutoffNode(f.fused_child, lbound, ubound);

    && 1 <= f.num_children_left < |child.buckets|
    && f.fused_parent.children.value[f.slot_idx] == f.fused_childref

    && bpl.Keyspace.lte(f.fused_child.pivotTable[0], f.fused_parent.pivotTable[f.slot_idx])
    && bpl.Keyspace.lte(f.fused_parent.pivotTable[f.slot_idx+1], Last(f.fused_child.pivotTable))

    && child.pivotTable[f.num_children_left].e == f.pivot
    && PivotInsertable(f.fused_parent.pivotTable,  f.slot_idx+1, f.pivot)

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

  // 0 index children is negative infinity to pivot[0]
  // f.pivot == the end of the pivot

  predicate ValidMerge(f: NodeFusion)
  {
    && WFNode(f.split_parent)
    && WFNode(f.left_child)
    && WFNode(f.right_child)
    && 0 <= f.slot_idx < |f.split_parent.buckets| - 1
    && f.num_children_left == |f.left_child.buckets|
    && f.split_parent.pivotTable[f.slot_idx+1].e == f.pivot
    && f.split_parent.children.Some?
    && f.split_parent.children.value[f.slot_idx] == f.left_childref
    && f.split_parent.children.value[f.slot_idx + 1] == f.right_childref
    && WeightBucketList(f.left_child.buckets) + WeightBucketList(f.right_child.buckets) <= MaxTotalBucketWeight()
    && |f.left_child.buckets| + |f.right_child.buckets| <= MaxNumChildren()

    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    && f.fused_parent == Node(
      remove(f.split_parent.pivotTable, f.slot_idx+1),
      Some(replace2with1(f.split_parent.children.value, f.fused_childref, f.slot_idx)),
      MergeBucketsInList(f.split_parent.buckets, f.slot_idx)
    )

    // this is actually an invariant which follows from fixed height of the tree,
    // but we currently don't track that as an invariant... should we?
    && (f.left_child.children.Some? ==> f.right_child.children.Some?)
    && (f.left_child.children.None? ==> f.right_child.children.None?)
  
    && var lbound :=  getlbound(f.split_parent, f.slot_idx);
    && var ubound :=  getubound(f.split_parent, f.slot_idx);

    && ValidSplitKey(f.left_child, lbound, Some(f.pivot))
    && ValidSplitKey(f.right_child, f.pivot, ubound)
    && var left := CutoffNode(f.left_child, lbound, Some(f.pivot));
    && var right := CutoffNode(f.right_child, f.pivot, ubound);

    && f.fused_child == Node(
      concat3(left.pivotTable[..|left.pivotTable|-1], KeyToElement(f.pivot), right.pivotTable[1..]),
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

  datatype Repivot = Repivot(ref: Reference, leaf: Node, pivots: PivotTable)

  predicate ValidRepivot(r: Repivot)
  {
    && WFNode(r.leaf)
    && |r.pivots| <= MaxNumChildren() + 1
    && BoundedBucketList(r.leaf.buckets, r.leaf.pivotTable)
    && ContainsAllKeys(r.pivots) 
    && r.leaf.children.None?
  }

  function RepivotReads(r: Repivot) : seq<ReadOp>
  requires ValidRepivot(r)
  {
    [
      ReadOp(r.ref, r.leaf)
    ]
  }

  lemma PivotsHasAllKeys(pt: PivotTable)
  requires ContainsAllKeys(pt)
  ensures (forall key : Key | MS.InDomain(key) :: BoundedKey(pt, key))
  {
    forall key : Key | MS.InDomain(key)
    ensures BoundedKey(pt, key)
    {
      G.Keyspace.SeqComparison.reveal_lte();
    }
  }

  function ApplyRepivot(r: Repivot) : (leaf': Node)
  requires ValidRepivot(r)
  {
    PivotsHasAllKeys(r.pivots);
    BoundedBucketListJoin(r.leaf.buckets, r.pivots);
    var leaf' := Node(r.pivots, None, SplitBucketOnPivots(JoinBucketList(r.leaf.buckets), r.pivots));
    leaf'
  }

  function RepivotOps(r: Repivot) : seq<Op>
  requires ValidRepivot(r)
  {
    [
      G.WriteOp(r.ref, ApplyRepivot(r))
    ]
  }

  //// Put it all together

  datatype BetreeStep =
    | BetreeQuery(q: LookupQuery)
    | BetreeSuccQuery(sq: SuccQuery)
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
      case BetreeSuccQuery(sq) => ValidSuccQuery(sq)
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
      case BetreeSuccQuery(sq) => SuccQueryReads(sq)
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
      case BetreeSuccQuery(sq) => SuccQueryOps(sq)
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
      case BetreeSuccQuery(sq) => uiop == MS.UI.SuccOp(sq.start, sq.results, sq.end)
      case BetreeInsert(ins) => ins.msg.Define? && uiop == MS.UI.PutOp(ins.key, ins.msg.value)
      case BetreeFlush(flush) => uiop.NoOp?
      case BetreeGrow(growth) => uiop.NoOp?
      case BetreeSplit(fusion) => uiop.NoOp?
      case BetreeMerge(fusion) => uiop.NoOp?
      case BetreeRepivot(r) => uiop.NoOp?
    }
  }

}
