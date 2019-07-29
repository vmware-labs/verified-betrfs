include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "../lib/Option.dfy"
include "Message.dfy"
include "BetreeSpec.dfy"
include "Betree.dfy"
include "PivotsLib.dfy"

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
  import Pivots = PivotsLib

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, WFNode
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  // TODO maybe move bucket stuff into the PivotsLib

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

  function method AddMessagesToBucket(pivotTable: PivotTable, i: int, childBucket: map<Key, Message>, parentBucket: map<Key, Message>) : Bucket
  requires Pivots.WFPivots(pivotTable)
  ensures forall key | key in AddMessagesToBucket(pivotTable, i, childBucket, parentBucket) :: Pivots.Route(pivotTable, key) == i
  {
    map key
    | && (key in (childBucket.Keys + parentBucket.Keys)) // this is technically redundant but allows Dafny to figure out that the domain is finite
      && Pivots.Route(pivotTable, key) == i
      && M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key)) != M.IdentityMessage()
    :: M.Merge(BucketLookup(parentBucket, key), BucketLookup(childBucket, key))
  }

  function method AddMessagesToBuckets(pivotTable: PivotTable, i: int, buckets: seq<map<Key, Message>>, parentBucket: map<Key, Message>) : seq<Bucket>
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

  function method AddMessagesToNode(node: Node, buffer: map<Key, Message>) : Node
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

  function method NodeLookup(node: Node, key: Key) : Message
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

  function method SplitBucketLeft(bucket: map<Key, Message>, pivot: Key) : map<Key, Message>
  {
    map key | key in bucket && Keyspace.lt(key, pivot) :: bucket[key]
  }

  function method SplitBucketRight(bucket: map<Key, Message>, pivot: Key) : map<Key, Message>
  {
    map key | key in bucket && Keyspace.lte(pivot, key) :: bucket[key]
  }

  lemma WFSplitBucketLeft(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
  requires 0 <= i <= |pivots|
  requires Pivots.WFPivots(pivots)
  requires WFBucket(bucket, pivots, i)
  ensures Pivots.WFPivots(pivots[.. i])
  ensures WFBucket(SplitBucketLeft(bucket, pivot), pivots[.. i], i)
  {
    Pivots.WFSlice(pivots, 0, i);
    forall key | key in SplitBucketLeft(bucket, pivot)
    ensures Pivots.Route(pivots[.. i], key) == i
    {
      Pivots.RouteIs(pivots[.. i], key, i);
    }
  }

  lemma WFSplitBucketRight(bucket: Bucket, pivot: Key, pivots: seq<Key>, i: int)
  requires 0 <= i <= |pivots|
  requires Pivots.WFPivots(pivots)
  requires WFBucket(bucket, pivots, i)
  ensures Pivots.WFPivots(pivots[i ..])
  ensures WFBucket(SplitBucketRight(bucket, pivot), pivots[i ..], 0)
  {
    Pivots.WFSuffix(pivots, i);
    forall key | key in SplitBucketRight(bucket, pivot)
    ensures Pivots.Route(pivots[i ..], key) == 0
    {
      Pivots.RouteIs(pivots[i ..], key, 0);
    }
  }

  function method {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures |node'.pivotTable| > 0 ==> Keyspace.lt(Last(node'.pivotTable), pivot)
  ensures forall key | key in Last(node'.buckets) :: Keyspace.lt(key, pivot)
  ensures G.Successors(node') <= G.Successors(node)
  {
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var leftBuckets := node.buckets[.. cLeft] + [SplitBucketLeft(node.buckets[cLeft], pivot)];

    //Pivots.WFSlice(node.pivotTable, 0, cLeft);
    assert NodeHasWFBucketAt(node, cLeft);
    WFSplitBucketLeft(node.buckets[cLeft], pivot, node.pivotTable, cLeft);
    //assert WFBucket(SplitBucketLeft(node.buckets[cLeft], pivot), leftPivots, cLeft);
    //assert WFBucket(leftBuckets[cLeft], leftPivots, cLeft);
    NodeHasWFBucketAtIdenticalSlice(node, Node(leftPivots, leftChildren, leftBuckets), 0, cLeft - 1, 0);

    Node(leftPivots, leftChildren, leftBuckets)
  }

  function method {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures |node'.pivotTable| > 0 ==> Keyspace.lt(pivot, node'.pivotTable[0])
  ensures forall key | key in node'.buckets[0] :: Keyspace.lte(pivot, key)
  ensures G.Successors(node') <= G.Successors(node)
  {
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var rightBuckets := [SplitBucketRight(node.buckets[cRight], pivot)] + node.buckets[cRight + 1 ..];

    assert NodeHasWFBucketAt(node, cRight);
    WFSplitBucketRight(node.buckets[cRight], pivot, node.pivotTable, cRight);
    NodeHasWFBucketAtIdenticalSlice(node, Node(rightPivots, rightChildren, rightBuckets),
      1, |rightBuckets| - 1, -cRight);

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

  function method {:opaque} CutoffNode(node: Node, lpivot: Option<Key>, rpivot: Option<Key>) : (node' : Node)
  requires WFNode(node)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures lpivot.Some? && |node'.pivotTable| > 0 ==> Keyspace.lt(lpivot.value, node'.pivotTable[0])
  ensures rpivot.Some? && |node'.pivotTable| > 0 ==> Keyspace.lt(Last(node'.pivotTable), rpivot.value)
  ensures lpivot.Some? ==> forall key | key in node'.buckets[0] :: Keyspace.lte(lpivot.value, key)
  ensures rpivot.Some? ==> forall key | key in Last(node'.buckets) :: Keyspace.lt(key, rpivot.value)
  ensures G.Successors(node') <= G.Successors(node)
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

  // Stuff for cutting up nodes

  // This is useful for proving NodeHasWFBuckets(node')
  // for indices over the given interval [a, b],
  // assuming we already know the buckets and pivots come from some other
  // well-formed node (possibly shifted by the amount d).
  lemma NodeHasWFBucketAtIdenticalSlice(
      node: G.Node, node': G.Node, a: int, b: int, d: int)
  requires WFNode(node)
  requires Pivots.WFPivots(node'.pivotTable)
  requires Pivots.NumBuckets(node'.pivotTable) == |node'.buckets|
  requires NodeHasWFBuckets(node)
  requires 0 <= a
  requires b < |node'.buckets|
  requires a-d >= 0
  requires b-d < |node.buckets|
  requires forall i | a <= i <= b :: node'.buckets[i] == node.buckets[i-d]
  requires forall i | a <= i < b :: node'.pivotTable[i] == node.pivotTable[i-d]
  requires b >= a && b < |node'.pivotTable| ==> (
      || (b-d < |node.pivotTable| && node'.pivotTable[b] == node.pivotTable[b-d])
      || (forall key | key in node'.buckets[b] :: Keyspace.lt(key, node'.pivotTable[b]))
    )
  requires b >= a && a-1 >= 0 ==> (
      || (a-1-d >= 0 && node'.pivotTable[a-1] == node.pivotTable[a-1-d])
      || (forall key | key in node'.buckets[a] :: Keyspace.lte(node'.pivotTable[a-1], key))
    )
  ensures forall i | a <= i <= b :: NodeHasWFBucketAt(node', i)
  {
    forall i | a <= i <= b
    ensures NodeHasWFBucketAt(node', i)
    {
      assert NodeHasWFBucketAt(node, i - d);
      forall key | key in node'.buckets[i]
      {
        Pivots.RouteIs(node'.pivotTable, key, i);
      }
    }
  }

  //// Split

  predicate ValidSplit(f: NodeFusion)
  {
    && WFNode(f.fused_parent)
    && WFNode(f.fused_child)

    && f.fused_parent.children.Some?
    && 0 <= f.slot_idx < |f.fused_parent.buckets|

    && var lbound := (if f.slot_idx > 0 then Some(f.fused_parent.pivotTable[f.slot_idx - 1]) else None);
    && var ubound := (if f.slot_idx < |f.fused_parent.pivotTable| then Some(f.fused_parent.pivotTable[f.slot_idx]) else None);
    && var child := CutoffNode(f.fused_child, lbound, ubound);

    && 1 <= f.num_children_left < |child.buckets|
    && f.fused_parent.children.value[f.slot_idx] == f.fused_childref
    && child.pivotTable[f.num_children_left - 1] == f.pivot
    && Pivots.Route(f.fused_parent.pivotTable, f.pivot) == f.slot_idx

    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    // We require buffer to already be flushed.
    && f.fused_parent.buckets[f.slot_idx] == map[]

    && f.split_parent == Node(
      insert(f.fused_parent.pivotTable, f.pivot, f.slot_idx),
      Some(replace1with2(f.fused_parent.children.value, f.left_childref, f.right_childref, f.slot_idx)),
      replace1with2(
        f.fused_parent.buckets,
        //SplitBucketLeft(f.fused_parent.buckets[f.slot_idx], f.pivot),
        //SplitBucketRight(f.fused_parent.buckets[f.slot_idx], f.pivot),
        map[],
        map[],
        f.slot_idx)
    )

    && f.left_child == Node(
      child.pivotTable[ .. f.num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. f.num_children_left ]) else None,
      child.buckets[ .. f.num_children_left ]
    )

    && f.right_child == Node(
      child.pivotTable[ f.num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ f.num_children_left .. ]) else None,
      child.buckets[ f.num_children_left .. ]
    )
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
    && f.split_parent.buckets[f.slot_idx] == map[]
    && f.split_parent.buckets[f.slot_idx + 1] == map[]

    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    // TODO require bucket to be empty before merge?
    && f.fused_parent == Node(
      remove(f.split_parent.pivotTable, f.slot_idx),
      Some(replace2with1(f.split_parent.children.value, f.fused_childref, f.slot_idx)),
      replace2with1(f.split_parent.buckets, map[], f.slot_idx)
    )

    // this is actually an invariant which follows from fixed height of the tree,
    // but we currently don't track that as an invariant... should we?
    && (f.left_child.children.Some? ==> f.right_child.children.Some?)
    && (f.left_child.children.None? ==> f.right_child.children.None?)

    && var lbound := (if f.slot_idx > 0 then Some(f.split_parent.pivotTable[f.slot_idx - 1]) else None);
    && var ubound := (if f.slot_idx + 1 < |f.split_parent.pivotTable| then Some(f.split_parent.pivotTable[f.slot_idx + 1]) else None);

    && var left := CutoffNode(f.left_child, lbound, Some(f.pivot));
    && var right := CutoffNode(f.right_child, Some(f.pivot), ubound);

    // TODO this isn't quite right:
    // we need to cut out every key > pivot in leftChild
    // and likewise cut out every key < pivot in rightChild
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
  }

  function RepivotReads(r: Repivot) : seq<ReadOp>
  requires ValidRepivot(r)
  {
    [
      ReadOp(r.ref, r.leaf)
    ]
  }

  function method JoinBuckets(buckets: seq<Bucket>) : (bucket : Bucket)
  {
    if |buckets| == 0 then map[] else MapUnion(JoinBuckets(DropLast(buckets)), Last(buckets))
  }

  function method SplitBucketOnPivots(pivots: seq<Key>, bucket: Bucket) : (buckets: seq<Bucket>)
  ensures |buckets| == |pivots| + 1
  {
    if |pivots| == 0 then (
      [bucket]
    ) else (
      var l := map key | key in bucket && Keyspace.lt(key, Last(pivots)) :: bucket[key];
      var r := map key | key in bucket && Keyspace.lte(Last(pivots), key) :: bucket[key];

      SplitBucketOnPivots(DropLast(pivots), l) + [r]
    )
  }

  function method ApplyRepivot(leaf: Node, pivots: seq<Key>) : (leaf': Node)
  requires WFNode(leaf)
  requires leaf.children.None?
  requires Pivots.WFPivots(pivots)
  {
    Node(pivots, None, SplitBucketOnPivots(pivots, JoinBuckets(leaf.buckets)))
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
  import Pivots = PivotsLib
  import M = ValueMessage

  import MS = MapSpec
  import Keyspace = MS.Keyspace
  type Key = Keyspace.Element

  lemma ValidFlushWritesWFNodes(flush: NodeFlush)
  requires ValidFlush(flush)
  ensures forall i | 0 <= i < |FlushOps(flush)| :: WFNode(FlushOps(flush)[i].node)
  {
    var newparent := G.Node(
        flush.parent.pivotTable,
        Some(flush.parent.children.value[flush.slotIndex := flush.newchildref]),
        flush.parent.buckets[flush.slotIndex := map[]]
      );
    //var newchild := AddMessagesToNode(flush.child, flush.parent.buckets[flush.slotIndex]);

    forall i | 0 <= i < |newparent.buckets|
    ensures NodeHasWFBucketAt(newparent, i)
    {
      //if (i == flush.slotIndex) {
      //  assert NodeHasWFBucketAt(newparent, i);
      //} else {
      assert NodeHasWFBucketAt(flush.parent, i);
      //  assert NodeHasWFBucketAt(newparent, i);
      //}
    }

    //assert WFNode(newparent);
    //assert WFNode(newchild);
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

    NodeHasWFBucketAtIdenticalSlice(fused_parent, split_parent, 0, slot_idx - 1, 0);
    NodeHasWFBucketAtIdenticalSlice(fused_parent, split_parent, slot_idx + 2, |split_parent.buckets| - 1, 1);

    assert WFNode(split_parent);

    Pivots.WFSlice(child.pivotTable, 0, f.num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, f.num_children_left);

    NodeHasWFBucketAtIdenticalSlice(child, left_child, 0, |left_child.buckets| - 1, 0);
    NodeHasWFBucketAtIdenticalSlice(child, right_child, 0, |right_child.buckets| - 1, -f.num_children_left);

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

    Pivots.WFPivotsRemoved(split_parent.pivotTable, slot_idx);

    NodeHasWFBucketAtIdenticalSlice(split_parent, fused_parent, 0, slot_idx - 1, 0);
    NodeHasWFBucketAtIdenticalSlice(split_parent, fused_parent, slot_idx + 1, |fused_parent.buckets| - 1, -1);

    assert WFNode(fused_parent);
    Pivots.PivotNotMinimum(split_parent.pivotTable, slot_idx);
    Pivots.WFConcat3(left_child.pivotTable, pivot, right_child.pivotTable);

    NodeHasWFBucketAtIdenticalSlice(left_child, fused_child, 0, |left_child.buckets| - 1, 0);
    NodeHasWFBucketAtIdenticalSlice(right_child, fused_child, |left_child.buckets|, |fused_child.buckets| - 1, |left_child.buckets|);

    assert WFNode(fused_child);
  }

  lemma SplitBucketOnPivotsCorrect(pivots: seq<Key>, bucket: G.Bucket, buckets: seq<G.Bucket>)
  requires Pivots.WFPivots(pivots)
  requires forall key | key in bucket :: bucket[key] != M.IdentityMessage()
  requires buckets == SplitBucketOnPivots(pivots, bucket)

  ensures |buckets| == |pivots| + 1
  ensures forall i | 0 <= i < |buckets| :: WFBucket(buckets[i], pivots, i)
  ensures forall i, key | 0 <= i < |buckets| && key in buckets[i] :: key in bucket
  ensures JoinBuckets(buckets) == bucket
  {
    if |pivots| == 0 {
    } else {
      var l := map key | key in bucket && Keyspace.lt(key, Last(pivots)) :: bucket[key];
      var r := map key | key in bucket && Keyspace.lte(Last(pivots), key) :: bucket[key];

      var bucketsPref := SplitBucketOnPivots(DropLast(pivots), l);
      Pivots.WFSlice(pivots, 0, |pivots| - 1);
      SplitBucketOnPivotsCorrect(DropLast(pivots), l, bucketsPref);

      forall i | 0 <= i < |buckets|
      ensures WFBucket(buckets[i], pivots, i)
      {
        if i < |buckets| - 1 {
          assert WFBucket(bucketsPref[i], DropLast(pivots), i);
          forall key | key in buckets[i] ensures Pivots.Route(pivots, key) == i
          {
            assert Pivots.Route(DropLast(pivots), key) == i;
            assert buckets[i] == bucketsPref[i];
            assert key in bucketsPref[i];
            assert key in l;
            Pivots.RouteIs(pivots, key, i);
          }
          assert WFBucket(buckets[i], pivots, i);
        } else {
          forall key | key in buckets[i] ensures Pivots.Route(pivots, key) == i
          {
            Pivots.RouteIs(pivots, key, i);
          }
          assert WFBucket(buckets[i], pivots, i);
        }
      }
    }
  }

  lemma JoinBucketsNoIdentity(buckets: seq<G.Bucket>)
  requires forall i | 0 <= i < |buckets| :: forall key | key in buckets[i] :: buckets[i][key] != M.IdentityMessage()
  ensures forall key | key in JoinBuckets(buckets) :: JoinBuckets(buckets)[key] != M.IdentityMessage()
  {
    if |buckets| == 0 {
    } else {
      JoinBucketsNoIdentity(DropLast(buckets));
    }
  }

  lemma WFApplyRepivot(leaf: G.Node, pivots: seq<Key>)
  requires WFNode(leaf)
  requires leaf.children.None?
  requires Pivots.WFPivots(pivots)
  ensures WFNode(ApplyRepivot(leaf, pivots))
  {
    var j := JoinBuckets(leaf.buckets);
    var s := SplitBucketOnPivots(pivots, j);
    forall i | 0 <= i < |leaf.buckets|
    ensures forall key | key in leaf.buckets[i] :: leaf.buckets[i][key] != M.IdentityMessage()
    {
      assert NodeHasWFBucketAt(leaf, i);
    }
    JoinBucketsNoIdentity(leaf.buckets);
    SplitBucketOnPivotsCorrect(pivots, j, s);
  }

  lemma ValidRepivotWFNodes(r: Repivot)
  requires ValidRepivot(r)
  ensures forall i | 0 <= i < |RepivotOps(r)| :: WFNode(RepivotOps(r)[i].node)
  {
    WFApplyRepivot(r.leaf, r.pivots);
  }

  // This lemma is useful for BetreeBlockCache
  lemma ValidStepWritesWFNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: WFNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeInsert(ins) => {}
      case BetreeFlush(flush) => {
        ValidFlushWritesWFNodes(flush);
      }
      case BetreeGrow(growth) => {}
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
