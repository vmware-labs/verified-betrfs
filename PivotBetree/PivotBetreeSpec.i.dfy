// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../lib/Buckets/BoundedPivotsLib.i.dfy"
include "../lib/Buckets/BucketsLib.i.dfy"
include "../lib/Buckets/BucketMap.i.dfy"
include "../lib/Buckets/TranslationLib.i.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "../lib/Buckets/BucketWeights.i.dfy"
include "../lib/Buckets/BucketFlushModel.i.dfy"
include "PivotBetreeGraph.i.dfy"

//
// A PivotBetree refines a Betree, carrying forward the tree structure
// but refining the abstract infinite key maps with key ranges separated
// by pivot keys.
//

module PivotBetreeSpec {
  import MS = MapSpec

  import opened G = PivotBetreeGraph
  import opened Sequences
  import opened Maps
  import opened Options
  import opened Bounds
  import opened BucketsLib
  import opened BucketMaps
  import opened BucketWeights
  import UI
  import opened KeyType
  import opened ValueMessage

  import opened Pivots = BoundedPivotsLib
  import opened TranslationLib
  import Upperbounded_Lexicographic_Byte_Order
  import BucketFlushModel

  export Spec provides BetreeStep, ValidBetreeStep, BetreeStepReads, BetreeStepOps, BetreeStepUI, G, WFNode, InvNode, MS
  export Internal reveals *

  export extends Spec // Default export-style is Spec

  // TODO(travis) the BoundedNode condition isn't useful at the PivotBetree state
  // machine level. Weights are only useful at the impl level, so I'm not sure it's
  // a good idea to have this here.

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
    && WFEdges(node.edgeTable, node.pivotTable)
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

  //// Query

  datatype Layer = Layer(readOp: G.ReadOp, currentKey: Key)
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
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].readOp.node)
  }

  predicate LookupVisitsWellMarshalledBuckets(lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  {
    forall i :: 0 <= i < |lookup| ==> BucketWellMarshalled(
      lookup[i].readOp.node.buckets[Route(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)])
  }

  predicate LookupBoundedKey(lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) ==> 
      BoundedKey(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey))
  }

  predicate LookupFollowsChildRefAtLayer(lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx)
  requires idx < |lookup| - 1;
  requires WFNode(lookup[idx].readOp.node)
  requires BoundedKey(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey)
  {
    && lookup[idx].readOp.node.children.Some?
    && var r := Route(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey);
    && lookup[idx].readOp.node.children.value[r] == lookup[idx+1].readOp.ref
  }

  predicate LookupFollowsChildRefs(lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(lookup, idx))
  }

  predicate LookupFollowsChildEdgeAtLayer(lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx)
  requires idx < |lookup| - 1
  requires WFNode(lookup[idx].readOp.node)
  requires BoundedKey(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey)
  {
    && TranslateKey(lookup[idx].readOp.node.pivotTable, lookup[idx].readOp.node.edgeTable,
        lookup[idx].currentKey) == lookup[idx+1].currentKey
  }

  predicate LookupFollowsChildEdges(lookup: Lookup)
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildEdgeAtLayer(lookup, idx))
  }

  function NodeLookup(node: Node, key: Key) : Message
  requires WFBucketList(node.buckets, node.pivotTable)
  requires BoundedKey(node.pivotTable, key)
  {
    BucketListGet(node.buckets, node.pivotTable, key)
  }

  function InterpretLookup(lookup: Lookup) : Message
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  {
    if |lookup| == 0 then
      Update(NopDelta())
    else
      Merge(InterpretLookup(DropLast(lookup)), NodeLookup(Last(lookup).readOp.node, Last(lookup).currentKey))
  }

  function InterpretLookupAccountingForLeaf(lookup: Lookup) : Message
  requires |lookup| > 0
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  {
    if Last(lookup).readOp.node.children.Some? then
      InterpretLookup(lookup)
    else
      Merge(InterpretLookup(lookup), DefineDefault())
  }

  predicate WFLookupForKey(lookup: Lookup, key: Key)
  {
    && |lookup| > 0
    && lookup[0].readOp.ref == Root()
    && lookup[0].currentKey == key
    && LookupVisitsWFNodes(lookup)
    && LookupBoundedKey(lookup)
    && LookupFollowsChildRefs(lookup)
    && LookupFollowsChildEdges(lookup)
  }

  predicate ValidQuery(q: LookupQuery) {
    && WFLookupForKey(q.lookup, q.key)
    && (LookupVisitsWellMarshalledBuckets(q.lookup) ==>
        BufferDefinesValue(InterpretLookupAccountingForLeaf(q.lookup), q.value)
    )
  }

  function LayersToReadOps(lookup: seq<Layer>): (result: seq<ReadOp>)
    ensures |lookup| == |result|
    ensures forall idx :: 0 <= idx < |lookup| ==> lookup[idx].readOp == result[idx]
  {
    if |lookup| == 0
    then
        []
    else
        LayersToReadOps(DropLast(lookup)) + [Last(lookup).readOp]
  }

  function QueryReads(q: LookupQuery): seq<ReadOp> {
    LayersToReadOps(q.lookup)
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
    translations: TranslationTable,
    lookup: Lookup)

  predicate ValidTranslationTable(lookup: Lookup, tt: TranslationTable, offset: int)
  requires 0 <= offset < |lookup|
  {
    && |lookup| == |tt| + 1 + offset
    && (forall i | 0 <= i < |tt| :: 
        && (tt[i].Some? ==> 
            && IsPrefix(tt[i].value.prefix, lookup[i+1+offset].currentKey)
            && IsPrefix(tt[i].value.newPrefix, lookup[0].currentKey)) // needed by succmodel
        && lookup[0].currentKey == ApplyPrefixSet(tt[i], lookup[i+1+offset].currentKey))
  }

  function {:opaque} LookupTranslationTable(lookup: Lookup, idx: int, prev: Option<PrefixSet>)
  : (tt: TranslationTable)
  requires 0 <= idx < |lookup|
  requires idx == 0 ==> prev.None?
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  requires LookupFollowsChildEdges(lookup)
  requires prev.Some? ==> IsPrefix(prev.value.prefix, lookup[idx].currentKey)
  requires lookup[0].currentKey == ApplyPrefixSet(prev, lookup[idx].currentKey)
  decreases |lookup| - idx
  ensures ValidTranslationTable(lookup, tt, idx)
  ensures |tt| > 0 ==> tt[1..] == LookupTranslationTable(lookup, idx + 1, tt[0])
  {
    if idx == |lookup| - 1 then (
      []
    ) else (
      var node := lookup[idx].readOp.node;
      var key := lookup[idx].currentKey;

      var curr := Translate(node.pivotTable, node.edgeTable, key);
      assert LookupFollowsChildEdgeAtLayer(lookup, idx);

      var pset := ComposePrefixSet(prev, curr);
      assert pset.Some? ==> IsPrefix(pset.value.prefix, lookup[idx+1].currentKey); // observe

      var tt := [ pset ] + LookupTranslationTable(lookup, idx + 1, pset);
      tt
    )
  }

  function LookupUpperBoundAtLayer(layer: Layer, pset: Option<PrefixSet>, startkey: Key) : (r: Option<Key>)
  requires WFNode(layer.readOp.node)
  requires pset.Some? ==> IsPrefix(pset.value.prefix, layer.currentKey)
  requires ApplyPrefixSet(pset, layer.currentKey) == startkey
  requires BoundedKey(layer.readOp.node.pivotTable, layer.currentKey)
  ensures pset.Some? ==> (
    var left := KeyToElement(startkey);
    var right := if r.Some? then KeyToElement(r.value) else Pivots.Keyspace.Max_Element;
    && Pivots.Keyspace.lt(left, right)
    && AllKeysInBetweenHasPrefix(left, right, pset.value.newPrefix))
  {
    var pivots := layer.readOp.node.pivotTable;
    var r := Route(pivots, layer.currentKey);
    var upper := if pset.None?
    then ( pivots[r+1] )
    else (
      var (left, right) := TranslatePivotPairInternal(KeyToElement(layer.currentKey),
        pivots[r+1], pset.value.prefix, pset.value.newPrefix);
        right
    );

    if upper.Element? then (
      var k: Key := upper.e;
      Some(k)
    ) else (
      None
    )
  }

  function OptionKeyMin(k1: Option<Key>, k2: Option<Key>) : Option<Key>
  {
    match k1 {
      case Some(key1) => match k2 {
        case Some(key2) => 
          if G.Keyspace.lt(k1.value, k2.value) then Some(k1.value) else Some(k2.value)
        case None => k1
      }
      case None => k2
    }
  }

  function {:opaque} LookupUpperBound(lookup: Lookup, tt: TranslationTable) : Option<Key>
  requires LookupVisitsWFNodes(lookup)
  requires LookupBoundedKey(lookup)
  requires |lookup| > 0 ==> ValidTranslationTable(lookup, tt, 0)
  decreases |lookup|
  {
    if |lookup| == 0 then (
      None
    ) else (
      var pset := if |tt| == 0 then None else Last(tt);
      var tt' := if |tt| == 0 then tt else DropLast(tt);

      OptionKeyMin(
        LookupUpperBound(DropLast(lookup), tt'),
        LookupUpperBoundAtLayer(Last(lookup), pset, lookup[0].currentKey)
      )
    )
  }

  function SuccBucketAtLayer(buckets: seq<Bucket>, tt: TranslationTable, idx: int) : Bucket
  requires 0 <= idx < |buckets|
  requires |tt| + 1 == |buckets|
  requires PreWFBucket(buckets[idx])
  {
    var pset := if idx == 0 then None else tt[idx - 1];
    if pset.None? then buckets[idx]
    else TranslateBucket(buckets[idx], pset.value.prefix, pset.value.newPrefix)
  }

  function TranslateSuccBuckets(buckets: seq<Bucket>, tt: TranslationTable, idx: int) 
    : (buckets': seq<Bucket>)
  requires 0 <= idx <= |buckets|
  requires |tt| + 1 == |buckets|
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  decreases |buckets| - idx
  ensures |buckets| == |buckets'| + idx
  ensures forall i | 0 <= i < |buckets'| :: buckets'[i] == SuccBucketAtLayer(buckets, tt, idx+i)
  ensures BucketListWellMarshalled(buckets) ==> BucketListWellMarshalled(buckets')
  {
    if idx == |buckets| then (
      []
    ) else (
      var bucket := SuccBucketAtLayer(buckets, tt, idx);
      [bucket] + TranslateSuccBuckets(buckets, tt, idx + 1)
    )
  }

  predicate BufferDefinesEmptyValue(m: Message)
  {
    Merge(m, DefineDefault()) == DefineDefault()
  }

  predicate ValidSuccQuery(sq: SuccQuery)
  {
    && var startKey := if sq.start.NegativeInf? then [] else sq.start.key;
    && WFLookupForKey(sq.lookup, startKey)

    && sq.translations == LookupTranslationTable(sq.lookup, 0, None)
    && var lookupUpperBound := LookupUpperBound(sq.lookup, sq.translations);
    && Last(sq.lookup).readOp.node.children.None?

    && |sq.lookup| == |sq.buckets|
    && (forall i | 0 <= i < |sq.lookup| :: sq.buckets[i] == 
      sq.lookup[i].readOp.node.buckets[
        Route(sq.lookup[i].readOp.node.pivotTable, sq.lookup[i].currentKey)])

    && (BucketListWellMarshalled(sq.buckets) ==>
      && MS.NonEmptyRange(sq.start, sq.end)
      && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, sq.end))
      && var translatedbuckets := TranslateSuccBuckets(sq.buckets, sq.translations, 0);
      && sq.results == SortedSeqOfKeyValueMap(
        KeyValueMapOfBucket(ClampRange(ComposeSeq(MapsOfBucketList(translatedbuckets)), sq.start, sq.end))))
  }

  function SuccQueryReads(q: SuccQuery): seq<ReadOp> {
    LayersToReadOps(q.lookup)
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
    newparent: Node,
    childref: Reference,
    child: Node,
    newchildref: Reference,
    newchild: Node,

    ghost slot_idx: int
  )

  predicate ValidFlush(f: NodeFlush)
  {
    && WFNode(f.parent)
    && WFNode(f.child)

    && 0 <= f.slot_idx < |f.parent.buckets|
    && f.parent.children.Some?

    && f.parent.children.value[f.slot_idx] == f.childref
    && ParentKeysInChildRange(f.parent.pivotTable, f.parent.edgeTable, f.child.pivotTable, f.slot_idx)
    && var child' := RestrictAndTranslateChild(f.parent, f.child, f.slot_idx);
    && WeightBucketList(child'.buckets) <= MaxTotalBucketWeight()
    // TODO(Jialin): for now implementation can check this and no op if this is the case
    // but what we want is different version of flush, where if this isn't met then we don't
    // flush the translation down, just the message itself.
    && var pfr := BucketFlushModel.partialFlush(
        f.parent.buckets[f.slot_idx], child'.pivotTable, child'.buckets);
    && f.newchild == Node(
        child'.pivotTable,
        child'.edgeTable,
        child'.children,
        pfr.bots
      )
    && WFBucketList(f.newchild.buckets, f.newchild.pivotTable)
    && f.newparent == Node(
        f.parent.pivotTable,
        f.parent.edgeTable[f.slot_idx := None],
        Some(f.parent.children.value[f.slot_idx := f.newchildref]),
        f.parent.buckets[f.slot_idx := pfr.top]
      )
    && WFBucket(f.newparent.buckets[f.slot_idx])
    && WeightBucket(f.newparent.buckets[f.slot_idx]) <= WeightBucket(f.parent.buckets[f.slot_idx])
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
    var allocop := G.AllocOp(f.newchildref, f.newchild);
    var writeop := G.WriteOp(f.parentref, f.newparent);
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
    var newroot := Node(InitPivotTable(), [None], Some([growth.newchildref]), [EmptyBucket()]);
    var allocop := G.AllocOp(growth.newchildref, growth.oldroot);
    var writeop := G.WriteOp(Root(), newroot);
    [allocop, writeop]
  }

  // Datatype for Split and Merge

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

  // Useful functions and lemmas for Split, Merge (other redirects)

  function {:opaque} CutoffNodeAndKeepLeft(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  requires ValidLeftCutOffKey(node.pivotTable, pivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures node'.pivotTable[0] == node.pivotTable[0]
  ensures Last(node'.pivotTable) == KeyToElement(pivot)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    reveal_SplitBucketLeft();
    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    var bplleftPivots := SplitLeft(node.pivotTable, pivot);
    var leftedges := SplitLeftEdges(node.edgeTable, node.pivotTable, pivot);

    reveal_CutoffForLeft();
  
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft+1]) else None;
    var leftBuckets := SplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    WFSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);
    WeightSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    Node(bplleftPivots, leftedges, leftChildren, leftBuckets)
  }

  function {:opaque} CutoffNodeAndKeepRight(node: Node, pivot: Key) : (node': Node)
  requires WFNode(node)
  requires BoundedKey(node.pivotTable, pivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures pivot == node'.pivotTable[0].e
  ensures Last(node.pivotTable) == Last(node'.pivotTable)
  ensures G.Successors(node') <= G.Successors(node)
  ensures WeightBucketList(node'.buckets) <= WeightBucketList(node.buckets)
  ensures |node'.buckets| <= |node.buckets|
  {
    reveal_SplitBucketRight();
    var cRight := CutoffForRight(node.pivotTable, pivot);
    var bplrightPivots := SplitRight(node.pivotTable, pivot);
    var rightedges := SplitRightEdges(node.edgeTable, node.pivotTable, pivot);

    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var rightBuckets := SplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    WFSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
    WeightSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);

    Node(bplrightPivots, rightedges, rightChildren, rightBuckets)
  }

  predicate ValidSplitKey(node: Node, lpivot: Key, rpivot: Option<Key>)
  requires WFNode(node)
  {
    && BoundedKey(node.pivotTable, lpivot)
    && (rpivot.Some? ==> ValidLeftCutOffKey(node.pivotTable, rpivot.value))
    && (rpivot.Some? ==> G.Keyspace.lt(node.pivotTable[0].e, rpivot.value))
    && (rpivot.Some? ==> G.Keyspace.lt(lpivot, rpivot.value))
    && (rpivot.None? ==> Last(node.pivotTable) == Pivots.Keyspace.Max_Element)
  }

  function {:opaque} CutoffNode(node: Node, lpivot: Key, rpivot: Option<Key>) : (node' : Node)
  requires WFNode(node)
  requires ValidSplitKey(node, lpivot, rpivot)
  ensures node.children.Some? <==> node'.children.Some?
  ensures WFNode(node')
  ensures lpivot == node'.pivotTable[0].e
  ensures rpivot.Some? ==> Last(node'.pivotTable) == KeyToElement(rpivot.value)
  ensures rpivot.None? ==> Last(node'.pivotTable) == Last(node.pivotTable)
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
          node'
      )
    }
  }

  function {:timeLimitMultiplier 2} RestrictAndTranslateChild(parent: Node, child: Node, slot: int): (newchild: Node)
  requires WFNode(parent)
  requires WFNode(child)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  requires ParentKeysInChildRange(parent.pivotTable, parent.edgeTable, child.pivotTable, slot)
  ensures NumBuckets(newchild.pivotTable) == |newchild.buckets|
  ensures newchild.children.Some? ==> |newchild.buckets| == |newchild.children.value|
  ensures WFPivots(newchild.pivotTable)
  ensures WFEdges(newchild.edgeTable, newchild.pivotTable)
  ensures WFBucketList(newchild.buckets, newchild.pivotTable)
  ensures |newchild.buckets| <= MaxNumChildren()
  ensures Last(newchild.pivotTable) == parent.pivotTable[slot+1]
  {
    Pivots.Keyspace.reveal_IsStrictlySorted();
    if parent.edgeTable[slot].None? then (
      var lbound := getlbound(parent, slot);
      var ubound := getubound(parent, slot);

      ContainsRangeImpliesBoundedKey(child.pivotTable, parent.pivotTable[slot], parent.pivotTable[slot+1]);
      assert BoundedKey(child.pivotTable, lbound);
      CutoffNode(child, lbound, ubound)
    ) else (
      var (lbound, ubound) := TranslatePivotPair(parent.pivotTable, parent.edgeTable, slot);
      var lboundkey : Key := lbound.e;
      var uboundkey := if ubound.Element? then (var k: Key := ubound.e; Some(k)) else None;
      var child' := CutoffNode(child, lboundkey, uboundkey);

      var parentprefix := PivotLcp(parent.pivotTable[slot], parent.pivotTable[slot+1]);
      var childprefix := parent.edgeTable[slot].value;
      
      TranslatePivotPairRangeProperty(parent.pivotTable[slot], parent.pivotTable[slot+1], parentprefix, childprefix);
      var newpivots := TranslatePivots(child'.pivotTable, childprefix, parentprefix, parent.pivotTable[slot+1], 0);
      assert newpivots[0] == parent.pivotTable[slot];
      assert Last(newpivots) == parent.pivotTable[slot+1];

      PrefixOfLcpIsPrefixOfKeys(parent.pivotTable[slot], parent.pivotTable[slot+1], parentprefix);
      assert AllKeysInBetweenHasPrefix(newpivots[0], Last(newpivots), parentprefix);

      var newedges := TranslateEdges(child'.edgeTable, child'.pivotTable, 0);
      assert WFEdges(newedges, newpivots);

      var translatedbuckets := TranslateBuckets(child'.buckets, childprefix, parentprefix);
  
      Node(newpivots, newedges, child'.children, translatedbuckets)
    )
  }

  //// Split
  function SplitChildLeft(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable| - 2
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  requires 0 <= num_children_left <= |child.edgeTable|
  {
    Node(
      child.pivotTable[ .. num_children_left + 1],
      child.edgeTable[ .. num_children_left ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function SplitChildRight(child: Node, num_children_left: int) : Node
  requires 0 <= num_children_left <= |child.pivotTable| - 1
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets| 
  requires 0 <= num_children_left <= |child.edgeTable|
  {
    Node(
      child.pivotTable[ num_children_left .. ],
      child.edgeTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  function SplitParent(fused_parent: Node, pivot: Key, slot_idx: int, left_childref: Reference, right_childref: Reference) : Node
  requires WFNode(fused_parent)
  requires 0 <= slot_idx < NumBuckets(fused_parent.pivotTable)
  requires fused_parent.children.Some?
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires PreWFBucket(fused_parent.buckets[slot_idx])
  {
    Node(
      insert(fused_parent.pivotTable, KeyToElement(pivot), slot_idx+1),
      replace1with2(fused_parent.edgeTable, None, None, slot_idx),
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      SplitBucketInList(fused_parent.buckets, slot_idx, pivot)
    )
  }

  function getlbound(parent: Node, slot: int) : Key
  requires WFNode(parent)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  {
    GetKey(parent.pivotTable, slot)
  }

  function getubound(parent: Node, slot: int) : Option<Key>
  requires WFNode(parent)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  {
    if parent.pivotTable[slot+1].Element? 
    then Some(GetKey(parent.pivotTable, slot+1))
    else None
  }

  predicate SplitChildrenWeight(buckets: BucketList, num_children_left: int)
  requires 1 <= num_children_left < |buckets|
  {
    && WeightBucketList(buckets[..num_children_left]) <= MaxTotalBucketWeight()
    && WeightBucketList(buckets[num_children_left..]) <= MaxTotalBucketWeight()
  }

  predicate ValidSplit(f: NodeFusion)
  {
    && WFNode(f.fused_parent)
    && WFNode(f.fused_child)

    && f.fused_parent.children.Some?
    && 0 <= f.slot_idx < |f.fused_parent.buckets|
    && |f.fused_parent.buckets| <= MaxNumChildren() - 1
    && PivotInsertable(f.fused_parent.pivotTable, f.slot_idx+1, f.pivot)
    && f.fused_parent.children.value[f.slot_idx] == f.fused_childref

    && ParentKeysInChildRange(f.fused_parent.pivotTable, f.fused_parent.edgeTable, f.fused_child.pivotTable, f.slot_idx)
    && var child := RestrictAndTranslateChild(f.fused_parent, f.fused_child, f.slot_idx);
    && 1 <= f.num_children_left < |child.buckets|
    && SplitChildrenWeight(child.buckets, f.num_children_left)
    && child.pivotTable[f.num_children_left].e == f.pivot

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
    && f.split_parent.pivotTable[f.slot_idx+1].e == f.pivot
    && f.split_parent.children.Some?
    && f.split_parent.children.value[f.slot_idx] == f.left_childref
    && f.split_parent.children.value[f.slot_idx + 1] == f.right_childref
    && WeightBucketList(f.left_child.buckets) + WeightBucketList(f.right_child.buckets) <= MaxTotalBucketWeight()
    && |f.left_child.buckets| + |f.right_child.buckets| <= MaxNumChildren()
    && (f.left_childref == f.right_childref ==> f.left_child == f.right_child)

    // this is actually an invariant which follows from fixed height of the tree,
    // but we currently don't track that as an invariant... should we?
    && (f.left_child.children.Some? ==> f.right_child.children.Some?)
    && (f.left_child.children.None? ==> f.right_child.children.None?)

    && ParentKeysInChildRange(f.split_parent.pivotTable, f.split_parent.edgeTable, f.left_child.pivotTable, f.slot_idx)
    && ParentKeysInChildRange(f.split_parent.pivotTable, f.split_parent.edgeTable, f.right_child.pivotTable, f.slot_idx+1)
    && var left := RestrictAndTranslateChild(f.split_parent, f.left_child, f.slot_idx);
    && var right := RestrictAndTranslateChild(f.split_parent, f.right_child, f.slot_idx+1);
    && WeightBucketList(left.buckets) + WeightBucketList(right.buckets) <= MaxTotalBucketWeight()
    && f.fused_child == FusedChild(left, right, f.pivot)
    && f.fused_parent == Node(
      remove(f.split_parent.pivotTable, f.slot_idx+1),
      replace2with1(f.split_parent.edgeTable, None, f.slot_idx),
      Some(replace2with1(f.split_parent.children.value, f.fused_childref, f.slot_idx)),
      MergeBucketsInList(f.split_parent.buckets, f.slot_idx)
    )
  }

  function FusedChild(left: Node, right: Node, pivot: Key): Node
  requires WFPivots(left.pivotTable)
  requires WFPivots(right.pivotTable)
  requires left.children.Some? <==> right.children.Some?
  {
    Node(
      concat3(left.pivotTable[..|left.pivotTable|-1], KeyToElement(pivot), right.pivotTable[1..]),
      concat(left.edgeTable, right.edgeTable),
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

  datatype Repivot = Repivot(ref: Reference, leaf: Node, pivots: PivotTable, pivot: Key)

  predicate ValidRepivot(r: Repivot)
  {
    && WFNode(r.leaf)
    && |r.pivots| <= MaxNumChildren() + 1
    && |r.leaf.buckets| == 1
    && ContainsAllKeys(r.pivots)
    && r.leaf.edgeTable[0].None?
    && r.leaf.children.None?
    && r.pivots == insert(InitPivotTable(), KeyToElement(r.pivot), 1)
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
    assert WFEdges([None, None], r.pivots);
    Node(
      r.pivots,
      [ None, None ],
      None,
      [
        SplitBucketLeft(r.leaf.buckets[0], r.pivot),
        SplitBucketRight(r.leaf.buckets[0], r.pivot)
      ])
  }

  function RepivotOps(r: Repivot) : seq<Op>
  requires ValidRepivot(r)
  {
    [
      G.WriteOp(r.ref, ApplyRepivot(r))
    ]
  }

  //// Clone

  datatype NodeClone = NodeClone(oldroot: Node, newroot: Node, from: Key, to: Key)

  // TODO: split into separate step
  function RestrictAndTranslateNode(node: Node, from: Key, to: Key) : (node': Node)
  requires WFNode(node)
  requires ContainsAllKeys(node.pivotTable)
  requires node.children.Some?
  requires to != []
  ensures WFNode(node')
  ensures WeightBucketList(node'.buckets) == 0
  {
    var fromend := ShortestUncommonPrefix(from, |from|);
    var fromendkey := if fromend.Element? then (var k : Key := fromend.e; Some(k)) else None;

    ContainsAllKeysImpliesBoundedKey(node.pivotTable, from);
    var fromnode := CutoffNode(node, from, fromendkey);
    assert WFNode(fromnode);

    PrefixOfLcpIsPrefixOfKeys(KeyToElement(from), fromend, from);
    Pivots.Keyspace.reveal_IsStrictlySorted();

    var toend := ShortestUncommonPrefix(to, |to|);
    var toendkey := if toend.Element? then (var k : Key := toend.e; Some(k)) else None;

    var e := TranslateElement(fromnode.pivotTable[|fromnode.pivotTable|-2], from, to);
    assert Pivots.Keyspace.lt(e, toend) by {
      if toend.Element? {
        KeyWithPrefixLt(to, toend.e, e.e);
      }
    }

    var topivots := TranslatePivots(fromnode.pivotTable, from, to, toend, 0);
    assert topivots[0] == KeyToElement(to);
    PrefixOfLcpIsPrefixOfKeys(topivots[0], Last(topivots), to);

    var toedges := TranslateEdges(fromnode.edgeTable, fromnode.pivotTable, 0);
    var tobuckets := EmptyBucketList(NumBuckets(topivots));
    WeightBucketListEmpty(NumBuckets(topivots));
    assert |tobuckets| == |fromnode.buckets|;

    Node(topivots, toedges, fromnode.children, tobuckets)
  }

  function {:timeLimitMultiplier 2} CloneNewRoot(node: Node, from: Key, to: Key) : (node': Node)
  requires WFNode(node)
  requires ContainsAllKeys(node.pivotTable)
  requires node.children.Some?
  requires to != []
  ensures WFPivots(node'.pivotTable)
  ensures WFEdges(node'.edgeTable, node'.pivotTable)
  ensures NumBuckets(node'.pivotTable) == |node'.buckets|
  ensures WFBucketList(node'.buckets, node'.pivotTable)
  ensures (node'.children.Some? ==> |node'.buckets| == |node'.children.value|)
  ensures WeightBucketList(node'.buckets) <= MaxTotalBucketWeight()
  ensures ContainsAllKeys(node'.pivotTable)
  {
    var tonode := RestrictAndTranslateNode(node, from, to);
    assert tonode.pivotTable[0] == KeyToElement(to);
    assert node.children.None? <==> tonode.children.None?;
    
    ContainsAllKeysImpliesBoundedKey(node.pivotTable, to);
    var lnode := CutoffNodeAndKeepLeft(node, to);
    assert Last(lnode.pivotTable) == KeyToElement(to);

    WeightBucketListConcat(lnode.buckets, tonode.buckets);
    assert WeightBucketList(lnode.buckets + tonode.buckets) == WeightBucketList(lnode.buckets);

    if Last(tonode.pivotTable).Max_Element? then (
      Node(
        lnode.pivotTable[..|lnode.pivotTable|-1] + tonode.pivotTable,
        lnode.edgeTable + tonode.edgeTable,
        Some(lnode.children.value + tonode.children.value),
        lnode.buckets + tonode.buckets
      )
    ) else (
      var toend := GetKey(tonode.pivotTable, |tonode.pivotTable|-1);
      var rnode := CutoffNodeAndKeepRight(node, toend);

      var cLeft := CutoffForLeft(node.pivotTable, to);
      var cRight := CutoffForRight(node.pivotTable, toend);

      WeightBucketListConcat(lnode.buckets, rnode.buckets);
      WeightBucketListConcat(lnode.buckets + tonode.buckets, rnode.buckets);
      WeightBucketListSubSets(node.buckets, node.pivotTable, cLeft, cRight, to, toend);

      assert WeightBucketList(lnode.buckets + rnode.buckets) <= WeightBucketList(node.buckets)
      by {
        reveal_CutoffNodeAndKeepLeft();
        reveal_CutoffNodeAndKeepRight();
      }

      Node(
        lnode.pivotTable[..|lnode.pivotTable|-1] + tonode.pivotTable + rnode.pivotTable[1..],
        lnode.edgeTable + tonode.edgeTable + rnode.edgeTable,
        Some(lnode.children.value + tonode.children.value + rnode.children.value),
        lnode.buckets + tonode.buckets + rnode.buckets
      )
    )
  }

  predicate ValidCloneBucketList(node: Node, prefix: Key)
  requires WFNode(node)
  requires ContainsAllKeys(node.pivotTable)
  {
    var prefixend := ShortestUncommonPrefix(prefix, |prefix|);
    ContainsAllKeysImpliesBoundedKey(node.pivotTable, prefix);

    var start := Route(node.pivotTable, prefix);
    var end := if prefixend.Max_Element? then |node.buckets| else Route(node.pivotTable, prefixend.e)+1;

    && BucketListNoKeyWithPrefix(node.buckets[start..end], prefix)
  }

  predicate ValidClone(clone: NodeClone)
  {
    && WFNode(clone.oldroot)
    && ContainsAllKeys(clone.oldroot.pivotTable)
    && ContainsAllKeys(clone.newroot.pivotTable)

    && clone.oldroot.children.Some?
    && clone.to != []
    && ValidCloneBucketList(clone.oldroot, clone.from)

    // from = old, to = new
    && clone.newroot == CloneNewRoot(clone.oldroot, clone.from, clone.to)
    && NumBuckets(clone.newroot.pivotTable) <= MaxNumChildren()
  }

  function CloneReads(clone: NodeClone) : seq<ReadOp>
  requires ValidClone(clone)
  {
    [G.ReadOp(Root(), clone.oldroot)]
  }

  function CloneOps(clone: NodeClone) : seq<Op>
  requires ValidClone(clone)
  {
    var writeop := G.WriteOp(Root(), clone.newroot);
    [ writeop ]
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
    | BetreeClone(clone: NodeClone)

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
      case BetreeClone(clone) => ValidClone(clone)
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
      case BetreeClone(clone) => CloneReads(clone)
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
      case BetreeClone(clone) => CloneOps(clone)
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
      case BetreeClone(clone) => uiop == MS.UI.CloneOp(clone.from, clone.to)
    }
  }

}