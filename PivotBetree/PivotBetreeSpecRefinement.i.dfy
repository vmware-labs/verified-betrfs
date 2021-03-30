// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
include "../Betree/Betree.i.dfy"
include "../Betree/BetreeInv.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "PivotBetreeSpecWFNodes.i.dfy"
//
// Lays out the abstraction function between the datatypes, setting
// up for PivotBetree_Refines_Betree.
//

module PivotBetreeSpecRefinement {
  import B = BetreeSpec`Internal
  import P = PivotBetreeSpec`Internal
  import opened ValueMessage`Internal
  import MS = MapSpec
  import opened Maps
  import opened Sequences
  import opened Options
  import opened BoundedPivotsLib
  import opened BucketsLib
  import opened TranslationLib
  import opened KeyType
  import PivotBetreeSpecWFNodes
  import opened BucketMaps
  import BucketFlushModel
  import Upperbounded_Lexicographic_Byte_Order

  type Node = B.G.Node
  type PNode = P.G.Node

  type Edge = B.G.Edge
  type Reference = B.G.Reference
  type Buffer = B.G.Buffer

  function IChildren(node: PNode) : (m: imap<Key, Edge>)
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires WFPivots(node.pivotTable)
  requires WFEdges(node.edgeTable, node.pivotTable)
  requires NumBuckets(node.pivotTable) == |node.buckets|
  {
    if node.children.Some? then (
      imap key:Key | BoundedKey(node.pivotTable, key) :: 
        B.G.Edge(
          TranslateKey(node.pivotTable, node.edgeTable, key),
          node.children.value[Route(node.pivotTable, key)]
        )
    ) else (
      imap[]
    )
  }

  function BucketOptGet(bucket: BucketMap, key: Key) : Message
  {
    if key in bucket then bucket[key] else IdentityMessage()
  }

  function BucketOptListGet(blist: BucketList, pivots: PivotTable, key: Key) : Message
  requires WFBucketList(blist, pivots)
  requires BoundedKey(pivots, key)
  {
    BucketOptGet(blist[Route(pivots, key)].as_map(), key)
  }

  function IBufferInternal(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: if BoundedKey(node.pivotTable, key) 
      then BucketOptListGet(node.buckets, node.pivotTable, key) else DefineDefault() 
    // safe because it's not reachable by any op
  }

  function IBufferLeaf(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    imap key:Key :: if BoundedKey(node.pivotTable, key) then Merge(
      BucketOptListGet(node.buckets, node.pivotTable, key),
      DefineDefault()
    ) else DefineDefault()
  }

  function IBuffer(node: PNode) : Buffer
  requires WFBucketList(node.buckets, node.pivotTable)
  {
    if node.children.Some? then
      IBufferInternal(node)
    else
      IBufferLeaf(node)
  }

  // This is the main part of the story: the refinement from pivot node to betree node.
  function INode(node: PNode) : Node
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires WFBucketList(node.buckets, node.pivotTable)
  requires WFEdges(node.edgeTable, node.pivotTable)
  ensures B.WFNode(INode(node))
  {
    B.G.Node(IChildren(node), IBuffer(node))
  }

  predicate ReadOpsBucketsWellMarshalled(readOps: seq<P.G.ReadOp>)
  {
    forall i | 0 <= i < |readOps| ::
      forall j | 0 <= j < |readOps[i].node.buckets| ::
        BucketWellMarshalled(readOps[i].node.buckets[j])
  }

  function IReadOp(readOp: P.G.ReadOp) : (r: B.G.ReadOp)
  requires P.WFNode(readOp.node)
  ensures B.WFNode(r.node)
  {
    B.G.ReadOp(readOp.ref, INode(readOp.node))
  }

  function IReadOps(readOps: seq<P.G.ReadOp>) : seq<B.G.ReadOp>
  requires forall i | 0 <= i < |readOps| :: P.WFNode(readOps[i].node)
  ensures |readOps| == |IReadOps(readOps)|
  ensures forall i | 0 <= i < |IReadOps(readOps)| :: B.WFNode(IReadOps(readOps)[i].node)
  {
    if |readOps| == 0 then [] else
      IReadOps(readOps[..|readOps|-1]) + [IReadOp(readOps[|readOps|-1])]
  }

  function ILayer(layer: P.Layer) : (l: B.Layer)
  requires P.WFNode(layer.readOp.node)
  ensures B.WFNode(l.readOp.node)
  {
    B.Layer(B.G.ReadOp(layer.readOp.ref, INode(layer.readOp.node)), layer.currentKey)
  }

  function ILayers(layers: seq<P.Layer>) : seq<B.Layer>
  requires forall i | 0 <= i < |layers| :: P.WFNode(layers[i].readOp.node)
  ensures |layers| == |ILayers(layers)|
  ensures forall i | 0 <= i < |ILayers(layers)| :: B.WFNode(ILayers(layers)[i].readOp.node)
  {
    if |layers| == 0 then [] else
      ILayers(layers[..|layers|-1]) + [ILayer(layers[|layers|-1])]
  }

  function IQuery(q: P.LookupQuery) : B.LookupQuery
  requires P.ValidQuery(q)
  {
    B.LookupQuery(q.key, q.value, ILayers(q.lookup))
  }

  function ISuccQuery(q: P.SuccQuery) : B.SuccQuery
  requires P.ValidSuccQuery(q)
  {
    B.SuccQuery(q.start, q.results, q.end, ILayers(q.lookup))
  }

  function IInsertion(ins: P.MessageInsertion) : B.MessageInsertion
  requires P.ValidInsertion(ins)
  {
    B.MessageInsertion(ins.key, ins.msg, INode(ins.oldroot))
  }

  function MovedKeys(node: PNode, slot_idx: int) : iset<Key>
  requires WFPivots(node.pivotTable)
  {
    iset key | BoundedKey(node.pivotTable, key) && Route(node.pivotTable, key) == slot_idx
  }

  function FlushedKeys(flush: P.NodeFlush) : iset<Key>
  requires P.ValidFlush(flush)
  {
    iset key | key in flush.parent.buckets[flush.slot_idx].as_map().Keys
            && key !in flush.newparent.buckets[flush.slot_idx].as_map().Keys
  }

  function IFlush(flush: P.NodeFlush) : B.NodeFlush
  requires P.ValidFlush(flush)
  {
    B.NodeFlush(flush.parentref, INode(flush.parent), INode(flush.newparent), flush.childref, INode(flush.child), flush.newchildref, INode(flush.newchild), MovedKeys(flush.parent, flush.slot_idx), FlushedKeys(flush))
  }

  function IGrow(growth: P.RootGrowth) : B.RootGrowth
  requires P.ValidGrow(growth)
  {
    B.RootGrowth(INode(growth.oldroot), growth.newchildref)
  }

  function ISplit(split: P.NodeFusion) : B.Redirect
  requires P.InvNode(split.fused_parent)
  requires P.InvNode(split.fused_child)
  requires P.ValidSplit(split)
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(split);
    B.Redirect(
      split.parentref,
      INode(split.fused_parent),
      [split.fused_childref],
      imap[
        split.fused_childref := INode(split.fused_child)
      ],
      INode(split.split_parent),
      [split.left_childref, split.right_childref],
      imap[
        split.left_childref := INode(split.left_child),
        split.right_childref := INode(split.right_child)
      ],
      PivotTableBucketKeySet(split.fused_parent.pivotTable, split.slot_idx)
    )
  }

  function IMerge(split: P.NodeFusion) : B.Redirect
  requires P.InvNode(split.split_parent)
  requires P.InvNode(split.left_child)
  requires P.InvNode(split.right_child)
  requires P.ValidMerge(split)
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(split);
    B.Redirect(
      split.parentref,
      INode(split.split_parent),
      [split.left_childref, split.right_childref],
      imap[
        split.left_childref := INode(split.left_child),
        split.right_childref := INode(split.right_child)
      ],
      INode(split.fused_parent),
      [split.fused_childref],
      imap[
        split.fused_childref := INode(split.fused_child)
      ],
      PivotTableBucketKeySet(split.fused_parent.pivotTable, split.slot_idx)
    )
  }

  function IClone(clone: P.NodeClone) : B.Clone
  requires P.ValidClone(clone)
  {
    B.Clone(INode(clone.oldroot), INode(clone.newroot), P.CloneMap(clone.from, clone.to))
  }

  function IStep(betreeStep: P.BetreeStep) : B.BetreeStep
  requires !betreeStep.BetreeRepivot?
  requires P.ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => B.BetreeQuery(IQuery(q))
      case BetreeSuccQuery(sq) => B.BetreeSuccQuery(ISuccQuery(sq))
      case BetreeInsert(ins) => B.BetreeInsert(IInsertion(ins))
      case BetreeFlush(flush) => B.BetreeFlush(IFlush(flush))
      case BetreeGrow(growth) => B.BetreeGrow(IGrow(growth))
      case BetreeSplit(fusion) => (
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        B.BetreeRedirect(ISplit(fusion))
      )
      case BetreeMerge(fusion) => (
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        B.BetreeRedirect(IMerge(fusion))
      )
      case BetreeClone(clone) => (
        B.BetreeClone(IClone(clone))
      )
    }
  }

  lemma RefinesLookup(lookup: P.Lookup, key: Key)
  requires P.WFLookupForKey(lookup, key)
  ensures B.WFLookupForKey(ILayers(lookup), key)
  {
    if (|lookup| == 1) {
    } else {
      var lookup' := DropLast(lookup);

      forall idx | P.ValidLayerIndex(lookup' , idx) && idx < |lookup' | - 1
      ensures P.LookupFollowsChildRefAtLayer(lookup' , idx)
      ensures P.LookupFollowsChildEdgeAtLayer(lookup', idx)
      {
        assert P.LookupFollowsChildRefAtLayer(lookup, idx);
        assert P.LookupFollowsChildEdgeAtLayer(lookup, idx);
      }

      RefinesLookup(lookup', key);

      forall idx | B.ValidLayerIndex(ILayers(lookup), idx) && idx < |ILayers(lookup)| - 1
      ensures B.LookupFollowsChildRefAtLayer(ILayers(lookup), idx)
      ensures B.LookupFollowsEdgeAtLayer(ILayers(lookup), idx)
      {
        if idx < |lookup| - 2 {
          assert B.LookupFollowsChildRefAtLayer(ILayers(lookup'), idx);
          assert B.LookupFollowsEdgeAtLayer(ILayers(lookup'), idx);

          assert B.LookupFollowsChildRefAtLayer(ILayers(lookup), idx);
          assert B.LookupFollowsEdgeAtLayer(ILayers(lookup), idx);
        } else {
          assert P.LookupFollowsChildRefAtLayer(lookup, |lookup|-2);
          assert P.LookupFollowsChildEdgeAtLayer(lookup, |lookup|-2);
        }
      }
    }
  }

  lemma RefinesInterpretLookup(lookup: P.Lookup, key: Key)
  requires P.WFLookupForKey(lookup, key)
  requires Last(lookup).readOp.node.children.Some?
  ensures B.WFLookupForKey(ILayers(lookup), key)
  ensures P.LookupVisitsWellMarshalledBuckets(lookup) ==>
    B.InterpretLookup(ILayers(lookup)) == P.InterpretLookup(lookup)
  {
    RefinesLookup(lookup, key);

    if |lookup| == 1 {
      /*
      assert INode(lookup[0].node).buffer[key]
          == P.NodeLookup(lookup[0].node, key);
      assert B.InterpretLookup(IReadOps(lookup), key)
          == B.InterpretLookup([IReadOp(lookup[0])], key)
          == B.G.M.Merge(
            B.G.M.Update(B.G.M.NopDelta()),
            INode(lookup[0].node).buffer[key])
          == P.InterpretLookup(lookup, key);
      */
    } else {
      var lookup' := DropLast(lookup);

      forall idx | P.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
      ensures P.LookupFollowsChildRefAtLayer(lookup', idx)
      ensures P.LookupFollowsChildEdgeAtLayer(lookup', idx)
      {
        assert P.LookupFollowsChildRefAtLayer(lookup, idx);
        assert P.LookupFollowsChildEdgeAtLayer(lookup, idx);
      }

      assert P.LookupFollowsChildRefAtLayer(lookup, |lookup|-2);
      RefinesInterpretLookup(DropLast(lookup), key);

      if P.LookupVisitsWellMarshalledBuckets(lookup) {
        assert B.InterpretLookup(ILayers(lookup)) == P.InterpretLookup(lookup);
      }
    }
  }

  lemma RefinesInterpretLookupAccountingForLeaf(lookup: P.Lookup, key: Key, value: Value)
  requires P.WFLookupForKey(lookup, key)
  ensures B.WFLookupForKey(ILayers(lookup), key)
  ensures P.LookupVisitsWellMarshalledBuckets(lookup) ==>
      B.InterpretLookup(ILayers(lookup)) == P.InterpretLookupAccountingForLeaf(lookup)
  {
    RefinesLookup(lookup, key);

    if (Last(lookup).readOp.node.children.Some?) {
      RefinesInterpretLookup(lookup, key);
    } else {
      if |lookup| == 1 {
        if P.LookupVisitsWellMarshalledBuckets(lookup) {
          MergeIsAssociative(
              Update(NopDelta()),
              P.NodeLookup(lookup[0].readOp.node, key),
              DefineDefault());
          assert B.InterpretLookup(ILayers(lookup))
              == Merge(P.InterpretLookup(lookup), DefineDefault())
              == P.InterpretLookupAccountingForLeaf(lookup);
        }
      } else {
        var lookup' := DropLast(lookup);

        forall idx | P.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
        ensures P.LookupFollowsChildRefAtLayer(lookup', idx)
        ensures P.LookupFollowsChildEdgeAtLayer(lookup', idx)
        {
          assert P.LookupFollowsChildRefAtLayer(lookup, idx);
          assert P.LookupFollowsChildEdgeAtLayer(lookup, idx);
        }

        assert P.LookupFollowsChildRefAtLayer(lookup, |lookup|-2);
        assert P.LookupFollowsChildEdgeAtLayer(lookup, |lookup|-2);
        RefinesInterpretLookup(lookup', key);

        if P.LookupVisitsWellMarshalledBuckets(lookup) {
          MergeIsAssociative(
              B.InterpretLookup(DropLast(ILayers(lookup))),
              P.NodeLookup(Last(lookup).readOp.node, Last(lookup).currentKey),
              DefineDefault());
        }
      }
    }
  }

  lemma RefinesValidQuery(q: P.LookupQuery)
  requires P.ValidQuery(q)
  requires ReadOpsBucketsWellMarshalled(P.QueryReads(q))
  ensures B.ValidQuery(IQuery(q))
  {
    RefinesLookup(q.lookup, q.key);
    RefinesInterpretLookupAccountingForLeaf(q.lookup, q.key, q.value);
    assert P.LookupVisitsWellMarshalledBuckets(q.lookup);
  }

  lemma SameILayersReadOp(lookup: P.Lookup, lookup': P.Lookup)
  requires |lookup| == |lookup'|
  requires forall i | 0 <= i < |lookup| :: 
    && P.WFNode(lookup[i].readOp.node)
    && lookup[i].readOp == lookup'[i].readOp
  ensures forall i | 0 <= i < |lookup| ::
    && ILayers(lookup)[i].readOp == ILayers(lookup')[i].readOp 
  {
  }

  lemma InUpperBoundAndNot(a: Key, end: MS.UI.RangeEnd, b: Key)
  requires MS.UpperBound(a, end)
  requires !MS.UpperBound(b, end)
  ensures P.G.Keyspace.lt(a, b)
  {
    match end {
      case EInclusive(key) => {
        assert P.G.Keyspace.lte(a, key);
        assert P.G.Keyspace.lt(key, b);
      }
      case EExclusive(key) => {
        assert P.G.Keyspace.lt(a, key);
        assert P.G.Keyspace.lte(key, b);
      }
      case PositiveInf => { }
    }
  }

  lemma LookupUpperBoundLte(lookup: P.Lookup, tt: TranslationTable, targetidx: int, idx: int)
  requires idx <= targetidx
  requires 0 <= idx < |lookup|
  requires 1 <= targetidx < |lookup|
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires P.ValidTranslationTable(lookup, tt, 0)
  ensures 
    var upperbound := P.LookupUpperBound(lookup, idx, tt);
    var upper := P.LookupUpperBoundAtLayer(lookup[targetidx], tt[targetidx-1], lookup[0].currentKey);
    && (upperbound.None? ==> upper.None?)
    && (upper.Some? ==> upperbound.Some?)
    && (upper.Some? ==> P.G.Keyspace.lte(upperbound.value, upper.value))
  decreases |lookup| - idx
  {
    P.reveal_LookupUpperBound();
    if idx == targetidx {
    } else {
      LookupUpperBoundLte(lookup, tt, targetidx, idx + 1);
    }
  }

  lemma KeyWithinUpperBoundIsWithinLookup(key: Key, upperbound: Option<Key>, lookup: P.Lookup, tt: TranslationTable, idx: int)
  requires 0 <= idx < |lookup|
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires P.ValidTranslationTable(lookup, tt, 0)
  requires P.G.Keyspace.lte(lookup[0].currentKey, key)
  requires upperbound == P.LookupUpperBound(lookup, 0, tt)
  requires upperbound.Some? ==> P.G.Keyspace.lt(key, upperbound.value)
  ensures idx > 0 && tt[idx-1].Some? ==> IsPrefix(tt[idx-1].value.prefix, key)
  ensures var r := Route(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey);
    var currentkey := GenerateKeyAtLayer(key, tt, idx);
    && Keyspace.lt(KeyToElement(currentkey), lookup[idx].readOp.node.pivotTable[r+1])
  {
    P.reveal_LookupUpperBound();

    var pivots := lookup[idx].readOp.node.pivotTable;
    var r := Route(pivots, lookup[idx].currentKey);
    var currentkey := GenerateKeyAtLayer(key, tt, idx);
    
    if idx == 0 {
      assert key == currentkey;
      assert Keyspace.lt(KeyToElement(currentkey), pivots[r+1]);
    } else {
      LookupUpperBoundLte(lookup, tt, idx, 0);
      if tt[idx-1].Some? {
        TranslatePivotPairRangeProperty(KeyToElement(lookup[idx].currentKey),
          pivots[r+1], tt[idx-1].value.newPrefix, tt[idx-1].value.prefix);
      }
    }
  }

  function GenerateKeyAtLayer(key: Key, tt: TranslationTable, idx: int) : (k: Key)
  requires 0 <= idx <= |tt|
  {
    if idx > 0 && tt[idx-1].Some? && IsPrefix(tt[idx-1].value.prefix, key)
    then ApplyPrefixSet(tt[idx-1], key)
    else ApplyPrefixSet(None, key)
  }

  function GenerateLookup(lookup: P.Lookup, key: Key, tt: TranslationTable, idx: int) : (lookup': P.Lookup)
  requires 0 <= idx < |lookup|
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires P.ValidTranslationTable(lookup, tt, 0)
  ensures |lookup| == |lookup'| + idx
  ensures forall i | 0 <= i < |lookup'| :: 
    && lookup'[i].readOp == lookup[i+idx].readOp
    && lookup'[i].currentKey == GenerateKeyAtLayer(key, tt, i+idx)
  decreases |lookup| - idx
  {
    var currentkey := GenerateKeyAtLayer(key, tt, idx);
    if idx == |lookup|-1 then (
      [ P.Layer(lookup[idx].readOp, currentkey) ]
    ) else (
      [ P.Layer(lookup[idx].readOp, currentkey) ] +  GenerateLookup(lookup, key, tt, idx+1)
    )
  }
  
  lemma InRangeImpliesSameRoute(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd, 
    lookup: P.Lookup, tt: TranslationTable, lookup': P.Lookup, idx: int)
  requires MS.InRange(start, key, end)
  requires P.ValidLayerIndex(lookup, idx)
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires lookup[0].currentKey == if start.NegativeInf? then [] else start.key
  requires P.ValidTranslationTable(lookup, tt, 0)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  ensures idx > 0 && tt[idx-1].Some? ==> IsPrefix(tt[idx-1].value.prefix, key)
  ensures BoundedKey(lookup'[idx].readOp.node.pivotTable, lookup'[idx].currentKey)
  ensures Route(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey)
    == Route(lookup'[idx].readOp.node.pivotTable, lookup'[idx].currentKey)
  ensures P.G.Keyspace.lte(lookup[idx].currentKey, lookup'[idx].currentKey)
  ensures var r := Route(lookup[idx].readOp.node.pivotTable, lookup[idx].currentKey);
    && (BucketWellMarshalled(lookup[idx].readOp.node.buckets[r]) ==> 
        BucketWellMarshalled(lookup'[idx].readOp.node.buckets[r]))
  {
    var startKey := if start.NegativeInf? then [] else start.key;
    var pivots := lookup'[idx].readOp.node.pivotTable;
    var edges := lookup'[idx].readOp.node.edgeTable;
    var r := Route(pivots, lookup[idx].currentKey);

    var upperbound := P.LookupUpperBound(lookup, 0, tt);
    if upperbound.Some? {
      InUpperBoundAndNot(key, end, upperbound.value);
    }

    P.G.Keyspace.EmptyLte(key);
    KeyWithinUpperBoundIsWithinLookup(key, upperbound, lookup, tt, idx);
    assert idx > 0 && tt[idx-1].Some? ==> IsPrefix(tt[idx-1].value.prefix, key);

    if  idx > 0 && tt[idx-1].Some? {
      assert IsPrefix(tt[idx-1].value.prefix, key);
      assert IsPrefix(tt[idx-1].value.prefix, startKey) by { reveal_IsPrefix(); }

      assert IsPrefix(tt[idx-1].value.newPrefix, lookup'[idx].currentKey) by { reveal_IsPrefix(); }
      assert IsPrefix(tt[idx-1].value.newPrefix, lookup[idx].currentKey);

      PrefixLteProperties( tt[idx-1].value.prefix, startKey, key);
      PrefixLteProperties( tt[idx-1].value.newPrefix, lookup[idx].currentKey, lookup'[idx].currentKey);
    } else {
      assert lookup[idx].currentKey == startKey;
      assert lookup'[idx].currentKey == key;
    }
    assert P.G.Keyspace.lte(lookup[idx].currentKey, lookup'[idx].currentKey);
    RouteIs(pivots, lookup'[idx].currentKey, r);
  }

  predicate LookupConditions(lookup: P.Lookup)
  {
    && P.LookupVisitsWFNodes(lookup)
    && P.LookupBoundedKey(lookup)
    && P.LookupFollowsChildRefs(lookup)
    && P.LookupFollowsChildEdges(lookup)
  }

  lemma WFGenerateLookupIter(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd,
    lookup: P.Lookup, lookup': P.Lookup, tt: TranslationTable, idx: int)
  requires MS.InRange(start, key, end)
  requires P.ValidLayerIndex(lookup, idx)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    && P.WFLookupForKey(lookup, startKey)
  requires tt == P.LookupTranslationTable(lookup, 0, None)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires var pset := if idx == 0 then None else tt[idx-1];
    && tt[idx..] == P.LookupTranslationTable(lookup, idx, pset)
  ensures LookupConditions(lookup'[idx..])
  decreases |lookup'| - idx 
  {
    var pivots := lookup'[idx].readOp.node.pivotTable;
    var edges := lookup'[idx].readOp.node.edgeTable;
    InRangeImpliesSameRoute(start, key, end, lookup, tt, lookup', idx);

    if idx < |lookup'| - 1 {
      WFGenerateLookupIter(start, key, end, lookup, lookup', tt, idx + 1); 
      assert P.LookupFollowsChildRefs(lookup'[idx+1..]);

      forall i | P.ValidLayerIndex(lookup'[idx..], i) && i < |lookup'[idx..]| - 1 
      ensures P.LookupFollowsChildRefAtLayer(lookup'[idx..], i)
      ensures P.LookupFollowsChildEdgeAtLayer(lookup'[idx..], i)
      {
        if i == 0 {
          assert lookup'[idx..][i] == lookup'[idx];
          assert P.LookupFollowsChildRefAtLayer(lookup', idx);
          assert P.LookupFollowsChildRefAtLayer(lookup, idx);
          assert P.LookupFollowsChildRefAtLayer(lookup'[idx..], i);

          var prefix1 := if idx == 0 then None else tt[idx-1];
          var prefix2 := Translate(pivots, edges, lookup[idx].currentKey);
          var prefix3 := Translate(pivots, edges, lookup'[idx].currentKey);
          assert prefix2 == prefix3;

          InRangeImpliesSameRoute(start, key, end, lookup, tt, lookup', idx+1);
          assert tt[idx] == ComposePrefixSet(prefix1, prefix2) by {
            P.reveal_LookupTranslationTable();
          }

          ComposePrefixSetCorrect(prefix1, prefix2, tt[idx], key, 
              lookup'[idx].currentKey, lookup'[idx+1].currentKey);
          assert P.LookupFollowsChildEdgeAtLayer(lookup', idx);
        } else {
          assert lookup'[idx..][i] == lookup'[idx+1..][i-1];
          assert P.LookupFollowsChildRefAtLayer(lookup'[idx+1..], i-1);
          assert P.LookupFollowsChildRefAtLayer(lookup'[idx..], i);
          assert P.LookupFollowsChildEdgeAtLayer(lookup'[idx+1..], i-1);
          assert P.LookupFollowsChildEdgeAtLayer(lookup'[idx..], i);
        }
      }
    }
  }

  lemma GenerateLookupWellMarshalled(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd,
    lookup: P.Lookup, lookup': P.Lookup, tt: TranslationTable, idx: int)
  requires MS.InRange(start, key, end)
  requires P.ValidLayerIndex(lookup, idx)
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires lookup[0].currentKey == if start.NegativeInf? then [] else start.key
  requires P.ValidTranslationTable(lookup, tt, 0)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires P.LookupBoundedKey(lookup')
  ensures P.LookupVisitsWellMarshalledBuckets(lookup) ==> 
      P.LookupVisitsWellMarshalledBuckets(lookup'[idx..])
  decreases |lookup'| - idx
  {
    InRangeImpliesSameRoute(start, key, end, lookup, tt, lookup', idx);
    if idx < |lookup'| - 1 {
      GenerateLookupWellMarshalled(start, key, end, lookup, lookup', tt, idx+1);
    }
  }

  lemma WFGenerateLookup(start: MS.UI.RangeStart, key: Key, end: MS.UI.RangeEnd,
    lookup: P.Lookup, lookup': P.Lookup, tt: TranslationTable)
  requires MS.InRange(start, key, end)
  requires
    var startKey := if start.NegativeInf? then [] else start.key;
    && P.WFLookupForKey(lookup, startKey)
  requires tt == P.LookupTranslationTable(lookup, 0, None)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  ensures P.WFLookupForKey(lookup', key)
  ensures P.LookupVisitsWellMarshalledBuckets(lookup) ==> 
      P.LookupVisitsWellMarshalledBuckets(lookup')
  {
    WFGenerateLookupIter(start, key, end, lookup, lookup', tt, 0);
    GenerateLookupWellMarshalled(start, key, end, lookup, lookup', tt, 0);
  }
 
  function InterpretBucketStack(buckets: seq<Bucket>, key: Key) : Message
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  {
    if |buckets| == 0 then
      Update(NopDelta())
    else
      Merge(InterpretBucketStack(DropLast(buckets), key), BucketGet(Last(buckets).as_map(), key))
  }

  lemma BucketGetComposeSeq(buckets: seq<Bucket>, key: Key)
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  ensures BucketGet(ComposeSeq(MapsOfBucketList(buckets)), key) == InterpretBucketStack(buckets, key);
  {
    reveal_ComposeSeq();
    reveal_Compose();
    if |buckets| == 0 {
    } else {
      calc {
        BucketGet(ComposeSeq(MapsOfBucketList(buckets)), key);
        Merge(BucketGet(ComposeSeq(DropLast(MapsOfBucketList(buckets))), key), BucketGet(Last(MapsOfBucketList(buckets)), key));
        {
          assert DropLast(MapsOfBucketList(buckets)) == MapsOfBucketList(DropLast(buckets));
          assert Last(MapsOfBucketList(buckets)) == Last(buckets).as_map();
        }
        Merge(BucketGet(ComposeSeq(MapsOfBucketList(DropLast(buckets))), key), BucketGet(Last(buckets).as_map(), key));
        {
          BucketGetComposeSeq(DropLast(buckets), key);
        }
        Merge(InterpretBucketStack(DropLast(buckets), key), BucketGet(Last(buckets).as_map(), key));
        InterpretBucketStack(buckets, key);
      }
    }
  }

  lemma TranslatedBucketPreservesLookup(layer: P.Layer, bucket: Bucket, layer': P.Layer, bucket': Bucket, key: Key, pset: Option<PrefixSet>)
  requires P.WFNode(layer.readOp.node)
  requires layer.readOp == layer'.readOp
  requires P.G.Keyspace.lte(layer.currentKey, layer'.currentKey)
  requires BoundedKey(layer.readOp.node.pivotTable, layer.currentKey)
  requires BoundedKey(layer'.readOp.node.pivotTable, layer'.currentKey)
  requires PreWFBucket(bucket)
  requires BucketWellMarshalled(bucket)
  requires Route(layer.readOp.node.pivotTable, layer.currentKey)
    == Route(layer'.readOp.node.pivotTable, layer'.currentKey)
  requires bucket == layer.readOp.node.buckets[Route(layer.readOp.node.pivotTable, layer.currentKey)]
  requires pset.None? ==> bucket == bucket'
  requires pset.Some? ==>
    && IsPrefix(pset.value.prefix, key)
    && IsPrefix(pset.value.newPrefix, layer.currentKey)
    && bucket' == P.ClampAndTranslateBucket(layer, bucket, pset.value)
  requires layer'.currentKey == ApplyPrefixSet(pset, key)
  ensures P.NodeLookup(layer'.readOp.node, layer'.currentKey)
          == BucketGet(bucket'.as_map(), key)
  {
    var r := Route(layer'.readOp.node.pivotTable, layer'.currentKey);
    if pset.None? {
      assert layer'.readOp.node.buckets[r] == bucket';
    } else {
      var pivots := layer.readOp.node.pivotTable;
      var (left, right) := TranslatePivotPairInternal(
          KeyToElement(layer.currentKey), pivots[r+1], pset.value.newPrefix, pset.value.newPrefix);

      TranslatePivotPairRangeProperty(KeyToElement(layer.currentKey), 
        pivots[r+1], pset.value.newPrefix, pset.value.newPrefix);

      var cutleft := if right.Max_Element? then bucket else SplitBucketLeft(bucket, right.e);
      var cutright := SplitBucketRight(cutleft, layer.currentKey);

      reveal_SplitBucketLeft();
      reveal_SplitBucketRight();
      P.G.Keyspace.reveal_IsStrictlySorted();

      assert left == KeyToElement(layer.currentKey); // observe
      assert InBetween(KeyToElement(layer.currentKey), pivots[r+1], layer'.currentKey); // observe
      assert InBetween(left, right, layer'.currentKey); // observe

      assert layer'.readOp.node.buckets[r] == bucket;
      assert layer'.currentKey in cutright.keys <==> layer'.currentKey in bucket.keys;
      MapSeqs.key_sets_eq(bucket.keys, bucket.msgs);
      MapSeqs.key_sets_eq(cutright.keys, cutright.msgs);
      assert layer'.currentKey in cutright.as_map() <==> layer'.currentKey in bucket.as_map();

      if layer'.currentKey in cutright.as_map() {
        var i1 := MapSeqs.GetIndex(bucket.keys, bucket.msgs, layer'.currentKey);
        var i2 := MapSeqs.GetIndex(cutright.keys, cutright.msgs, layer'.currentKey);
        MapSeqs.MapMapsIndex(bucket.keys, bucket.msgs, i1);
        MapSeqs.MapMapsIndex(cutright.keys, cutright.msgs, i2);
        assert BucketGet(cutright.as_map(), layer'.currentKey) == BucketGet(bucket.as_map(), layer'.currentKey);
      }

      TranslateBucketSameMessage(cutright, bucket', pset.value.newPrefix, pset.value.prefix, 
        layer'.currentKey, key);

      assert BucketGet(cutright.as_map(), layer'.currentKey) == BucketGet(bucket.as_map(), layer'.currentKey);
      assert BucketGet(cutright.as_map(), layer'.currentKey) == BucketGet(bucket'.as_map(), key);
    }
  }

  lemma InterpretBucketStackEqInterpretLookupIter(start: MS.UI.RangeStart, key: Key,
    end: MS.UI.RangeEnd, lookup: P.Lookup, buckets: seq<Bucket>, lookup': P.Lookup,
    buckets': seq<Bucket>, tt: TranslationTable, idx: int)
  requires 1 <= idx <= |lookup| == |buckets|
  requires MS.InRange(start, key, end)
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires lookup[0].currentKey == if start.NegativeInf? then [] else start.key
  requires P.ValidTranslationTable(lookup, tt, 0)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires P.LookupVisitsWFNodes(lookup')
  requires P.LookupBoundedKey(lookup')
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |lookup| :: buckets[i] 
    == lookup[i].readOp.node.buckets[Route(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)]
  requires buckets' == P.TranslateSuccBuckets(lookup, buckets, tt, 0)
  ensures InterpretBucketStack(buckets'[..idx], key)
       == P.InterpretLookup(lookup'[..idx])
  {
    assert |buckets| == |buckets'|;
    assert |lookup| == |lookup'|;

    InRangeImpliesSameRoute(start, key, end, lookup, tt, lookup', idx-1);

    if idx == 1 {
      assert key == lookup'[0].currentKey;
      assert InterpretBucketStack(buckets'[..idx], key) == P.InterpretLookup(lookup'[..idx]);
    } else {
      TranslatedBucketPreservesLookup(lookup[idx-1], buckets[idx-1], lookup'[idx-1], buckets'[idx-1], key, tt[idx-2]);
      assert P.NodeLookup(lookup'[idx-1].readOp.node, lookup'[idx-1].currentKey) == BucketGet(buckets'[idx-1].as_map(), key);
      InterpretBucketStackEqInterpretLookupIter(start, key, end, lookup, buckets, lookup', buckets', tt, idx-1);
      assert InterpretBucketStack(buckets'[..idx-1], key) == P.InterpretLookup(lookup'[..idx-1]);

      assert DropLast(buckets'[..idx]) == buckets'[..idx-1];
      assert DropLast(lookup'[..idx]) == lookup'[..idx-1];
      assert InterpretBucketStack(buckets'[..idx], key) == P.InterpretLookup(lookup'[..idx]);
    }
  }

  lemma InterpretBucketStackEqInterpretLookup(start: MS.UI.RangeStart, key: Key,
    end: MS.UI.RangeEnd, lookup: P.Lookup, buckets: seq<Bucket>, lookup': P.Lookup,
    buckets': seq<Bucket>, tt: TranslationTable)
  requires MS.InRange(start, key, end)
  requires 0 < |lookup| == |buckets|
  requires P.LookupVisitsWFNodes(lookup)
  requires P.LookupBoundedKey(lookup)
  requires lookup[0].currentKey == if start.NegativeInf? then [] else start.key
  requires P.ValidTranslationTable(lookup, tt, 0)
  requires lookup' == GenerateLookup(lookup, key, tt, 0)
  requires P.LookupVisitsWFNodes(lookup')
  requires P.LookupBoundedKey(lookup')
  requires
    var lookupUpperBound := P.LookupUpperBound(lookup, 0, tt);
    && (lookupUpperBound.Some? ==> !MS.UpperBound(lookupUpperBound.value, end))
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |lookup| :: buckets[i] 
    == lookup[i].readOp.node.buckets[Route(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)]
  requires buckets' == P.TranslateSuccBuckets(lookup, buckets, tt, 0)
  ensures InterpretBucketStack(buckets', key)
       == P.InterpretLookup(lookup')
  {
    InterpretBucketStackEqInterpretLookupIter(start, key, end, lookup, buckets, lookup', buckets', tt, |buckets|);
    assert buckets'[..|buckets'|] == buckets';
    assert lookup'[..|buckets'|] == lookup';
  }

  lemma SuccQueryProperties(results: seq<UI.SuccResult>, buckets: seq<Bucket>,
      start: UI.RangeStart, end: UI.RangeEnd)
  requires BucketListWellMarshalled(buckets)
  requires forall i | 0 <= i < |buckets| :: PreWFBucket(buckets[i])
  requires results ==
        SortedSeqOfKeyValueMap(
          KeyValueMapOfBucket(
            ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)))
  ensures (forall i | 0 <= i < |results| ::
      P.BufferDefinesValue(InterpretBucketStack(buckets, results[i].key), results[i].value))
  ensures (forall i | 0 <= i < |results| :: results[i].value != MS.EmptyValue())
  ensures (forall i | 0 <= i < |results| :: MS.InRange(start, results[i].key, end))
  ensures (forall i, j | 0 <= i < j < |results| :: P.G.Keyspace.lt(results[i].key, results[j].key))
  ensures (forall key | MS.InRange(start, key, end) ::
        (forall i | 0 <= i < |results| :: results[i].key != key) ==>
        P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key))
      )
  {
    forall i | 0 <= i < |results|
    ensures P.BufferDefinesValue(InterpretBucketStack(buckets, results[i].key), results[i].value)
    ensures results[i].value != MS.EmptyValue()
    ensures MS.InRange(start, results[i].key, end)
    {
      SortedSeqOfKeyValueMaps(KeyValueMapOfBucket(ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)), i);
      reveal_KeyValueMapOfBucket();
      reveal_ClampRange();

      //var m := ComposeSeq(buckets)[results[i].key];
      //assert Merge(m, M.DefineDefault()).value == results[i].value;
      BucketGetComposeSeq(buckets, results[i].key);
      //assert m == InterpretBucketStack(buckets, results[i].key);
    }

    SortedSeqOfKeyValueMapHasSortedKeys(KeyValueMapOfBucket(
            ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)));

    forall key | MS.InRange(start, key, end) &&
        (forall i | 0 <= i < |results| :: results[i].key != key)
    ensures
      P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key))
    {
      if !P.BufferDefinesEmptyValue(InterpretBucketStack(buckets, key)) {
        reveal_KeyValueMapOfBucket();
        reveal_ClampRange();

        BucketGetComposeSeq(buckets, key);
        //assert BucketGet(ComposeSeq(buckets), key) == InterpretBucketStack(buckets, key);
        //assert key in KeyValueMapOfBucket(ClampRange(ComposeSeq(buckets), start, end));
        SortedSeqOfKeyValueHasKey(KeyValueMapOfBucket(ClampRange(ComposeSeq(MapsOfBucketList(buckets)), start, end)), key);
      }
    }
  }

  lemma RefinesValidSuccQuery(sq: P.SuccQuery)
  requires P.ValidSuccQuery(sq)
  requires ReadOpsBucketsWellMarshalled(P.SuccQueryReads(sq))
  ensures B.ValidSuccQuery(ISuccQuery(sq))
  {
    var q := ISuccQuery(sq);
    var startKey := if sq.start.NegativeInf? then [] else sq.start.key;
    var translatedbuckets := P.TranslateSuccBuckets(sq.lookup, sq.buckets, sq.translations, 0);
    SuccQueryProperties(sq.results, translatedbuckets, sq.start, sq.end);

    forall i | 0 <= i < |q.results|
    ensures (exists lookup :: B.SamePathWithKeyValue(q.lookup, lookup, q.results[i].key, q.results[i].value))
    {
      var lookup' := GenerateLookup(sq.lookup, sq.results[i].key, sq.translations, 0);
      WFGenerateLookup(sq.start, sq.results[i].key, sq.end, sq.lookup, lookup', sq.translations);
      SameILayersReadOp(sq.lookup, lookup');

      RefinesLookup(lookup', sq.results[i].key);
      RefinesInterpretLookupAccountingForLeaf(lookup', sq.results[i].key, sq.results[i].value);

      InterpretBucketStackEqInterpretLookup(sq.start, sq.results[i].key, sq.end, sq.lookup, sq.buckets, lookup', translatedbuckets, sq.translations);
      assert B.InterpretLookup(ILayers(lookup')) == P.InterpretLookup(lookup');
      assert B.SamePathWithKeyValue(q.lookup, ILayers(lookup'), q.results[i].key, q.results[i].value);
    }

    assert (forall r | r in q.results :: (exists lookup :: B.SamePathWithKeyValue(q.lookup, lookup, r.key, r.value)));

    forall key | MS.InRange(q.start, key, q.end)
        && (forall i | 0 <= i < |q.results| :: q.results[i].key != key)
    ensures (exists lookup :: B.SamePathWithKeyValue(q.lookup, lookup, key, MS.EmptyValue()))
    {
      var lookup' := GenerateLookup(sq.lookup, key, sq.translations, 0);
      WFGenerateLookup(sq.start, key, sq.end, sq.lookup, lookup', sq.translations);
      SameILayersReadOp(sq.lookup, lookup');

      RefinesLookup(lookup', key);
      RefinesInterpretLookupAccountingForLeaf(lookup', key, MS.EmptyValue());

      /*assert B.InterpretLookup(IReadOps(sq.lookup), key).value
          == P.InterpretLookupAccountingForLeaf(sq.lookup, key).value
          == MS.EmptyValue();*/
      
      InterpretBucketStackEqInterpretLookup(sq.start, key, sq.end, sq.lookup, sq.buckets, lookup', translatedbuckets, sq.translations);
      assert InterpretBucketStack(translatedbuckets, key) == P.InterpretLookup(lookup');
      assert P.BufferDefinesEmptyValue(P.InterpretLookup(lookup'));
      assert B.LookupKeyValue(ILayers(lookup'), key, MS.EmptyValue());
      assert B.SamePathWithKeyValue(q.lookup, ILayers(lookup'), key, MS.EmptyValue());
    }
  }

  lemma RefinesValidInsertion(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires ReadOpsBucketsWellMarshalled(P.InsertionReads(ins))
  ensures B.ValidInsertion(IInsertion(ins))
  {
  }

  lemma RefinesValidFlushNewParent(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires P.InvNode(flush.parent)
  requires P.InvNode(flush.child)
  requires (forall key | key in IFlush(flush).flushedkeys :: key in IFlush(flush).parent.children)
  ensures B.ValidFlushNewParent(IFlush(flush))
  {
    var f := IFlush(flush);

    var child' := P.RestrictAndTranslateChild(flush.parent, flush.child, flush.slot_idx);
    PivotBetreeSpecWFNodes.RestrictAndTranslateWFProperWellMarshalled(flush.parent, flush.child, flush.slot_idx);
    assert child'.pivotTable[0] == flush.parent.pivotTable[flush.slot_idx];
    assert Last(child'.pivotTable) == flush.parent.pivotTable[flush.slot_idx+1];

    var flushedKeys := BucketFlushModel.partialFlushCorrect(
      flush.parent.buckets[flush.slot_idx], child'.pivotTable, child'.buckets);
    reveal_BucketIntersect();
    reveal_BucketComplement();
  }

  lemma ValidFlushNewChildChildren(flush: P.NodeFlush, f: B.NodeFlush)
  requires P.ValidFlush(flush)
  requires P.InvNode(flush.parent)
  requires P.InvNode(flush.child)
  requires P.InvNode(flush.newchild)
  requires f == IFlush(flush)
  requires (forall key | key in f.movedkeys :: key in f.parent.children)
  ensures IChildren(flush.newchild) ==
     (imap k | k in f.movedkeys && f.parent.children[k].edgeKey in f.child.children :: 
        f.child.children[f.parent.children[k].edgeKey])
  {
    if flush.child.children.Some? {
      var child' := P.RestrictAndTranslateChild(flush.parent, flush.child, flush.slot_idx);
      assert child'.pivotTable[0] == flush.parent.pivotTable[flush.slot_idx];
      assert Last(child'.pivotTable) == flush.parent.pivotTable[flush.slot_idx+1];

      forall k | k !in f.movedkeys || f.parent.children[k].edgeKey !in f.child.children
      ensures k !in IChildren(child')
      {
        if k !in f.movedkeys {
          assert k !in IChildren(child');
       } else if f.parent.children[k].edgeKey !in f.child.children {
          RestrictAndTranslateKeyConsistency(flush.parent, flush.child, child', flush.slot_idx, k);
          assert k !in IChildren(child');
        }
      }

      forall k | k in f.movedkeys && f.parent.children[k].edgeKey in f.child.children
      ensures k in IChildren(child')
      ensures IChildren(child')[k] == f.child.children[f.parent.children[k].edgeKey]
      {
        RestrictAndTranslateKeyConsistency(flush.parent, flush.child, child', flush.slot_idx, k);
        assert k in IChildren(child');
      }
    }
  }

  lemma RefinesValidFlushNewChild(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires P.InvNode(flush.parent)
  requires P.InvNode(flush.child)
  requires P.InvNode(flush.newchild)
  requires (forall key | key in IFlush(flush).movedkeys :: key in IFlush(flush).parent.children)
  ensures B.ValidFlushNewChild(IFlush(flush))
  {
    var f := IFlush(flush);

    var child' := P.RestrictAndTranslateChild(flush.parent, flush.child, flush.slot_idx);
    PivotBetreeSpecWFNodes.RestrictAndTranslateWFProperWellMarshalled(flush.parent, flush.child, flush.slot_idx);
    assert child'.pivotTable[0] == flush.parent.pivotTable[flush.slot_idx];
    assert Last(child'.pivotTable) == flush.parent.pivotTable[flush.slot_idx+1];

    ValidFlushNewChildChildren(flush, f);

    var tmpbuffer := imap k | k in f.movedkeys :: f.child.buffer[f.parent.children[k].edgeKey];
    var newbuffer := imap k | k in f.movedkeys :: if k in f.flushedkeys then Merge(f.parent.buffer[k], tmpbuffer[k]) else tmpbuffer[k];
    
    forall k | k in f.movedkeys 
    ensures IBuffer(child')[k] == tmpbuffer[k]
    {
      RestrictAndTranslateKeyConsistency(flush.parent, flush.child, child', flush.slot_idx, k);
    }

    var flushedKeys := BucketFlushModel.partialFlushCorrect(
      flush.parent.buckets[flush.slot_idx], child'.pivotTable, child'.buckets);

    reveal_BucketComplement();
    reveal_BucketIntersect();

    var isec := BucketIntersect(flush.parent.buckets[flush.slot_idx].as_map(), flushedKeys);

    forall k | k in f.movedkeys
    ensures IMapsAgreeOnKey(f.newchild.buffer, newbuffer, k)
    {
      AddMessagesToNodeResult(child', isec, flush.newchild, k);
      if k in isec {
        if (flush.newchild.children.None?) {
           MergeIsAssociative(BucketGet(isec, k), IBuffer(child')[k], DefineDefault());
        }
      } else {
        assert newbuffer[k] == IBuffer(child')[k];
        assert k !in f.flushedkeys; // observe
        assert IBuffer(child')[k] == f.newchild.buffer[k];
      }
    }
  }

  lemma AddMessagesToNodeResult(node: PNode, bucket: BucketMap, node': PNode, key: Key)
  requires WFPivots(node.pivotTable)
  requires P.WFNode(node')
  requires WFBucketListProper(node.buckets, node.pivotTable)
  requires BucketListWellMarshalled(node.buckets)
  requires WFBucketListProper(node'.buckets, node'.pivotTable);
  requires BoundedKey(node.pivotTable, key)
  requires BoundedKey(node'.pivotTable, key)
  requires node'.pivotTable == node.pivotTable
  requires node'.children == node.children
  requires |node'.buckets| == |node.buckets|
  requires forall i | 0 <= i < |node.buckets| ::
      node'.buckets[i].as_map() == BucketListItemFlush(bucket, node.buckets[i].as_map(), node.pivotTable, i)
  ensures WFBucketListProper(node'.buckets, node'.pivotTable);
  ensures key !in bucket ==> IBuffer(node')[key] == IBuffer(node)[key]
  ensures key in bucket ==> IBuffer(node')[key] == Merge(bucket[key], IBuffer(node)[key])
  {
    var i := Route(node.pivotTable, key);
    assert node'.buckets[i].as_map() == 
        BucketListItemFlush(bucket, node.buckets[i].as_map(), node.pivotTable, i);
  }

  lemma RefinesValidFlush(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires forall i | 0 <= i < |P.FlushReads(flush)| :: P.InvNode(P.FlushReads(flush)[i].node)
  requires ReadOpsBucketsWellMarshalled(P.FlushReads(flush))
  ensures B.ValidFlush(IFlush(flush))
  {
    PivotBetreeSpecWFNodes.ValidFlushWritesInvNodes(flush);
    var f := IFlush(flush);

    assert P.InvNode(P.FlushReads(flush)[0].node);
    assert P.InvNode(P.FlushReads(flush)[1].node);

    forall key | key in flush.parent.buckets[flush.slot_idx].as_map().Keys
    ensures BoundedKey(flush.parent.pivotTable, key)
    ensures Route(flush.parent.pivotTable, key) == flush.slot_idx
    {
      assert WFBucketAt(
        flush.parent.buckets[flush.slot_idx],
        flush.parent.pivotTable,
        flush.slot_idx);
      PivotBetreeSpecWFNodes.bucket_keys_in_seq(
          flush.parent.buckets[flush.slot_idx]);
    }

    RefinesValidFlushNewParent(flush);
    RefinesValidFlushNewChild(flush);
  }

  lemma RefinesValidGrow(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires ReadOpsBucketsWellMarshalled(P.GrowReads(growth))
  ensures B.ValidGrow(IGrow(growth))
  {
  }

  lemma CutoffNodeAndKeepLeftAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires ValidLeftCutOffKey(node.pivotTable, pivot)
  requires BoundedKey(node.pivotTable, key) && P.G.Keyspace.lt(key, pivot)
  requires node' == P.CutoffNodeAndKeepLeft(node, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketLeft();
    P.reveal_CutoffNodeAndKeepLeft();
    var i := Route(node'.pivotTable, key);

    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    assert node.pivotTable[i] == node'.pivotTable[i];
    assert Keyspace.lt(KeyToElement(key), node'.pivotTable[i+1]);
    assert Keyspace.lt(KeyToElement(key), node.pivotTable[i+1]);
    RouteIs(node.pivotTable, key, i);
    PivotBetreeSpecWFNodes.SplitMaps(node.buckets[cLeft], pivot);
    assert MapsAgreeOnKey(node.buckets[i].as_map(), node'.buckets[i].as_map(), key);
  }

  lemma CutoffNodeAndKeepRightAgree(node: PNode, node': PNode, pivot: Key, key: Key)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires BucketListWellMarshalled(node.buckets)
  requires BoundedKey(node.pivotTable, pivot)
  requires BoundedKey(node.pivotTable, key) && P.G.Keyspace.lte(pivot, key)
  requires node' == P.CutoffNodeAndKeepRight(node, pivot);
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    reveal_SplitBucketRight();
    P.reveal_CutoffNodeAndKeepRight();
    var i := Route(node'.pivotTable, key);
    RouteIs(node.pivotTable, key, i + |node.pivotTable| - |node'.pivotTable|);
    var cRight := CutoffForRight(node.pivotTable, pivot);
    PivotBetreeSpecWFNodes.SplitMaps(node.buckets[cRight], pivot);
  }

  lemma CutoffNodeAgree(node: PNode, node': PNode, l: Key, r: Option<Key>, key: Key)
  requires P.InvNode(node)
  requires P.WFNode(node')
  requires P.ValidSplitKey(node, l, r)
  requires node' == P.CutoffNode(node, l, r)
  requires P.G.Keyspace.lte(l, key)
  requires r.Some? ==> P.G.Keyspace.lt(key, r.value)
  ensures IBuffer(node)[key] == IBuffer(node')[key]
  ensures IMapsAgreeOnKey(IChildren(node), IChildren(node'), key)
  {
    P.reveal_CutoffNode();
    if (r.Some?) {
      var node1 := P.CutoffNodeAndKeepLeft(node, r.value);
      CutoffNodeAndKeepLeftAgree(node, node1, r.value, key);
      PivotBetreeSpecWFNodes.KeepLeftWFProperWellMarshalled(node, r.value);
      CutoffNodeAndKeepRightAgree(node1, node', l, key);
    } else {
      CutoffNodeAndKeepRightAgree(node, node', l, key);
    }
  }

  lemma WriteFusedChildInTermsOfLeftAndRight(l: PNode, r: PNode, child: PNode, pivot: Key, num_children_left: int)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires WFPivots(child.pivotTable)
  requires WFEdges(child.edgeTable, child.pivotTable)
  requires |child.buckets| == NumBuckets(child.pivotTable)
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 1 <= num_children_left < |child.buckets|
  requires l == P.SplitChildLeft(child, num_children_left)
  requires r == P.SplitChildRight(child, num_children_left)
  requires child.pivotTable[num_children_left].e == pivot
  ensures child == P.FusedChild(l, r, pivot)
  {
    reveal_concat3();
    assert child.pivotTable == concat3(l.pivotTable[..|l.pivotTable|-1], KeyToElement(pivot), r.pivotTable[1..]);
    if (child.children.Some?) {
      assert child.children.value == child.children.value[..num_children_left] + child.children.value[num_children_left..];
      assert child.children == if l.children.Some? then Some(l.children.value + r.children.value) else None;
    } else {
      assert child.children == if l.children.Some? then Some(l.children.value + r.children.value) else None;
    }
    assert child.buckets == l.buckets + r.buckets;
  }

  lemma MergedNodeAndLeftAgree(l: PNode, r: PNode, node: PNode, pivot: Key, key: Key)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires WFPivots(node.pivotTable)
  requires WFEdges(node.edgeTable, node.pivotTable)
  requires NumBuckets(node.pivotTable) == |node.buckets|
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires BoundedKey(l.pivotTable, key) && P.G.Keyspace.lt(key, pivot)
  requires l.children.Some? <==> r.children.Some?
  requires Last(l.pivotTable) == r.pivotTable[0] == KeyToElement(pivot)
  requires node == P.FusedChild(l, r, pivot)
  ensures IBuffer(l)[key] == IBuffer(node)[key]
  ensures IMapsAgreeOnKey(IChildren(l), IChildren(node), key)
  {
    var i := Route(l.pivotTable, key);
    RouteIs(node.pivotTable, key, i);
    WFConcatEdges(l.pivotTable, l.edgeTable, r.pivotTable, r.edgeTable, node.pivotTable);
  }

  lemma MergedNodeAndRightAgree(l: PNode, r: PNode, node: PNode, pivot: Key, key: Key)
  requires P.WFNode(l)
  requires P.WFNode(r)
  requires WFPivots(node.pivotTable)
  requires WFEdges(node.edgeTable, node.pivotTable)
  requires NumBuckets(node.pivotTable) == |node.buckets|
  requires (node.children.Some? ==> |node.buckets| == |node.children.value|)
  requires BoundedKey(r.pivotTable, key) && P.G.Keyspace.lte(pivot, key)
  requires Last(l.pivotTable) == r.pivotTable[0] == KeyToElement(pivot)
  requires l.children.Some? <==> r.children.Some?
  requires node == P.FusedChild(l, r, pivot)
  ensures IBuffer(r)[key] == IBuffer(node)[key]
  ensures IMapsAgreeOnKey(IChildren(r), IChildren(node), key)
  {
    var i := Route(r.pivotTable, key);
    if i > 0 {
      assert node.pivotTable[i+|l.buckets|] == r.pivotTable[i];
    }
    assert node.pivotTable[i+|l.buckets|+1] == r.pivotTable[i+1];
    RouteIs(node.pivotTable, key, i + |l.buckets|);
    WFConcatEdges(l.pivotTable, l.edgeTable, r.pivotTable, r.edgeTable, node.pivotTable);
  }

  lemma SplitMergeBuffersChildrenEq(node: PNode, node': PNode, idx: int)
  requires P.WFNode(node)
  requires P.WFNode(node')
  requires node.children.Some?
  requires node'.children.Some?
  requires BucketListWellMarshalled(node.buckets)
  requires 0 <= idx < |node.buckets|
  requires |node'.buckets| == |node.buckets| + 1
  requires node'.buckets[idx] == SplitBucketLeft(node.buckets[idx], GetKey(node'.pivotTable, idx+1))
  requires node'.buckets[idx+1] == SplitBucketRight(node.buckets[idx], GetKey(node'.pivotTable, idx+1))
  requires forall i | 0 <= i < idx :: 
    && node.buckets[i] == node'.buckets[i]
    && node.edgeTable[i] == node'.edgeTable[i]
    && node.children.value[i] == node'.children.value[i]
  requires forall i | idx + 2 <= i < |node'.buckets| :: 
    && node.buckets[i-1] == node'.buckets[i]
    && node.edgeTable[i-1] == node'.edgeTable[i]
    && node.children.value[i-1] == node'.children.value[i]
  requires forall i | 0 <= i <= idx :: node.pivotTable[i] == node'.pivotTable[i]
  requires forall i | idx+1 < i < |node'.pivotTable| :: node'.pivotTable[i] == node.pivotTable[i-1]
  requires forall key :: BoundedKey(node.pivotTable, key) <==> BoundedKey(node'.pivotTable, key)
  ensures IBuffer(node) == IBuffer(node')
  ensures forall key:Key | key !in PivotTableBucketKeySet(node.pivotTable, idx) && BoundedKey(node.pivotTable, key) ::
      IChildren(node)[key] == IChildren(node')[key]
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();

    forall key:Key | BoundedKey(node.pivotTable, key)
    ensures IBuffer(node)[key] == IBuffer(node')[key]
    ensures key !in PivotTableBucketKeySet(node.pivotTable, idx) ==> IChildren(node)[key] == IChildren(node')[key]
    {
      var i := Route(node'.pivotTable, key);
      if (i < idx) {
        RouteIs(node.pivotTable, key, i);
        assert node'.buckets[i] == node.buckets[i];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      } else if (i == idx || i == idx+1) {
        assert node'.pivotTable[idx+2] == node.pivotTable[idx+1];
        RouteIs(node.pivotTable, key, idx);
        assert IBuffer(node)[key] == IBuffer(node')[key] by {
          PivotBetreeSpecWFNodes.SplitMaps(node.buckets[idx], GetKey(node'.pivotTable, idx+1));
        }
        assert key in PivotTableBucketKeySet(node.pivotTable, idx);
      } else {
        assert node.pivotTable[i-1] == node'.pivotTable[i];
        assert node.pivotTable[i] == node'.pivotTable[i+1];
        RouteIs(node.pivotTable, key, i-1);
        assert node'.buckets[i] == node.buckets[i-1];
        assert IBuffer(node)[key] == IBuffer(node')[key];
        assert IChildren(node)[key] == IChildren(node')[key];
      }
    }
  }

  lemma RestrictAndTranslateKeyConsistency(parent: PNode, child: PNode, child': PNode, slot: int, key: Key)
  requires P.InvNode(parent)
  requires P.InvNode(child)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  requires P.ParentKeysInChildRange(parent, child, slot)
  requires BoundedKey(parent.pivotTable, key) && Route(parent.pivotTable, key) == slot
  requires child' == P.RestrictAndTranslateChild(parent, child, slot)
  ensures BoundedKey(child'.pivotTable, key)
  ensures var edgekey := TranslateKey(parent.pivotTable, parent.edgeTable, key);
    && IBuffer(child')[key] == IBuffer(child)[edgekey]
    && (key in IChildren(child') <==> edgekey in IChildren(child))
    && (key in IChildren(child') ==> IChildren(child')[key] == IChildren(child)[edgekey])
  {
    if parent.edgeTable[slot].None? {
      var lbound := P.getlbound(parent, slot);
      var ubound := P.getubound(parent, slot);

      ContainsRangeImpliesBoundedKey(child.pivotTable, parent.pivotTable[slot], parent.pivotTable[slot+1]);
      CutoffNodeAgree(child, child', lbound, ubound, key);
    } else {
      var (lbound, ubound) := TranslatePivotPair(parent.pivotTable, parent.edgeTable, slot);
      var lboundkey : Key := lbound.e;
      var uboundkey := if ubound.Element? then (var k: Key := ubound.e; Some(k)) else None;
      var tmpchild := P.CutoffNode(child, lboundkey, uboundkey);

      var parentprefix := PivotLcp(parent.pivotTable[slot], parent.pivotTable[slot+1]);
      var childprefix := parent.edgeTable[slot].value;
      var edgekey := TranslateKey(parent.pivotTable, parent.edgeTable, key);

      TranslatePivotPairRangeProperty(parent.pivotTable[slot], parent.pivotTable[slot+1], parentprefix, childprefix);
      CutoffNodeAgree(child, tmpchild, lboundkey, uboundkey, edgekey);
      PivotBetreeSpecWFNodes.CutoffNodeWFProperWellMarshalled(child, lboundkey, uboundkey);

      assert child'.pivotTable[0] == parent.pivotTable[slot];
      assert Last(child'.pivotTable) == parent.pivotTable[slot+1]; // observe
      TranslatePivotsSameRoute(tmpchild.pivotTable,child'.pivotTable, childprefix, parentprefix, edgekey, key);
      TranslatePivotsEdgesPreserveTranslateKey(tmpchild.pivotTable, tmpchild.edgeTable, child'.pivotTable,
        child'.edgeTable, childprefix, parentprefix, parent.pivotTable[slot+1], edgekey, key);
      
      var i := Route(tmpchild.pivotTable, edgekey);
      assert WFBucketAt(tmpchild.buckets[i], tmpchild.pivotTable, i);
      assert tmpchild.pivotTable[0] == lbound;
      assert Last(tmpchild.pivotTable) == ubound;
      BucketKeysHasPrefix(tmpchild.buckets[i], tmpchild.pivotTable, i,  childprefix);
      TranslateBucketSameMessage(tmpchild.buckets[i], child'.buckets[i], childprefix, parentprefix, edgekey, key);
    }
  }

  lemma MergeRefinesWFRedirect(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  ensures B.WFRedirect(IMerge(f))
  {
    var r := IMerge(f);
    var old_parent_children_ref := imap k | k in r.old_parent.children :: r.old_parent.children[k].ref;

    forall ref | ref in r.old_childrefs
    ensures ref in IMapRestrict(old_parent_children_ref, r.keys).Values
    {
      assert ref == f.left_childref || ref == f.right_childref;
      if (ref == f.left_childref) {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in r.keys;
        assert key in IMapRestrict(r.old_parent.children, r.keys);
        assert IMapRestrict(old_parent_children_ref, r.keys)[key] == ref;
        assert ref in IMapRestrict(old_parent_children_ref, r.keys).Values;
      } else {
        var key := GetKeyInBucket(f.split_parent.pivotTable, f.slot_idx + 1);
        RouteIs(f.fused_parent.pivotTable, key, f.slot_idx);
        assert key in r.keys;
        assert key in IMapRestrict(r.old_parent.children, r.keys);
        assert IMapRestrict(old_parent_children_ref, r.keys)[key] == ref;
        assert ref in IMapRestrict(old_parent_children_ref, r.keys).Values;
      }
    }

    forall ref | ref in IMapRestrict(old_parent_children_ref, r.keys).Values
    ensures ref in r.old_childrefs
    {
      // var key: Key :| IMapsTo(IMapRestrict(old_parent_children_ref, r.keys), key, ref);
      // assert key in r.keys;
      // if (P.G.Keyspace.lt(key, f.pivot)) {
      //   RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
      //   assert ref == f.left_childref;
      // } else {
      //   assert f.split_parent.pivotTable[f.slot_idx + 2] == f.fused_parent.pivotTable[f.slot_idx + 1];
      //   RouteIs(f.split_parent.pivotTable, key, f.slot_idx+1);
      //   assert ref == f.right_childref;
      // }
    }

    assert forall k | k in r.keys :: Keyspace.lt(KeyToElement(k), f.fused_parent.pivotTable[f.slot_idx+1]);
    assert B.WFRedirect(r);
  }

  lemma MergeRefinesRedirectNewParent(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires B.WFRedirect(IMerge(f))
  ensures B.ValidRedirectNewParent(IMerge(f))
  {
    reveal_MergeBucketsInList();
    SplitOfMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);
  }

  lemma MergeRefinesRedirectNewChildren(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires B.WFRedirect(IMerge(f))
  requires B.ValidRedirectNewParent(IMerge(f))
  ensures B.ValidRedirectNewChildren(IMerge(f))
  {
    var r := IMerge(f);

    var left := P.RestrictAndTranslateChild(f.split_parent, f.left_child, f.slot_idx);
    assert left.pivotTable[0] == f.split_parent.pivotTable[f.slot_idx];
    assert Last(left.pivotTable) == f.split_parent.pivotTable[f.slot_idx+1];

    var right := P.RestrictAndTranslateChild(f.split_parent, f.right_child, f.slot_idx+1);
    assert right.pivotTable[0] == f.split_parent.pivotTable[f.slot_idx+1];
    assert Last(right.pivotTable) == f.split_parent.pivotTable[f.slot_idx+2];

    forall key:Key | key in r.keys 
    ensures r.old_parent.children[key].ref in r.old_children
      && var newchild := r.new_children[r.new_parent.children[key].ref];
      && var oldchild := r.old_children[r.old_parent.children[key].ref];
      && var edgekey := r.old_parent.children[key].edgeKey; // translated key
      && newchild.buffer[key] == oldchild.buffer[edgekey]
      && ((key in newchild.children) <==> (edgekey in oldchild.children))
      && ((key in newchild.children) ==> newchild.children[key] == oldchild.children[edgekey])
    {
      var edgekey := r.old_parent.children[key].edgeKey;
      assert BoundedKey(f.split_parent.pivotTable, key);

      if (P.G.Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert 0 <= f.slot_idx < NumBuckets(f.split_parent.pivotTable); // observe
        RestrictAndTranslateKeyConsistency(f.split_parent, f.left_child, left, f.slot_idx, key);
        assert BoundedKey(left.pivotTable, key); // observe
        MergedNodeAndLeftAgree(left, right, f.fused_child, f.pivot, key);
      } else {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx + 1);
        assert 0 <= f.slot_idx+1 < NumBuckets(f.split_parent.pivotTable); // observe
        RestrictAndTranslateKeyConsistency(f.split_parent, f.right_child, right, f.slot_idx+1, key);
        assert BoundedKey(right.pivotTable, key); // observe
        MergedNodeAndRightAgree(left, right, f.fused_child, f.pivot, key);
      }
    }
  }

  lemma MergeRefinesRedirectNewGrandChildren(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires B.WFRedirect(IMerge(f))
  requires B.ValidRedirectNewParent(IMerge(f))
  requires B.ValidRedirectNewChildren(IMerge(f))
  ensures B.ValidRedirectNewGrandchildren(IMerge(f))
  {
    var r := IMerge(f);

    var left := P.RestrictAndTranslateChild(f.split_parent, f.left_child, f.slot_idx);
    assert left.pivotTable[0] == f.split_parent.pivotTable[f.slot_idx];
    assert Last(left.pivotTable) == f.split_parent.pivotTable[f.slot_idx+1];

    var right := P.RestrictAndTranslateChild(f.split_parent, f.right_child, f.slot_idx+1);
    assert right.pivotTable[0] == f.split_parent.pivotTable[f.slot_idx+1];
    assert Last(right.pivotTable) == f.split_parent.pivotTable[f.slot_idx+2];

    assert f.fused_parent.pivotTable[f.slot_idx] == f.split_parent.pivotTable[f.slot_idx];
    assert f.fused_parent.pivotTable[f.slot_idx+1] == f.split_parent.pivotTable[f.slot_idx+2];
    assert f.fused_parent.pivotTable[f.slot_idx] == f.fused_child.pivotTable[0];
    assert f.fused_parent.pivotTable[f.slot_idx+1] == Last(f.fused_child.pivotTable);
    assert left.pivotTable[0] == f.fused_child.pivotTable[0];
    assert Last(right.pivotTable) == Last(f.fused_child.pivotTable);
    
    assert Keyspace.lte(f.fused_parent.pivotTable[f.slot_idx], f.fused_child.pivotTable[0]);
    assert Keyspace.lte(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx+1]);

    forall edge | edge in IChildren(f.fused_child).Values
    ensures exists key :: B.ValidRedirectNewGrandchildrenCheckKey(r, key, f.fused_childref, edge.ref)
    {
      var _ := MergeRouteNewChild(f, r, f.fused_childref, edge);
    }

    assert B.ValidRedirectNewGrandchildren(r) by {
      B.reveal_ValidRedirectNewGrandchildren();
    }
  }

  lemma MergeRouteNewChild(f: P.NodeFusion, r: B.Redirect, childref: Reference, edge: B.G.Edge) returns (key: Key)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires Keyspace.lte(f.fused_parent.pivotTable[f.slot_idx], f.fused_child.pivotTable[0])
  requires Keyspace.lte(Last(f.fused_child.pivotTable), f.fused_parent.pivotTable[f.slot_idx+1])
  requires r == IMerge(f)
  requires childref in r.new_children
  requires edge in r.new_children[childref].children.Values
  ensures B.ValidRedirectNewGrandchildrenCheckKey(r, key, childref, edge.ref)
  {
    assert childref == f.fused_childref;
    var new_child := r.new_children[childref];

    var k :| k in new_child.children && new_child.children[k].ref == edge.ref;
    var i := Route(f.fused_child.pivotTable, k);

    key := GetKeyInChildBucket(f.fused_parent.pivotTable, f.fused_child.pivotTable, f.slot_idx, i);
  }

  lemma RefinesValidMerge(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires ReadOpsBucketsWellMarshalled(P.MergeReads(f))
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  ensures B.ValidRedirect(IMerge(f))
  {
    var r := IMerge(f);
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);
    assert P.InvNode(P.MergeOps(f)[0].node);
    assert P.InvNode(P.MergeOps(f)[1].node);

    B.reveal_ValidRedirect();

    MergeRefinesWFRedirect(f);
    MergeRefinesRedirectNewParent(f);
    MergeRefinesRedirectNewChildren(f);
    MergeRefinesRedirectNewGrandChildren(f);
  }

  lemma SplitRefinesWFRedirect(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  ensures B.WFRedirect(ISplit(f))
  {
    var r := ISplit(f);
    var old_parent_children_ref := imap k | k in r.old_parent.children :: r.old_parent.children[k].ref;

    forall ref | ref in r.old_childrefs
    ensures ref in IMapRestrict(old_parent_children_ref, r.keys).Values
    {
      assert ref == f.fused_childref;
      var key := GetKeyInBucket(f.fused_parent.pivotTable, f.slot_idx);
      assert IMapRestrict(old_parent_children_ref, r.keys)[key] == ref;
    }
  }

  lemma SplitRefinesRedirectNewParent(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires B.WFRedirect(ISplit(f))
  ensures B.ValidRedirectNewParent(ISplit(f))
  {
    reveal_SplitBucketInList();
    SplitMergeBuffersChildrenEq(f.fused_parent, f.split_parent, f.slot_idx);
  }

  lemma SplitRefinesRedirectNewChildren(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires B.WFRedirect(ISplit(f))
  requires B.ValidRedirectNewParent(ISplit(f))
  ensures B.ValidRedirectNewChildren(ISplit(f))
  {
    var r := ISplit(f);

    var child := P.RestrictAndTranslateChild(f.fused_parent, f.fused_child, f.slot_idx);
    assert child.pivotTable[0] == f.fused_parent.pivotTable[f.slot_idx];
    assert Last(child.pivotTable) == f.fused_parent.pivotTable[f.slot_idx+1];
    assert Last(f.left_child.pivotTable) == f.right_child.pivotTable[0] == KeyToElement(f.pivot);
    assert Last(f.right_child.pivotTable) == Last(child.pivotTable);

    WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, child, f.pivot, f.num_children_left);

    forall key:Key | key in r.keys 
    ensures r.old_parent.children[key].ref in r.old_children
      && var newchild := r.new_children[r.new_parent.children[key].ref];
      && var oldchild := r.old_children[r.old_parent.children[key].ref];
      && var edgekey := r.old_parent.children[key].edgeKey; // translated key
      && newchild.buffer[key] == oldchild.buffer[edgekey]
      && ((key in newchild.children) <==> (edgekey in oldchild.children))
      && ((key in newchild.children) ==> newchild.children[key] == oldchild.children[edgekey])
    {
      var edgekey := r.old_parent.children[key].edgeKey;
      assert BoundedKey(f.fused_parent.pivotTable, key);
      assert BoundedKey(f.split_parent.pivotTable, key);

      RestrictAndTranslateKeyConsistency(f.fused_parent, f.fused_child, child, f.slot_idx, key);
      if (P.G.Keyspace.lt(key, f.pivot)) {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx);
        assert r.new_parent.children[key].ref == f.left_childref;
        assert r.new_children[r.new_parent.children[key].ref] == INode(f.left_child);
        MergedNodeAndLeftAgree(f.left_child, f.right_child, child, f.pivot, key);
      } else {
        RouteIs(f.split_parent.pivotTable, key, f.slot_idx+1);
        assert r.new_parent.children[key].ref == f.right_childref;
        assert r.new_children[r.new_parent.children[key].ref] == INode(f.right_child);
        WriteFusedChildInTermsOfLeftAndRight(f.left_child, f.right_child, child, f.pivot, f.num_children_left);
        MergedNodeAndRightAgree(f.left_child, f.right_child, child, f.pivot, key);
      }
    }
  }

  lemma SplitRefinesRedirectNewGrandChildren(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires B.WFRedirect(ISplit(f))
  requires B.ValidRedirectNewParent(ISplit(f))
  requires B.ValidRedirectNewChildren(ISplit(f))
  ensures B.ValidRedirectNewGrandchildren(ISplit(f))
  {
    var r := ISplit(f);

    var child := P.RestrictAndTranslateChild(f.fused_parent, f.fused_child, f.slot_idx);
    assert child.pivotTable[0] == f.fused_parent.pivotTable[f.slot_idx];
    assert Last(child.pivotTable) == f.fused_parent.pivotTable[f.slot_idx+1];
    assert f.fused_parent.pivotTable[f.slot_idx] == f.split_parent.pivotTable[f.slot_idx];
    assert f.fused_parent.pivotTable[f.slot_idx+1] == f.split_parent.pivotTable[f.slot_idx+2];

    forall childref, edge | childref in r.new_children && edge in r.new_children[childref].children.Values
    ensures exists key :: B.ValidRedirectNewGrandchildrenCheckKey(r, key, childref, edge.ref)
    {
      var _ := SplitRouteNewChild(f, r, childref, edge);
    }

    assert B.ValidRedirectNewGrandchildren(r) by {
      B.reveal_ValidRedirectNewGrandchildren();
    }
  }

  lemma SplitRouteNewChild(f: P.NodeFusion, r: B.Redirect, childref: Reference, edge: B.G.Edge) returns (key: Key)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires Keyspace.lte(f.split_parent.pivotTable[f.slot_idx], f.left_child.pivotTable[0])
  requires Keyspace.lte(Last(f.left_child.pivotTable), f.split_parent.pivotTable[f.slot_idx+1])
  requires Keyspace.lte(f.split_parent.pivotTable[f.slot_idx+1], f.right_child.pivotTable[0])
  requires Keyspace.lte(Last(f.right_child.pivotTable), f.split_parent.pivotTable[f.slot_idx+2])
  requires r == ISplit(f)
  requires childref in r.new_children
  requires edge in r.new_children[childref].children.Values
  ensures B.ValidRedirectNewGrandchildrenCheckKey(r, key, childref, edge.ref)
  {
    var new_child := r.new_children[childref];
    var k :| k in new_child.children && new_child.children[k].ref == edge.ref;

    var parent_slot;
    var lr_child;
    if (childref == f.left_childref) {
      parent_slot := f.slot_idx;
      lr_child := f.left_child;
    } else {
      parent_slot := f.slot_idx + 1;
      lr_child := f.right_child;
    }

    var child_slot := Route(lr_child.pivotTable, k);
    key := GetKeyInChildBucket(f.split_parent.pivotTable, lr_child.pivotTable, parent_slot, child_slot);
  }

  lemma RefinesValidSplit(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires ReadOpsBucketsWellMarshalled(P.SplitReads(f))
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  ensures B.ValidRedirect(ISplit(f))
  {
    var r := ISplit(f);
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(f);

    SplitRefinesWFRedirect(f);
    SplitRefinesRedirectNewParent(f);
    SplitRefinesRedirectNewChildren(f);
    SplitRefinesRedirectNewGrandChildren(f);

    assert B.ValidRedirect(r) by {
      B.reveal_ValidRedirect();
    }
  }

  lemma RestrictAndTranslateNodeKeyRange(node: PNode, node': PNode, from: Key, to: Key)
  requires P.WFNode(node)
  requires ContainsAllKeys(node.pivotTable)
  requires node.children.Some?
  requires P.G.Keyspace.lt([], to)
  requires node' == P.RestrictAndTranslateNode(node, from, to)
  ensures forall k : Key | IsPrefix(to, k) :: BoundedKey(node'.pivotTable, k)
  ensures AllKeysInBetweenHasPrefix(node'.pivotTable[0], Last(node'.pivotTable), to)
  {
    assert node'.pivotTable[0] == KeyToElement(to);
    assert Last(node'.pivotTable) == ShortestUncommonPrefix(to, |to|);
    PrefixOfLcpIsPrefixOfKeys(node'.pivotTable[0], Last(node'.pivotTable), to);

    forall k : Key | IsPrefix(to, k)
    ensures BoundedKey(node'.pivotTable, k)
    {
      reveal_IsPrefix();
      P.G.Keyspace.EmptyLte(k[|to|..]);
      PrefixLteProperties(to, to, k);
      assert Keyspace.lte(node'.pivotTable[0], KeyToElement(k));

      if Last(node'.pivotTable).Element? {
        Keyspace.reveal_IsStrictlySorted();
        assert !IsPrefix(to, Last(node'.pivotTable).e);
        KeyWithPrefixLt(to, Last(node'.pivotTable).e, k);
      }
    }
  }

  lemma RestrictAndTranslateNodePreservesChildren(node: PNode, node': PNode, from: Key, to: Key, key: Key, key': Key)
  requires P.InvNode(node)
  requires ContainsAllKeys(node.pivotTable)
  requires node.children.Some?
  requires P.G.Keyspace.lt([], to)
  requires node' == P.RestrictAndTranslateNode(node, from, to)
  requires IsPrefix(to, key')
  requires BoundedKey(node.pivotTable, key)
  requires BoundedKey(node'.pivotTable, key')
  requires key == from + key'[|to|..]
  ensures IChildren(node)[key] == IChildren(node')[key']
  {
    var fromend := ShortestUncommonPrefix(from, |from|);
    var fromendkey := if fromend.Element? then (var k : Key := fromend.e; Some(k)) else None;

    ContainsAllKeysImpliesBoundedKey(node.pivotTable, from);
    var fromnode := P.CutoffNode(node, from, fromendkey);

    P.G.Keyspace.EmptyLte(key[|from|..]);
    PrefixLteProperties(from, from, key);
    if fromendkey.Some? {
      KeyWithPrefixLt(from, fromendkey.value, key);
    }

    CutoffNodeAgree(node, fromnode, from, fromendkey, key);
    assert IChildren(node)[key] == IChildren(fromnode)[key];

    var toend := ShortestUncommonPrefix(to, |to|);
    assert node'.pivotTable[0] == KeyToElement(to);
    assert Last(node'.pivotTable) == toend;
    assert PivotLcp(node'.pivotTable[0], Last(node'.pivotTable)) == to;

    TranslatePivotsSameRoute(fromnode.pivotTable, node'.pivotTable, from, to, key, key');
    TranslatePivotsEdgesPreserveTranslateKey(fromnode.pivotTable, fromnode.edgeTable,
      node'.pivotTable, node'.edgeTable, from, to, Last(node'.pivotTable), key, key');
  }

  predicate IsNodeSlice(node: PNode, subnode: PNode, a: int, b: int)
  {
    && P.WFNode(node)
    && P.WFNode(subnode)
    && 0 <= a < b < |node.pivotTable|
    && |subnode.buckets| <= |node.buckets|
    && node.pivotTable[a..b+1] == subnode.pivotTable
    && node.edgeTable[a..b] == subnode.edgeTable
    && node.buckets[a..b] == subnode.buckets
    && (node.children.Some? <==> subnode.children.Some?)
    && (node.children.Some? ==> node.children.value[a..b] == subnode.children.value)
  }

  lemma NodeSliceProperty(node: PNode, subnode: PNode, key: Key, a: int, b: int)
  requires IsNodeSlice(node, subnode, a, b)
  requires BoundedKey(node.pivotTable, key)
  requires BoundedKey(subnode.pivotTable, key)
  ensures IBuffer(node)[key] == IBuffer(subnode)[key]
  ensures node.children.Some? ==> IChildren(node)[key] == IChildren(subnode)[key]
  {
    var r := Route(node.pivotTable, key);
    var r' := Route(subnode.pivotTable, key);
    assert r' == r - a;
    if node.children.Some? {
      assert node.children.value[r] == subnode.children.value[r'];
    }
  }

  lemma RefinesValidClone(clone: P.NodeClone)
  requires P.ValidClone(clone)
  requires forall i | 0 <= i < |P.CloneReads(clone)| :: P.InvNode(P.CloneReads(clone)[i].node)
  requires ReadOpsBucketsWellMarshalled(P.CloneReads(clone))
  ensures B.ValidClone(IClone(clone))
  {
    var c := IClone(clone);
    PivotBetreeSpecWFNodes.ValidCloneWritesInvNodes(clone);
    assert P.InvNode(P.CloneReads(clone)[0].node);

    // oldroot buffer condition
    forall k | k in c.new_to_old
    ensures IMapsTo(c.oldroot.buffer, c.new_to_old[k], Update(NopDelta()))
    ensures c.new_to_old[k] in c.oldroot.children
    {
      ContainsAllKeysImpliesBoundedKey(clone.oldroot.pivotTable, c.new_to_old[k]);
      var r := Route(clone.oldroot.pivotTable, c.new_to_old[k]);
      assert BucketNoKeyWithPrefix(clone.oldroot.buckets[r], clone.from);
      assert IsPrefix(clone.from, c.new_to_old[k]) by { reveal_IsPrefix(); }
      MapSeqs.key_sets_eq(clone.oldroot.buckets[r].keys, clone.oldroot.buckets[r].msgs);
    }

    // new root condition - keys affected by clone
    ContainsAllKeysImpliesBoundedKey(clone.oldroot.pivotTable, clone.to);
    var lnode := P.CutoffNodeAndKeepLeft(clone.oldroot, clone.to);
    assert Last(lnode.pivotTable) == KeyToElement(clone.to);
    assert |lnode.pivotTable| < |clone.newroot.pivotTable|;

    var tonode := P.RestrictAndTranslateNode(clone.oldroot, clone.from, clone.to);
    RestrictAndTranslateNodeKeyRange(clone.oldroot, tonode, clone.from, clone.to);

    var tostart := |lnode.buckets|;
    var toend := |lnode.buckets|+|tonode.buckets|;
    assert IsNodeSlice(clone.newroot, tonode, tostart, toend);

    forall k | k in c.new_to_old
    ensures IMapsTo(c.newroot.buffer, k, Update(NopDelta()))
    ensures IMapsTo(c.newroot.children, k, c.oldroot.children[c.new_to_old[k]])
    {
      RestrictAndTranslateNodePreservesChildren(clone.oldroot, tonode, clone.from, clone.to, c.new_to_old[k], k);
      ContainsAllKeysImpliesBoundedKey(clone.newroot.pivotTable, k);
      NodeSliceProperty(clone.newroot, tonode, k, tostart, toend);
    }

    // new root condition - keys not affected by clone
    assert clone.newroot.pivotTable[..tostart] == lnode.pivotTable[..tostart];
    assert clone.newroot.pivotTable[tostart] == KeyToElement(clone.to);
    assert IsNodeSlice(clone.newroot, lnode, 0, tostart);

    var rnode : PNode;
    var toendkey : Key;
    if Last(tonode.pivotTable).Element? {
      toendkey := GetKey(tonode.pivotTable, |tonode.pivotTable|-1);
      rnode := P.CutoffNodeAndKeepRight(clone.oldroot, toendkey);
      assert IsNodeSlice(clone.newroot, rnode, toend, |clone.newroot.buckets|);
    }

    forall k : Key | k !in c.new_to_old
    ensures IMapsAgreeOnKey(c.newroot.buffer, c.oldroot.buffer, k)
    ensures IMapsAgreeOnKey(c.newroot.children, c.oldroot.children, k)
    {
      ContainsAllKeysImpliesBoundedKey(clone.oldroot.pivotTable, k);
      ContainsAllKeysImpliesBoundedKey(clone.newroot.pivotTable, k);
      var r := Route(clone.newroot.pivotTable, k);
      assert r < tostart || r >= toend;

      if r < tostart {
        CutoffNodeAndKeepLeftAgree(clone.oldroot, lnode, clone.to, k);
        NodeSliceProperty(clone.newroot, lnode, k, 0, tostart);
      } else {
        CutoffNodeAndKeepRightAgree(clone.oldroot, rnode, toendkey, k);
        NodeSliceProperty(clone.newroot, rnode, k, toend, |clone.newroot.buckets|);
      }
    }
  }

  lemma RefinesValidBetreeStep(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  ensures B.ValidBetreeStep(IStep(betreeStep))
  {
    match betreeStep {
      case BetreeQuery(q) => RefinesValidQuery(q);
      case BetreeSuccQuery(sq) => RefinesValidSuccQuery(sq);
      case BetreeInsert(ins) => RefinesValidInsertion(ins);
      case BetreeFlush(flush) => RefinesValidFlush(flush);
      case BetreeGrow(growth) => RefinesValidGrow(growth);
      case BetreeSplit(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        RefinesValidSplit(fusion);
      }
      case BetreeMerge(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        RefinesValidMerge(fusion);
      }
      case BetreeClone(clone) => RefinesValidClone(clone);
    }
  }

  lemma {:fuel IReadOps,3} RefinesReadOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures IReadOps(P.BetreeStepReads(betreeStep)) == B.BetreeStepReads(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);
  }

  // interpret the pivot-y Ops (from our little cache DSL) to their Betree (non-pivot) versions.
  function IOp(op: P.G.Op) : B.G.Op
  requires P.InvNode(op.node)
  {
    match op {
      case AllocOp(ref, block) => B.G.AllocOp(ref, INode(block))
      case WriteOp(ref, block) => B.G.WriteOp(ref, INode(block))
    }
  }

  function IOps(ops: seq<P.G.Op>) : seq<B.G.Op>
  requires forall i | 0 <= i < |ops| :: P.InvNode(ops[i].node)
  {
    if |ops| == 0 then [] else
      IOps(ops[..|ops|-1]) + [IOp(ops[|ops|-1])]
  }

  lemma InsertRefinesOps(ins: P.MessageInsertion)
  requires P.ValidInsertion(ins)
  requires forall i | 0 <= i < |P.InsertionReads(ins)| :: P.InvNode(P.InsertionReads(ins)[i].node)
  requires B.ValidInsertion(IInsertion(ins))
  ensures forall i | 0 <= i < |P.InsertionOps(ins)| ::
      P.InvNode(P.InsertionOps(ins)[i].node)
  ensures IOps(P.InsertionOps(ins)) == B.InsertionOps(IInsertion(ins))
  {
    assert P.InvNode(P.InsertionReads(ins)[0].node);
    PivotBetreeSpecWFNodes.ValidInsertWritesInvNodes(ins);
    assert P.InvNode(P.InsertionOps(ins)[0].node);

    var newroot := P.AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var newroot' := B.AddMessageToNode(INode(ins.oldroot), ins.key, ins.msg);

    forall key:Key
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
            BucketGet(oldroot.buckets[Route(oldroot.pivotTable, ins.key)].as_map(), ins.key),
            DefineDefault()
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

  lemma {:fuel IOps,2} FlushRefinesOps(flush: P.NodeFlush)
  requires P.ValidFlush(flush)
  requires forall i | 0 <= i < |P.FlushReads(flush)| :: P.InvNode(P.FlushReads(flush)[i].node)
  requires B.ValidFlush(IFlush(flush))
  ensures forall i | 0 <= i < |P.FlushOps(flush)| ::
      P.InvNode(P.FlushOps(flush)[i].node)
  ensures IOps(P.FlushOps(flush)) == B.FlushOps(IFlush(flush))
  {
    PivotBetreeSpecWFNodes.ValidFlushWritesInvNodes(flush);
  }

  lemma {:fuel IOps,3} GrowRefinesOps(growth: P.RootGrowth)
  requires P.ValidGrow(growth)
  requires forall i | 0 <= i < |P.GrowReads(growth)| :: P.InvNode(P.GrowReads(growth)[i].node)
  requires B.ValidGrow(IGrow(growth))
  ensures forall i | 0 <= i < |P.GrowOps(growth)| ::
      P.InvNode(P.GrowOps(growth)[i].node)
  ensures IOps(P.GrowOps(growth)) == B.GrowOps(IGrow(growth))
  {
    assert P.InvNode(P.GrowReads(growth)[0].node);
    PivotBetreeSpecWFNodes.ValidGrowWritesInvNodes(growth);

    var newroot := P.G.Node(InitPivotTable(), [None], Some([growth.newchildref]), [EmptyBucket()]);
    P.PivotsHasAllKeys(newroot.pivotTable);

    // observe: (I don't know really know why this is necessary)
    assert B.GrowOps(IGrow(growth))[1] 
        == B.G.WriteOp(B.G.Root(), INode(newroot));
  }

  lemma {:fuel IOps,3} SplitRefinesOps(f: P.NodeFusion)
  requires P.ValidSplit(f)
  requires P.InvNode(f.fused_parent)
  requires P.InvNode(f.fused_child)
  requires B.ValidRedirect(ISplit(f))
  ensures forall i | 0 <= i < |P.SplitOps(f)| ::
      P.InvNode(P.SplitOps(f)[i].node)
  ensures IOps(P.SplitOps(f)) == B.RedirectOps(ISplit(f))
  {
    PivotBetreeSpecWFNodes.ValidSplitWritesInvNodes(f);
    assert IOp(P.G.AllocOp(f.left_childref, f.left_child)) == B.RedirectOps(ISplit(f))[0];
    assert IOp(P.G.AllocOp(f.right_childref, f.right_child)) == B.RedirectOps(ISplit(f))[1];
    assert IOp(P.G.WriteOp(f.parentref, f.split_parent)) == B.RedirectOps(ISplit(f))[2];

    /*
    assert IOps(P.SplitOps(f)) == [
      IOp(P.G.AllocOp(f.left_childref, f.left_child)),
      IOp(P.G.AllocOp(f.right_childref, f.right_child)),
      IOp(P.G.WriteOp(f.parentref, f.split_parent))
    ];

    assert IOps(P.SplitOps(f))
        == [
          IOp(P.G.AllocOp(f.left_childref, f.left_child)),
          IOp(P.G.AllocOp(f.right_childref, f.right_child)),
          IOp(P.G.WriteOp(f.parentref, f.split_parent))
        ]
        == [
          B.RedirectOps(ISplit(f))[0],
          B.RedirectOps(ISplit(f))[1],
          B.RedirectOps(ISplit(f))[2]
        ]
        == B.RedirectOps(ISplit(f));
        */
  }

  lemma {:fuel IOps,3} MergeRefinesOps(f: P.NodeFusion)
  requires P.ValidMerge(f)
  requires P.InvNode(f.split_parent)
  requires P.InvNode(f.left_child)
  requires P.InvNode(f.right_child)
  requires B.ValidRedirect(IMerge(f))
  ensures forall i | 0 <= i < |P.MergeOps(f)| ::
      P.InvNode(P.MergeOps(f)[i].node)
  ensures IOps(P.MergeOps(f)) == B.RedirectOps(IMerge(f))
  {
    PivotBetreeSpecWFNodes.ValidMergeWritesInvNodes(f);
  }

  lemma {:fuel IOps,3} CloneRefinesOps(c: P.NodeClone)
  requires P.ValidClone(c)
  requires P.InvNode(c.oldroot)
  requires B.ValidClone(IClone(c))
  ensures forall i | 0 <= i < |P.CloneOps(c)| ::
      P.InvNode(P.CloneOps(c)[i].node)
  ensures IOps(P.CloneOps(c)) == B.CloneOps(IClone(c))
  {
    PivotBetreeSpecWFNodes.ValidCloneWritesInvNodes(c);
  }

  // The meaty lemma: If we mutate the nodes of a pivot-y cache according to a
  // (generic-DSL) BetreeStep, under the INode interpretation, the same
  // mutation happens to the imap-y cache.
  lemma {:fuel IOps,3} RefinesOps(betreeStep: P.BetreeStep)
  requires P.ValidBetreeStep(betreeStep)
  requires !betreeStep.BetreeRepivot?
  requires ReadOpsBucketsWellMarshalled(P.BetreeStepReads(betreeStep))
  requires forall i | 0 <= i < |P.BetreeStepReads(betreeStep)| :: P.InvNode(P.BetreeStepReads(betreeStep)[i].node)
  ensures B.ValidBetreeStep(IStep(betreeStep))
  ensures forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
      P.InvNode(P.BetreeStepOps(betreeStep)[i].node)
  ensures IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep))
  {
    RefinesValidBetreeStep(betreeStep);

    match betreeStep {
      case BetreeQuery(q) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.InvNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
      case BetreeSuccQuery(q) => {
        assert forall i | 0 <= i < |P.BetreeStepOps(betreeStep)| ::
            P.InvNode(P.BetreeStepOps(betreeStep)[i].node);
        assert IOps(P.BetreeStepOps(betreeStep)) == B.BetreeStepOps(IStep(betreeStep));
      }
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
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        SplitRefinesOps(fusion);
      }
      case BetreeMerge(fusion) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[1].node);
        assert P.InvNode(P.BetreeStepReads(betreeStep)[2].node);
        MergeRefinesOps(fusion);
      }
      case BetreeClone(clone) => {
        assert P.InvNode(P.BetreeStepReads(betreeStep)[0].node);
        CloneRefinesOps(clone);
      }
    }
  }

  // /*lemma IBufferLeafEqJoin(node: PNode)
  // requires P.InvNode(node)
  // requires BucketListWellMarshalled(node.buckets)
  // ensures IBufferLeaf(node) == imap key :: if BoundedKey(node.pivotTable, key) then Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault()) else DefineDefault() 
  // {
  //   forall key:Key | BoundedKey(node.pivotTable, key)
  //   ensures IBufferLeaf(node)[key] == Merge(BucketGet(JoinBucketList(node.buckets), key), DefineDefault())
  //   {
  //     forall i | 0 <= i < |node.buckets| ensures WFBucketAt(node.buckets[i], node.pivotTable, i)
  //     {
  //     }
  //     GetJoinBucketListEq(node.buckets, node.pivotTable, key);
  //   }
  // }*/

  lemma RepivotPreservesNode(r: P.Repivot)
  requires P.ValidRepivot(r)
  requires forall i | 0 <= i < |P.RepivotReads(r)| :: P.InvNode(P.RepivotReads(r)[i].node)
  ensures P.InvNode(P.ApplyRepivot(r))
  ensures INode(r.leaf) == INode(P.ApplyRepivot(r))
  {
    assert P.InvNode(P.RepivotReads(r)[0].node);
    PivotBetreeSpecWFNodes.InvApplyRepivot(r);

    P.PivotsHasAllKeys(r.pivots);
    assert r.pivots[1] == KeyToElement(r.pivot);

    MapSeqs.key_sets_eq(r.leaf.buckets[0].keys, r.leaf.buckets[0].msgs);

    PivotBetreeSpecWFNodes.SplitMaps(r.leaf.buckets[0], r.pivot);

    /*var leaf'_buckets := [
          SplitBucketLeft(r.leaf.buckets[0], r.idx),
          SplitBucketRight(r.leaf.buckets[0], r.idx)
        ];*/

    //PivotBetreeSpecWFNodes.bucket_keys_equiv(r.leaf.buckets[0]);
    //PivotBetreeSpecWFNodes.bucket_keys_equiv(leaf'_buckets[0]);
    //PivotBetreeSpecWFNodes.bucket_keys_equiv(leaf'_buckets[1]);

    /*var buckets1 := r.leaf.buckets;
    P.PivotsHasAllKeys(r.pivots);
    BoundedBucketListJoin(buckets1, r.pivots);
    var joined := JoinBucketList(buckets1);
    WFJoinBucketList(buckets1);
    var buckets2 := SplitBucketOnPivots(joined, r.pivots);
    WFSplitBucketOnPivots(joined, r.pivots);

    forall i | 0 <= i < |buckets1|
    ensures forall key:Key | key in buckets1[i].as_map() :: buckets1[i].as_map()[key] != IdentityMessage()
    {
      //assert P.NodeHasWFBucketAt(r.leaf, i);
    }
    WFJoinBucketList(r.leaf.buckets);
    JoinBucketsSplitBucketOnPivotsCancel(joined, r.pivots);
    assert JoinBucketList(buckets1) == JoinBucketList(buckets2);
    
  //   IBufferLeafEqJoin(r.leaf);
  //   IBufferLeafEqJoin(P.ApplyRepivot(r));

  //   BoundedBucketListJoin(buckets1, r.leaf.pivotTable);
  //   assert BoundedBucket(joined, r.leaf.pivotTable);*/
  }
}
