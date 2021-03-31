// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in MainHandlers.dfy

module QueryModel { 
  import opened IOModel
  import opened BookkeepingModel
  import opened KeyType
  import opened ViewOp
  import opened InterpretationDiskOps
  import ValueType
  import opened ValueMessage
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened BoundedPivotsLib
  import opened TranslationLib
  import Messages = ValueMessage`Internal

  // == query ==

  predicate queryInv(s: BBC.Variables, key: Key, msg: Message, ref: BT.G.Reference, 
    io: IO, counter: uint64, lookup: seq<BT.Layer>)
  {
    && s.Ready?
    && BBC.Inv(s)
    && io.IOInit?
    && ref in s.ephemeralIndirectionTable.graph
    && counter >= 0
    && (|lookup| == 0 ==> ref == BT.G.Root())
    && (msg.Define? ==> |lookup| > 0)
    && (|lookup| > 0 ==> BT.WFLookupForKey(lookup, lookup[0].currentKey))
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).readOp.node.children.Some?)
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).readOp.node.children.value[
          Route(Last(lookup).readOp.node.pivotTable, Last(lookup).currentKey)] == ref)
    && (!msg.Define? ==> |lookup| > 0 ==> TranslateKey(Last(lookup).readOp.node.pivotTable, 
          Last(lookup).readOp.node.edgeTable, Last(lookup).currentKey) == key)
    && (forall i | 0 <= i < |lookup| :: BT.WFNode(lookup[i].readOp.node))
    && (forall i | 0 <= i < |lookup| :: lookup[i].readOp.ref in s.ephemeralIndirectionTable.graph)
    && (forall i | 0 <= i < |lookup| :: MapsTo(s.cache, lookup[i].readOp.ref, lookup[i].readOp.node))
    && (forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].readOp.node.pivotTable, lookup[i].currentKey))
    && (ref in s.ephemeralIndirectionTable.graph)
    && (BT.LookupVisitsWellMarshalledBuckets(lookup) ==> msg == BT.InterpretLookup(lookup))
  }

  function {:opaque} new_lookup(lookup: seq<BT.Layer>, ref: BT.G.Reference, node: BT.G.Node, key: Key) : seq<BT.Layer>
  {
    lookup + [BT.Layer(BT.G.ReadOp(ref, node), key)]
  }

  lemma AugmentLookup(lookup': seq<BT.Layer>, lookup: seq<BT.Layer>, ref: BT.G.Reference, node: BT.G.Node, 
    key: Key, cache: map<BT.G.Reference, BT.G.Node>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires lookup' == new_lookup(lookup, ref, node, key)
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, lookup[0].currentKey)
  requires forall i | 0 <= i < |lookup| :: BT.WFNode(lookup[i].readOp.node)
  requires forall i | 0 <= i < |lookup| :: lookup[i].readOp.ref in graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(cache, lookup[i].readOp.ref, lookup[i].readOp.node)
  requires forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].readOp.node.pivotTable, lookup[i].currentKey)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).readOp.node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).readOp.node.children.value[
        Route(Last(lookup).readOp.node.pivotTable, Last(lookup).currentKey)] == ref
  requires |lookup| > 0 ==> TranslateKey(Last(lookup).readOp.node.pivotTable, 
        Last(lookup).readOp.node.edgeTable, Last(lookup).currentKey) == key
  requires BT.WFNode(node)
  requires MapsTo(cache, ref, node);
  requires BoundedKey(node.pivotTable, key)
  requires ref in graph
  ensures |lookup'| > 0 && BT.WFLookupForKey(lookup', lookup'[0].currentKey)
  ensures Last(lookup').readOp.node == node
  ensures BT.InterpretLookup(lookup') == Messages.Merge(BT.InterpretLookup(lookup), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: lookup'[i].readOp.ref in graph
  ensures forall i | 0 <= i < |lookup'| :: MapsTo(cache, lookup'[i].readOp.ref, lookup'[i].readOp.node)
  ensures forall i | 0 <= i < |lookup'| :: BoundedKey(lookup'[i].readOp.node.pivotTable, lookup'[i].currentKey)
  {
    reveal_new_lookup();

    forall idx | BT.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
    ensures BT.LookupFollowsChildRefAtLayer(lookup', idx)
    ensures BT.LookupFollowsChildEdgeAtLayer(lookup', idx)
    {
      if idx == |lookup'| - 2 {
        assert BT.LookupFollowsChildRefAtLayer(lookup', idx);
        assert BT.LookupFollowsChildEdgeAtLayer(lookup', idx);
      } else {
        assert BT.LookupFollowsChildRefAtLayer(lookup, idx);
        assert BT.LookupFollowsChildRefAtLayer(lookup', idx);

        assert BT.LookupFollowsChildEdgeAtLayer(lookup, idx);
        assert BT.LookupFollowsChildEdgeAtLayer(lookup', idx);
      }
    }
    assert BT.LookupFollowsChildRefs(lookup');
    assert BT.LookupFollowsChildEdges(lookup');
  }
}
