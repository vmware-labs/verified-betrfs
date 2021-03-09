// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in MainHandlers.dfy

module QueryModel { 
  import opened StateSectorModel

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

  import PBS = PivotBetreeSpec`Internal
  import Messages = ValueMessage`Internal

  // == query ==

  predicate queryInv(s: BBC.Variables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64, lookup: seq<BT.G.ReadOp>)
  {
    && s.Ready?
    && BBC.Inv(s)
    && io.IOInit?
    && ref in s.ephemeralIndirectionTable.graph
    && counter >= 0
    && (|lookup| == 0 ==> ref == BT.G.Root())
    && (msg.Define? ==> |lookup| > 0)
    && (|lookup| > 0 ==> BT.WFLookupForKey(lookup, key))
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.Some?)
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.value[Route(Last(lookup).node.pivotTable, key)] == ref)
    && (forall i | 0 <= i < |lookup| :: lookup[i].ref in s.ephemeralIndirectionTable.graph)
    && (forall i | 0 <= i < |lookup| :: MapsTo(s.cache, lookup[i].ref, lookup[i].node))
    && (forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].node.pivotTable, key))
    && (ref in s.ephemeralIndirectionTable.graph)
    && (PBS.LookupVisitsWellMarshalledBuckets(lookup, key) ==>
        msg == BT.InterpretLookup(lookup, key))
  }


  function {:opaque} new_lookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node) : seq<BT.G.ReadOp>
  {
    lookup + [BT.G.ReadOp(ref, node)]
  }

  lemma AugmentLookup(lookup': seq<BT.G.ReadOp>, lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: Key, cache: map<BT.G.Reference, BT.G.Node>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires lookup' == new_lookup(lookup, ref, node)
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(cache, lookup[i].ref, lookup[i].node)
  requires forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].node.pivotTable, key)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Route(Last(lookup).node.pivotTable, key)] == ref
  requires BT.WFNode(node)
  requires MapsTo(cache, ref, node);
  requires BoundedKey(node.pivotTable, key)
  requires ref in graph;
  ensures BT.WFLookupForKey(lookup', key)
  ensures Last(lookup').node == node
  ensures BT.InterpretLookup(lookup', key) == Messages.Merge(BT.InterpretLookup(lookup, key), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: lookup'[i].ref in graph
  ensures forall i | 0 <= i < |lookup'| :: MapsTo(cache, lookup'[i].ref, lookup'[i].node)
  ensures forall i | 0 <= i < |lookup'| :: BoundedKey(lookup'[i].node.pivotTable, key)
  {
    reveal_new_lookup();

    forall idx | BT.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
    ensures BT.LookupFollowsChildRefAtLayer(key, lookup', idx)
    {
      if idx == |lookup'| - 2 {
        assert BT.LookupFollowsChildRefAtLayer(key, lookup', idx);
      } else {
        assert BT.LookupFollowsChildRefAtLayer(key, lookup, idx);
        assert BT.LookupFollowsChildRefAtLayer(key, lookup', idx);
      }
    }
    assert BT.LookupFollowsChildRefs(key, lookup');
  }
}
