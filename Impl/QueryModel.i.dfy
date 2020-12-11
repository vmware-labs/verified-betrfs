include "StateModel.i.dfy"
include "BookkeepingModel.i.dfy"
include "EvictModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in MainHandlers.dfy

module QueryModel { 
  import opened StateBCModel
  import opened StateSectorModel

  import opened IOModel
  import opened BookkeepingModel
  import opened EvictModel
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
  // == query ==

  predicate {:opaque} queryIterate(s: BCVariables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64,
      s': BCVariables, result: Option<Value>, io': IO)    
  requires s.Ready?
  requires BCInv(s)
  requires io.IOInit?
  requires ref in s.ephemeralIndirectionTable.graph
  requires counter >= 0
  decreases counter
  {
    if counter == 0 then (
      && s' == s
      && result == None
      && io' == io
    ) else (
      if (ref !in s.cache) then (
        && PageInNodeReqOrMakeRoom(s, io, ref, s', io')
        && result == None
      ) else (
        var node := s.cache[ref];
        if !BoundedKey(node.pivotTable, key) then (
          // TODO: no op if not bounded?
          && s' == s
          && result == None
          && io' == io
        ) else (
          var s0 := s.(lru := LruModel.Use(s.lru, ref));
          LruModel.LruUse(s.lru, ref);
          assert IBlockCache(s0) == IBlockCache(s);
          var r := Pivots.Route(node.pivotTable, key);
          var bucket := node.buckets[r];
          var kmtMsg := bucketBinarySearchLookup(bucket, key);
          var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;
          if newmsg.Define? then (
            && s' == s0
            && result == Some(newmsg.value)
            && io' == io
          ) else (
            if node.children.Some? then (
            var childref := node.children.value[r];
              lemmaChildInGraph(s0, ref, childref);
              && queryIterate(s0, key, newmsg, childref, io, counter - 1, s', result, io')
            ) else (
              && s' == s0
              && result == Some(ValueType.DefaultValue())
              && io' == io
            )
          )
        ) 
      )
    )
  }

  predicate {:opaque} query(s: BCVariables, io: IO, key: Key,
      s': BCVariables, result: Option<Value>, io': IO)
  requires io.IOInit?
  requires s.Ready?
  requires BCInv(s)
  {
    queryIterate(s, key, Messages.IdentityMessage(), BT.G.Root(), io, 40, s', result, io')
  }

  predicate queryInv(s: BCVariables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64, lookup: seq<BT.G.ReadOp>)
  {
    && s.Ready?
    && BCInv(s)
    && io.IOInit?
    && ref in s.ephemeralIndirectionTable.graph
    && counter >= 0
    && (|lookup| == 0 ==> ref == BT.G.Root())
    && (msg.Define? ==> |lookup| > 0)
    && (|lookup| > 0 ==> BT.WFLookupForKey(lookup, key))
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.Some?)
    && (!msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref)
    && (forall i | 0 <= i < |lookup| :: lookup[i].ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
    && (forall i | 0 <= i < |lookup| :: MapsTo(ICache(s.cache), lookup[i].ref, lookup[i].node))
    && (forall i | 0 <= i < |lookup| :: BoundedKey(lookup[i].node.pivotTable, key))
    && (ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
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
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
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

  lemma queryIterateCorrect(s: BCVariables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64, lookup: seq<BT.G.ReadOp>,
      s': BCVariables, res: Option<Value>, io': IO)
  requires queryInv(s, key, msg, ref, io, counter, lookup)
  requires !msg.Define?
  requires queryIterate(s, key, msg, ref, io, counter, s', res, io');
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(IBlockCache(s), IBlockCache(s'),
          IDiskOp(diskOp(io')).bdop,
          AdvanceOp(UI.GetOp(key, res.value), false));
  ensures res.None? ==>
      betree_next_dop(IBlockCache(s), IBlockCache(s'),
          IDiskOp(diskOp(io')).bdop)
  decreases counter
  {
    reveal_queryIterate();

    if counter == 0 {
      assert noop(IBlockCache(s), IBlockCache(s));
    } else {
      if (ref !in s.cache) {
        PageInNodeReqOrMakeRoomCorrect(s, io, ref, s', io');
      } else {
        var node := s.cache[ref];
        if !BoundedKey(node.pivotTable, key) {
          assert noop(IBlockCache(s), IBlockCache(s));
        } else {
          var s0 := s.(lru := LruModel.Use(s.lru, ref));
          LruModel.LruUse(s.lru, ref);
          assert IBlockCache(s0) == IBlockCache(s);

          var r := Pivots.Route(node.pivotTable, key);
          var bucket := node.buckets[r];

          var kmtMsg := bucketBinarySearchLookup(bucket, key);
          var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;

          var lookupMsg := if kmtMsg.Some? then kmtMsg.value else Messages.IdentityMessage();
          assert newmsg == Messages.Merge(msg, lookupMsg);
          assert BucketWellMarshalled(bucket) ==> lookupMsg == BT.NodeLookup(node, key);

          var newlookup := new_lookup(lookup, ref, node);
          AugmentLookup(newlookup, lookup, ref, node, key, ICache(s0.cache), IIndirectionTable(s0.ephemeralIndirectionTable).graph);

          assert PBS.LookupVisitsWellMarshalledBuckets(newlookup, key) ==> BucketWellMarshalled(bucket);
          assert PBS.LookupVisitsWellMarshalledBuckets(newlookup, key) ==> PBS.LookupVisitsWellMarshalledBuckets(lookup, key)
          by {
            reveal_new_lookup();
          }

          if newmsg.Define? {
            assert BT.ValidQuery(BT.LookupQuery(key, res.value, newlookup));
            assert BBC.BetreeMove( IBlockCache(s), IBlockCache(s0),
              IDiskOp(diskOp(io)).bdop,
              AdvanceOp(UI.GetOp(key, res.value), false),
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
            assert stepsBetree(IBlockCache(s), IBlockCache(s0),
              AdvanceOp(UI.GetOp(key, res.value), false),
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
          } else {
            if node.children.Some? {
              var childref := node.children.value[r];
              lemmaChildInGraph(s0, ref, childref);
              queryIterateCorrect(s0, key, newmsg, childref, io, counter - 1,    
                newlookup, s', res, io');
            } else {
              assert BC.OpTransaction(IBlockCache(s), IBlockCache(s0),
                PBS.BetreeStepOps(BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup))));

              assert BBC.BetreeMove(IBlockCache(s), IBlockCache(s0),
                IDiskOp(diskOp(io)).bdop,
                AdvanceOp(UI.GetOp(key, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));

              assert stepsBetree(IBlockCache(s), IBlockCache(s0),
                AdvanceOp(UI.GetOp(key, res.value), false),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
            }
          }
        }
      }
    }
  }

  lemma queryCorrect(s: BCVariables, io: IO, key: Key,
      s': BCVariables, res: Option<Value>, io': IO)
  requires io.IOInit?
  requires BCInv(s)
  requires s.Ready?
  requires query(s, io, key, s', res, io');
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures res.Some? ==>
      BBC.Next(IBlockCache(s), IBlockCache(s'),
          IDiskOp(diskOp(io')).bdop,
          AdvanceOp(UI.GetOp(key, res.value), false));
  ensures res.None? ==>
      betree_next_dop(IBlockCache(s), IBlockCache(s'),
          IDiskOp(diskOp(io')).bdop)

  {
    reveal_query();
    queryIterateCorrect(s, key, Messages.IdentityMessage(), BT.G.Root(), io, 40, [], s', res, io');
  }
}
