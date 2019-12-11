include "StateModel.i.dfy"
include "BookkeepingModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in Handlers.dfy

module QueryModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import PivotsLib

  import PBS = PivotBetreeSpec`Spec

  // == query ==

  function {:opaque} queryIterate(k: Constants, s: Variables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64)
  : (r : (Variables, Option<MS.Value>, IO))
  requires s.Ready?
  requires Inv(k, s)
  requires io.IOInit?
  requires ref in s.ephemeralIndirectionTable.graph
  requires counter >= 0
  decreases counter
  {
    if counter == 0 then (
      (s, None, io)
    ) else (
      if (ref !in s.cache) then (
        if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
          assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph;

          var (s', io') := PageInReq(k, s, io, ref);
          (s', None, io')
        ) else (
          (s, None, io)
        )
      ) else (
        var node := s.cache[ref];

        var s' := s.(lru := LruModel.Use(s.lru, ref));
        LruModel.LruUse(s.lru, ref);
        assert IVars(s') == IVars(s);

        var r := Pivots.Route(node.pivotTable, key);
        var bucket := node.buckets[r];
        var kmtMsg := MapLookupOption(bucket, key);
        var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;
        if newmsg.Define? then (
          (s', Some(newmsg.value), io)
        ) else (
          if node.children.Some? then (
            lemmaChildInGraph(k, s', ref, node.children.value[r]);
            queryIterate(k, s', key, newmsg, node.children.value[r], io, counter - 1)
          ) else (
            (s', Some(MS.V.DefaultValue()), io)
          )
        )
      )
    )
  }

  function {:opaque} query(k: Constants, s: Variables, io: IO, key: MS.Key)
  : (r : (Variables, Option<MS.Value>, IO))
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (s.Unready?) then (
      var (s', io') := PageInIndirectionTableReq(k, s, io);
      (s', None, io')
    ) else (
      queryIterate(k, s, key, Messages.IdentityMessage(), BT.G.Root(), io, 40)
    )
  }

  predicate queryInv(k: Constants, s: Variables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64, lookup: seq<BT.G.ReadOp>)
  {
    && s.Ready?
    && Inv(k, s)
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
    && (ref in IIndirectionTable(s.ephemeralIndirectionTable).graph)
    && msg == BT.InterpretLookup(lookup, key)
  }

  lemma AugmentLookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: MS.Key, cache: map<BT.G.Reference, BT.G.Node>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  returns (lookup' : seq<BT.G.ReadOp>)
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(cache, lookup[i].ref, lookup[i].node)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
  requires BT.WFNode(node)
  requires MapsTo(cache, ref, node);
  requires ref in graph;
  ensures BT.WFLookupForKey(lookup', key)
  ensures Last(lookup').node == node
  ensures BT.InterpretLookup(lookup', key) == Messages.Merge(BT.InterpretLookup(lookup, key), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: lookup'[i].ref in graph
  ensures forall i | 0 <= i < |lookup'| :: MapsTo(cache, lookup'[i].ref, lookup'[i].node)
  {
    lookup' := lookup + [BT.G.ReadOp(ref, node)];

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

  lemma queryIterateCorrect(k: Constants, s: Variables, key: Key, msg: Message, ref: BT.G.Reference, io: IO, counter: uint64, lookup: seq<BT.G.ReadOp>)
  requires queryInv(k, s, key, msg, ref, io, counter, lookup)
  requires !msg.Define?
  ensures var (s', res, io') := queryIterate(k, s, key, msg, ref, io, counter);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'),
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          diskOp(io'))
  decreases counter
  {
    reveal_queryIterate();
    var (s', res, io') := queryIterate(k, s, key, msg, ref, io, counter);

    if counter == 0 {
      assert noop(k, IVars(s), IVars(s));
    } else {
      if (ref !in s.cache) {
        if TotalCacheSize(s) <= MaxCacheSize() - 1 {
          PageInReqCorrect(k, s, io, ref);
        } else {
          assert noop(k, IVars(s), IVars(s));
        }
      } else {
        var node := s.cache[ref];

        var s' := s.(lru := LruModel.Use(s.lru, ref));
        LruModel.LruUse(s.lru, ref);
        assert IVars(s') == IVars(s);

        var r := Pivots.Route(node.pivotTable, key);
        var bucket := node.buckets[r];

        var kmtMsg := MapLookupOption(bucket, key);
        var newmsg := if kmtMsg.Some? then Messages.Merge(msg, kmtMsg.value) else msg;

        var lookupMsg := if kmtMsg.Some? then kmtMsg.value else Messages.IdentityMessage();
        assert newmsg == Messages.Merge(msg, lookupMsg);

        var inode := INode(s'.cache[ref]);
        assert lookupMsg == BT.NodeLookup(inode, key);

        var newlookup := AugmentLookup(lookup, ref, inode, key, ICache(s'.cache), IIndirectionTable(s'.ephemeralIndirectionTable).graph);

        if newmsg.Define? {
          assert BT.ValidQuery(BT.LookupQuery(key, res.value, newlookup));
          assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'),
            UI.GetOp(key, res.value),
            M.IDiskOp(diskOp(io)),
            BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
          assert stepsBetree(k, IVars(s), IVars(s'),
            if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
            BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
        } else {
          if node.children.Some? {
            lemmaChildInGraph(k, s', ref, node.children.value[r]);
            queryIterateCorrect(k, s', key, newmsg, node.children.value[r], io, counter - 1,
                newlookup);
          } else {
            assert BC.OpTransaction(Ik(k), IVars(s), IVars(s'),
              PBS.BetreeStepOps(BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup))));

            assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'),
              if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
              M.IDiskOp(diskOp(io)),
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));

            assert stepsBetree(k, IVars(s), IVars(s'),
              if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
              BT.BetreeQuery(BT.LookupQuery(key, res.value, newlookup)));
          }
        }
      }
    }
  }

  lemma queryCorrect(k: Constants, s: Variables, io: IO, key: MS.Key)
  requires io.IOInit?
  requires Inv(k, s)
  ensures var (s', res, io') := query(k, s, io, key);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'),
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          diskOp(io'))
  {
    reveal_query();
    if (s.Unready?) {
      PageInIndirectionTableReqCorrect(k, s, io);
    } else {
      queryIterateCorrect(k, s, key, Messages.IdentityMessage(), BT.G.Root(), io, 40, []);
    }
  }
}
