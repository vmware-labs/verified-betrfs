include "Impl.i.dfy"
include "ImplSync.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplQuery { 
  import opened Impl
  import opened ImplSync
  import opened ImplIO

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened BucketsLib
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == query ==

  method TryRootBucketLookup(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  modifies io
  ensures res.Some? ==> ImplADM.M.Next(Ik(k), old(IS.IVars(s)), old(IS.IVars(s)),
    UI.GetOp(key, res.value), io.diskOp())
  ensures res.None? ==> io.initialized()
  ensures res.None? ==> key !in TTT.I(s.rootBucket)
  {
    var qres := TTT.Query(s.rootBucket, key);
    if (qres.ValueForKey?) {
      assert qres.value.Define?;
      res := Some(qres.value.value);

      ghost var lookup := [BT.G.ReadOp(BT.G.Root(), IS.INodeRoot(s.cache[BT.G.Root()], s.rootBucket))];

      ghost var node := s.cache[BT.G.Root()];
      GetBucketListFlushEqMerge(TTT.I(s.rootBucket), KMTable.ISeq(node.buckets), node.pivotTable, key);
      assert BT.NodeLookup(IS.INodeRoot(node, s.rootBucket), key) == TTT.I(s.rootBucket)[key];

      assert BT.InterpretLookup(lookup, key) == TTT.I(s.rootBucket)[key]
          == qres.value;
      //assert BT.InterpretLookupAccountingForLeaf(lookup, key) == qres.value;

      //assert BT.ValidQuery(BT.LookupQuery(key, res.value, lookup));
      //assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s),
      //  UI.GetOp(key, res.value),
      //  ImplADM.M.IDiskOp(io.diskOp()),
      //  BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

      assert stepsBetree(k, IS.IVars(s), IS.IVars(s),
        UI.GetOp(key, res.value),
        BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

    } else {
      res := None;
    }
  }

  // note: I split this out because of sequence-related trigger loop problems
  ghost method AugmentLookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: MS.Key, cache: map<BT.G.Reference, BT.G.Node>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
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

  lemma NodeLookupIfNotInRootBucket(node: IS.Node, rootBucket: IS.TreeMap, key: Key)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires key !in TTT.I(rootBucket)
  requires BT.WFNode(IS.INode(node))
  ensures BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.NodeLookup(IS.INode(node), key) == BT.NodeLookup(IS.INodeRoot(node, rootBucket), key)
  {
    WFBucketListFlush(TTT.I(rootBucket), KMTable.ISeq(node.buckets), node.pivotTable);
    GetBucketListFlushEqMerge(TTT.I(rootBucket), KMTable.ISeq(node.buckets), node.pivotTable, key);
  }

  method query(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (s': ImplVariables, res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
    if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
    io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      res := None;
    } else {
      var ref := BT.G.Root();
      var msg := Messages.IdentityMessage();
      ghost var lookup := [];

      var rootLookup := TryRootBucketLookup(k, s, io, key);
      if (rootLookup.Some?) {
        s' := s;
        res := rootLookup;
        return;
      }

      // TODO if we have the acyclicity invariant, we can prove
      // termination without a bound like this.
      var loopBound := 40;
      ghost var exiting := false;

      while !msg.Define? && loopBound > 0
      invariant |lookup| == 0 ==> ref == BT.G.Root()
      invariant msg.Define? ==> |lookup| > 0
      invariant |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
      invariant !exiting && !msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.Some?
      invariant !exiting && !msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
      invariant forall i | 0 <= i < |lookup| :: lookup[i].ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
      invariant forall i | 0 <= i < |lookup| :: MapsTo(IS.ICache(s.cache, s.rootBucket), lookup[i].ref, lookup[i].node)
      invariant ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
      invariant !exiting ==> msg == BT.InterpretLookup(lookup, key)
      invariant io.initialized()
      invariant key !in TTT.I(s.rootBucket)
      {
        assert !exiting;
        loopBound := loopBound - 1;

        if (ref !in s.cache) {
          s' := PageInReq(k, s, io, ref);
          res := None;

          exiting := true;
          return;
        } else {
          var node := s.cache[ref];
          ghost var inode := IS.INodeForRef(s.cache, ref, s.rootBucket);
          lookup := AugmentLookup(lookup, ref, inode, key, IS.ICache(s.cache, s.rootBucket), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph); // ghost-y

          var r := Pivots.ComputeRoute(node.pivotTable, key);
          var bucket := node.buckets[r];

          if |bucket.keys| >= 0x8000_0000_0000_0000 {
            s' := s;
            res := None;
            assert noop(k, IS.IVars(s), IS.IVars(s'));
            print "giving up; kmgMsg too big\n";
            return;
          }

          var kmtMsg := KMTable.Query(bucket, key);

          var lookupMsg := if kmtMsg.Some? then kmtMsg.value else Messages.IdentityMessage();
          msg := Messages.Merge(msg, lookupMsg);

          NodeLookupIfNotInRootBucket(s.cache[BT.G.Root()], s.rootBucket, key);
          assert lookupMsg == BT.NodeLookup(inode, key);

          if (node.children.Some?) {
            var r1 := Pivots.ComputeRoute(node.pivotTable, key);
            ref := node.children.value[r1];
            assert ref in BT.G.Successors(inode);
            assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
          } else {
            if !msg.Define? {
              // Case where we reach leaf and find nothing
              s' := s;
              res := Some(MS.V.DefaultValue());

              assert BC.OpTransaction(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
                PBS.BetreeStepOps(BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup))));

              assert BBC.BetreeMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                ImplADM.M.IDiskOp(io.diskOp()),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

              assert stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'),
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

              exiting := true;
              return;
            }
          }
        }
      }

      if msg.Define? {
        s' := s;
        res := Some(msg.value);

        assert BT.ValidQuery(BT.LookupQuery(key, res.value, lookup));
        assert BBC.BetreeMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
          UI.GetOp(key, res.value),
          ImplADM.M.IDiskOp(io.diskOp()),
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
        assert stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'),
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
      } else {
        // loop bound exceeded; do nothing :/
        s' := s;
        res := None;

        assert noop(k, IS.IVars(s), IS.IVars(s'));
        print "giving up; did not reach Leaf or a Define\n";
      }
    }
  }
}
