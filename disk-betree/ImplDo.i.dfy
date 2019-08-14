include "Impl.i.dfy"
include "ImplSync.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplDo { 
  import opened Impl
  import opened ImplSync
  import opened ImplIO

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened BucketsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == pushSync ==

  method freeId<A>(syncReqs: map<int, A>) returns (id: int)
  ensures id !in syncReqs
  {
    var s := syncReqs.Keys;
    if (|s| == 0) {
      id := 0;
    } else {
      var maxId := maximumInt(syncReqs.Keys);
      id := maxId + 1;
    }
  }

  method pushSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables, id: int)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.PushSyncOp(id), io.diskOp())
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.PushSyncOp(id), io, BC.PushSyncReqStep(id));
  }

  // == popSync ==

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: int)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      success := true;
      s' := s.(syncReqs := MapRemove1(s.syncReqs, id));
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.PopSyncOp(id), io, BC.PopSyncReqStep(id));
    } else {
      success := false;
      s' := sync(k, s, io);
    }
  }

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
  requires BT.WFNode(IS.INode(node)) || BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.WFNode(IS.INode(node))
  ensures BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.NodeLookup(IS.INode(node), key) == BT.NodeLookup(IS.INodeRoot(node, rootBucket), key)
  {
    assume false;
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

  // == insert ==

  lemma LemmaInsertToRootBucket(node: IS.Node, rootBucket: IS.TreeMap, rootBucket': IS.TreeMap, key: Key, msg: Message)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires TTT.TTTree(rootBucket')
  requires TTT.I(rootBucket') == TTT.I(rootBucket)[key := msg]
  requires BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures IS.INodeRoot(node, rootBucket') == BT.AddMessageToNode(IS.INodeRoot(node, rootBucket), key, msg)
  {
    assume false;
  }

  method RemoveLBAFromIndirectionTable(table: IS.MutIndirectionTable, ref: IS.Reference)
  requires table.Inv()
  ensures table.Inv()
  ensures table.Contents == if ref in old(table.Contents)
      then old(
        var (_, graph) := table.Contents[ref];
        table.Contents[ref := (None, graph)])
      else old(table.Contents)
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  {
    var lbaGraph := table.Remove(ref);
    if lbaGraph.Some? {
      // TODO how do we deal with this?
      assume table.Count as nat < 0x10000000000000000 / 8;
      var (lba, graph) := lbaGraph.value;
      var _ := table.Insert(ref, (None, graph));
    }
  }

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if s.frozenIndirectionTable.Some? {
      var rootInFrozenLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if (
        && (s.frozenIndirectionTable.Some? && rootInFrozenLbaGraph.Some?)
        && rootInFrozenLbaGraph.value.0.None?
      ) {
        assert (s.frozenIndirectionTable.Some? && BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph) &&
            !(BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs);
        // TODO write out the root here instead of giving up
        s' := s;
        success := false;
        assert noop(k, IS.IVars(s), IS.IVars(s'));
        print "giving up; can't dirty root when frozen is not written yet\n";
        return;
      }
    }

    var msg := Messages.Define(value);

    ghost var baseroot := s.cache[BT.G.Root()];

    ghost var r := Pivots.Route(baseroot.pivotTable, key);
    ghost var bucket := baseroot.buckets[r];

    assert BC.BlockPointsToValidReferences(IS.INodeRoot(baseroot, s.rootBucket), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;

    ghost var iVarsBeforeRemoval := IS.IVars(s);

    label before_removal: assert true;

    RemoveLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root());

    assert IS.IVars(s) == iVarsBeforeRemoval.(ephemeralIndirectionTable := BC.IndirectionTable(
        MapRemove1(iVarsBeforeRemoval.ephemeralIndirectionTable.locs, BT.G.Root()),
        iVarsBeforeRemoval.ephemeralIndirectionTable.graph));

    s' := s.(rootBucket := newRootBucket);
    success := true;

    ghost var oldroot := IS.INodeRoot(baseroot, s.rootBucket);
    ghost var newroot := IS.INodeRoot(baseroot, newRootBucket);

    assert IS.IVars(s') == old@before_removal(IS.IVars(s) // timeout observe
        .(cache := IS.IVars(s).cache[BT.G.Root() := newroot])
        .(ephemeralIndirectionTable := BC.IndirectionTable(
          MapRemove1(IS.IVars(s).ephemeralIndirectionTable.locs, BT.G.Root()),
          IS.IVars(s).ephemeralIndirectionTable.graph
        )));

    LemmaInsertToRootBucket(baseroot, s.rootBucket, newRootBucket, key, msg);
    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    ghost var btStep := BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot));

    assert BC.Dirty(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.G.WriteOp(BT.G.Root(), newroot));
    assert BC.OpStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(btStep)[0]);
    assert BC.OpTransaction(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(btStep));
    assert BBC.BetreeMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.PutOp(key, value), SD.NoDiskOp, btStep);
    assert stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'), UI.PutOp(key, value), btStep);

    if success {
      assert ImplADM.M.NextStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp,
          ImplADM.M.Step(BBC.BetreeMoveStep(btStep)));
    }
    /* (doc) assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp); */
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      success := false;
      return;
    }

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      success := false;
      return;
    }

    s', success := InsertKeyValue(k, s, key, value);
    assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
      if success then UI.PutOp(key, value) else UI.NoOp,
      io.diskOp());
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<IS.Sector>) : Option<BC.Sector>
  requires sector.Some? ==> IS.WFSector(sector.value)
  reads if sector.Some? && sector.value.SectorIndirectionTable? then sector.value.indirectionTable.Repr else {}
  {
    match sector {
      case None => None
      case Some(sector) => Some(IS.ISector(sector))
    }
  }

  method ReadSector(io: DiskIOHandler)
  returns (id: D.ReqId, sector: Option<IS.Sector>)
  requires io.diskOp().RespReadOp?
  ensures sector.Some? ==> IS.WFSector(sector.value)
  ensures ImplADM.M.IDiskOp(io.diskOp()) == SD.RespReadOp(id, SD.RespRead(ISectorOpt(sector)))
  {
    Marshalling.reveal_parseCheckedSector();
    ImplADM.M.reveal_IBytes();
    ImplADM.M.reveal_ValidCheckedBytes();
    ImplADM.M.reveal_Parse();
    D.reveal_ChecksumChecksOut();

    var id1, bytes := io.getReadResult();
    id := id1;
    if |bytes| <= ImplADM.M.BlockSize() {
      var sectorOpt := Marshalling.ParseCheckedSector(bytes);
      sector := sectorOpt;
    } else {
      sector := None;
    }
  }

  method PageInIndirectionTableResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.diskOp().RespReadOp?
  requires s.Unready?
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var persistentIndirectionTable := sector.value.indirectionTable.Clone();
      var ephemeralIndirectionTable := sector.value.indirectionTable.Clone();
      s' := IS.Ready(persistentIndirectionTable, None, ephemeralIndirectionTable, None, map[], map[], s.syncReqs, map[], TTT.EmptyTree);
      assert IS.WFVars(s');
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableRespStep);
      assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp());
    } else {
      s' := s;
      assert ImplADM.M.NextStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp(), ImplADM.M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)));
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);

    if (id !in s.outstandingBlockReads) {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;
    
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if (lbaGraph.None? || lbaGraph.value.0.None? || ref in s.cache) { // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: ref !in lbas or ref in s.cache\n";
      return;
    }

    assert lbaGraph.Some? && lbaGraph.value.0.Some?;
    var lba := lbaGraph.value.0.value;
    var graph := lbaGraph.value.1;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.value.block])
               .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id));

        INodeRootEqINodeForEmptyRootBucket(node);

        assert BC.PageInResp(k, old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.PageInRespStep);
      } else {
        s' := s;
        assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "giving up; block read in was not block\n";
    }
  }

  method readResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableResp(k, s, io);
    } else {
      s' := PageInResp(k, s, io);
    }
  }

  // == writeResponse ==

  method writeResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespWriteOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id := io.getWriteResult();
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      s' := s.(outstandingIndirectionTableWrite := None)
             .(frozenIndirectionTable := None) // frozenIndirectiontable is moved to persistentIndirectionTable
             .(persistentIndirectionTable := s.frozenIndirectionTable.value)
             .(syncReqs := BC.syncReqs2to1(s.syncReqs));
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      s' := s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id));
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.WriteBackRespStep);
    } else {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
    }
  }

}
