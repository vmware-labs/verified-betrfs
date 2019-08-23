include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplSplit.i.dfy"
include "ImplFlush.i.dfy"
include "ImplFlushRootBucket.i.dfy"
include "ImplGrow.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplLeaf.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplSync { 
  import opened Impl
  import opened ImplIO
  import opened ImplSplit
  import opened ImplCache
  import opened ImplFlush
  import opened ImplFlushRootBucket
  import opened ImplDealloc
  import opened ImplGrow
  import opened ImplLeaf

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method {:fuel JoinBucketList,0} fixBigNode(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires ref in s.cache
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref]
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this I think
  requires ref != BT.G.Root()
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if (ref !in s.cache) {
      s' := PageInReq(k, s, io, ref);
      return;
    }

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs;
          s' := s;
          assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
          print "giving up; fixBigNode can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    if i :| 0 <= i < |node.buckets| && !Marshalling.CappedBucket(node.buckets[i]) {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i);
        return;
      } else {
        // leaf case
        s' := repivotLeaf(k, s, io, ref, i, node);
        return;
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageInReq(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      INodeRootEqINodeForEmptyRootBucket(parent);

      assert ref in BT.G.Successors(IS.INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
      return;
    } else {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; fixBigNode\n";
      return;
    }
  }

  method AssignRefToLBA(table: IS.MutIndirectionTable, ref: IS.Reference, loc: BC.Location)
  requires table.Inv()
  ensures table.Inv()
  ensures IS.IIndirectionTable(table) == old(BC.assignRefToLocation(IS.IIndirectionTable(table), ref, loc))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  {
    var locGraph := table.Remove(ref);
    if locGraph.Some? {
      var (_, graph) := locGraph.value;
      assume table.Count as nat < 0x10000000000000000 / 8;
      var _ := table.Insert(ref, (Some(loc), graph));
    }
    assert IS.IIndirectionTable(table) ==
        old(BC.assignRefToLocation(IS.IIndirectionTable(table), ref, loc));
  }

  method FindUncappedNodeInCache(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value in s.cache && !Marshalling.CappedNode(s.cache[ref.value])
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r !in s.cache || Marshalling.CappedNode(s.cache[r])
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
        && (ephemeralRefs[k] !in s.cache || Marshalling.CappedNode(s.cache[ephemeralRefs[k]])))
    {
      var ref := ephemeralRefs[i];
      if ref in s.cache && !Marshalling.CappedNode(s.cache[ref]) {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r !in s.cache || Marshalling.CappedNode(s.cache[r]);
    return None;
  }

  method FindRefInFrozenWithNoLba(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph 
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
      :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(frozenTable.Keys);

    assume |frozenRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    invariant forall k : nat | k < i as nat :: (
        && frozenRefs[k] in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
        && frozenRefs[k] in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs)
    {
      var ref := frozenRefs[i];
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      if lba.None? {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
        :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs;
    return None;
  }

  method FindRefNotPointingToRefInEphemeral(s: ImplVariables, ref: IS.Reference) returns (result: IS.Reference)
  requires IS.WFVars(s)
  requires s.Ready?
  requires exists r :: r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph && 
      ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]
  ensures result in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph && 
      ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[result]
  {
    assert s.ephemeralIndirectionTable.Inv();
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();

    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);
    assert forall k | k in ephemeralRefs :: k in ephemeralTable;

    assert forall k | k in ephemeralRefs :: k in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph; // TODO

    // TODO how do we deal with this?
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as nat < |ephemeralRefs|
    invariant i as nat <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        || ephemeralRefs[k] !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
        || ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[ephemeralRefs[k]])
    {
      var eRef := ephemeralRefs[i];
      assert eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;

      var lbaGraph := s.ephemeralIndirectionTable.Get(eRef);
      assert lbaGraph.Some?;

      var (_, graph) := lbaGraph.value;
      if ref in graph {
        assert eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph && 
            ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[eRef];
        return eRef;
      }

      i := i + 1;
    }
    assert false;
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.None?
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
    var foundDeallocable := FindDeallocable(s);
    if foundDeallocable.Some? {
      s' := Dealloc(k, s, io, foundDeallocable.value);
      return;
    }
    var foundUncapped := FindUncappedNodeInCache(s);
    if foundUncapped.Some? {
      var ref := foundUncapped.value;
      assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
      assert ref in s.cache && !Marshalling.CappedNode(s.cache[foundUncapped.value]);
      if (ref == BT.G.Root()) {
        s' := fixBigRoot(k, s, io);
        return;
      } else {
        assert !deallocable(s, ref);
        assert !(forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ::
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        assert !(forall r :: r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        assert (exists r :: !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]));
        var r := FindRefNotPointingToRefInEphemeral(s, ref);
        assert !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        s' := fixBigNode(k, s, io, ref, r);
        return;
      }
    } else {
      var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();
      assert IS.IIndirectionTable(clonedEphemeralIndirectionTable) == IS.IIndirectionTable(s.ephemeralIndirectionTable); // observe

      s' := s
          .(frozenIndirectionTable := Some(clonedEphemeralIndirectionTable))
          .(syncReqs := BC.syncReqs3to2(s.syncReqs));

      assert BC.Freeze(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
      assert BBC.BlockCacheMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, ImplADM.M.IDiskOp(io.diskOp()), BC.FreezeStep);
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.FreezeStep);
      return;
    }
  }

  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: IS.Reference)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.Some?
  requires ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph 
  requires ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? then s.frozenIndirectionTable.value.Repr else {}
  {
    assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if (!Marshalling.CappedNode(s.cache[ref])) {
      // TODO we should be able to prove this is impossible by adding an invariant
      // about frozenIndirectionTable (that is, we should never be freezing a table
      // with too-big nodes in it)
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
      return;
    }

    var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
    if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
      assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).locs;
      // TODO we should be able to prove this is impossible as well
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    assert ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).locs;

    INodeRootEqINodeForEmptyRootBucket(s.cache[ref]);
    var id, loc := FindLocationAndRequestWrite(s, io, IS.SectorBlock(s.cache[ref]));
    if (id.Some?) {
      assert loc.value == ImplADM.M.IDiskOp(io.diskOp()).reqWrite.loc;
      /* (doc) assert reqWriteLoc.addr != BC.IndirectionTableLBA(); */
      /* (doc) assert BC.ValidAllocation(old(IS.IVars(s)), loc.value); */

      AssignRefToLBA(s.ephemeralIndirectionTable, ref, loc.value);
      assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
        BC.assignRefToLocation(IS.IIndirectionTable(s.ephemeralIndirectionTable), ref, loc.value);
      AssignRefToLBA(s.frozenIndirectionTable.value, ref, loc.value);
      assert IS.IIndirectionTable(s.frozenIndirectionTable.value) ==
        BC.assignRefToLocation(IS.IIndirectionTable(s.frozenIndirectionTable.value), ref, loc.value);
      s' := s
        .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)]);

      assert BC.ValidLocationForNode(ImplADM.M.IDiskOp(io.diskOp()).reqWrite.loc);
      assert BC.WriteBackReq(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.WriteBackReqStep(ref));
      return;
    } else {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "sync: giving up; write req failed\n";
      return;
    }
  }

  method {:fuel BC.GraphClosed,0} sync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "sync: giving up; frozen table is currently being written\n";
      return;
    }

    if (s.rootBucket != TTT.EmptyTree) {
      s' := flushRootBucket(k, s, io);
      return;
    }

    // Plan:
    // - If the indirection table is not frozen then:
    //    - If anything can be unalloc'ed, do it
    //    - If any node is too big, do split/flush/whatever to shrink it
    //    - Freeze the indirection table
    // - Otherwise:
    //    - If any block in the frozen table doesn't have an LBA, Write it to disk
    //    - Write the frozenIndirectionTable to disk

    if (s.frozenIndirectionTable.None?) {
      s' := syncNotFrozen(k, s, io);
      return;
    }
    var foundInFrozen := FindRefInFrozenWithNoLba(s);
    if foundInFrozen.Some? {
      s' := syncFoundInFrozen(k, s, io, foundInFrozen.value);
      return;
    } else if (s.outstandingBlockWrites != map[]) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "sync: giving up; blocks are still being written\n";
      return;
    } else {
      LBAType.reveal_ValidAddr();
      var id := RequestWrite(io, BC.IndirectionTableLocation(), IS.SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        assert BC.WriteBackIndirectionTableReq(Ik(k), old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableReqStep);
        return;
      } else {
        s' := s;
        assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
        print "sync: giving up; write back indirection table failed (no id)\n";
        return;
      }
    }
  }

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

}
