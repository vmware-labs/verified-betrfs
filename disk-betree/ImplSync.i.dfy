include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplSplit.i.dfy"
include "ImplFlush.i.dfy"
include "ImplFlushRootBucket.i.dfy"
include "ImplGrow.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplLeaf.i.dfy"
include "ImplModelSync.i.dfy"
include "ImplModelCache.i.dfy"
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
  import ImplModelSync
  import ImplModelCache
  import ImplModelDealloc
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method {:fuel JoinBucketList,0} fixBigNode(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.cache
  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable)[parentref].1
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this I think
  requires ref != BT.G.Root()
  requires io.initialized()
  modifies io
  ensures WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelSync.fixBigNode(Ic(k), old(IVars(s)), old(IIO(io)), ref, parentref)
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelSync.reveal_fixBigNode();

    if (ref !in s.cache) {
      s' := PageInReq(k, s, io, ref);
      return;
    }

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; fixBigNode can't run because frozen isn't written";
          return;
        }
      }
    }

    ImplModelCache.lemmaGraphChildInGraph(Ic(k), IVars(s), parentref, ref);
    assert IIndirectionTable(s.ephemeralIndirectionTable)[parentref].1
        == IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph[parentref];

    var node := s.cache[ref];

    var i := ImplModelSync.getUncappedBucket(node.buckets, 0);
    if i.Some? {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i.value);
        return;
      } else {
        // leaf case
        s' := repivotLeaf(k, s, ref, i.value, node);
        return;
      }
    } else if |node.buckets| > IMM.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        ImplModelSync.lemmaRefHasLoc(Ic(k), IVars(s), parentref);
        s' := PageInReq(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      assert ref in BT.G.Successors(IM.INode(parent));
      var j := SeqIndex(parent.children.value, ref);

      s' := doSplit(k, s, parentref, ref, j.value);
      return;
    } else {
      s' := s;
      print "giving up; fixBigNode\n";
      return;
    }
  }

  method AssignRefToLoc(table: MutIndirectionTable, ref: Reference, loc: BC.Location)
  requires table.Inv()
  ensures table.Inv()
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  ensures table.Contents == ImplModelSync.AssignRefToLoc(old(table.Contents), ref, loc)
  {
    ImplModelSync.reveal_AssignRefToLoc();
    var locGraph := table.Remove(ref);
    if locGraph.Some? {
      var (_, graph) := locGraph.value;
      assume table.Count as nat < 0x10000000000000000 / 8;
      var _ := table.Insert(ref, (Some(loc), graph));
    }
    //assert IIndirectionTable(table) ==
    //    old(BC.assignRefToLocation(IIndirectionTable(table), ref, loc));
  }

  method FindUncappedNodeInCache(s: ImplVariables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  ensures ref == ImplModelSync.FindUncappedNodeInCache(IVars(s))
  {
    assume false;
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
        && (ephemeralRefs[k] !in s.cache || IMM.CappedNode(s.cache[ephemeralRefs[k]])))
    {
      var ref := ephemeralRefs[i];
      if ref in s.cache && !IMM.CappedNode(s.cache[ref]) {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph :: r !in s.cache || IMM.CappedNode(s.cache[r]);
    return None;
  }

  method FindRefInFrozenWithNoLoc(s: ImplVariables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref == ImplModelSync.FindRefInFrozenWithNoLoc(IVars(s))
  {
    assume false;
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(frozenTable.Keys);

    assume |frozenRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    invariant forall k : nat | k < i as nat :: (
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs)
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
    assert forall r | r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph
        :: r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs;
    return None;
  }

  method FindParentRef(s: ImplVariables, ref: Reference) returns (result: Reference)
  requires WFVars(s)
  requires s.Ready?
  ensures result == ImplModelSync.FindParentRef(IVars(s), ref)
  {
    assume false;
    assert s.ephemeralIndirectionTable.Inv();
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();

    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);
    assert forall k | k in ephemeralRefs :: k in ephemeralTable;

    assert forall k | k in ephemeralRefs :: k in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph; // TODO

    // TODO how do we deal with this?
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as nat < |ephemeralRefs|
    invariant i as nat <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        || ephemeralRefs[k] !in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph
        || ref !in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph[ephemeralRefs[k]])
    {
      var eRef := ephemeralRefs[i];
      assert eRef in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph;

      var lbaGraph := s.ephemeralIndirectionTable.Get(eRef);
      assert lbaGraph.Some?;

      var (_, graph) := lbaGraph.value;
      if ref in graph {
        assert eRef in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph && 
            ref in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph[eRef];
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
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.None?
  ensures WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelSync.syncNotFrozen(Ic(k), old(IVars(s)), old(IIO(io)))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
    var foundDeallocable := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(IVars(s));
    if foundDeallocable.Some? {
      s' := Dealloc(k, s, io, foundDeallocable.value);
      return;
    }
    var foundUncapped := FindUncappedNodeInCache(s);
    ImplModelSync.FindUncappedNodeInCacheCorrect(IVars(s));
    if foundUncapped.Some? {
      var ref := foundUncapped.value;
      if (ref == BT.G.Root()) {
        s' := fixBigRoot(k, s, io);
        return;
      } else {
        var r := FindParentRef(s, ref);
        ImplModelSync.FindParentRefCorrect(IVars(s), ref);

        s' := fixBigNode(k, s, io, ref, r);
        return;
      }
    } else {
      var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

      s' := s
          .(frozenIndirectionTable := Some(clonedEphemeralIndirectionTable))
          .(syncReqs := BC.syncReqs3to2(s.syncReqs));

      return;
    }
  }

  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: Reference)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.Contents
  requires s.frozenIndirectionTable.value.Contents[ref].0.None?
  ensures WVars(s')
  ensures ImplModelSync.syncFoundInFrozen(Ic(k), old(IVars(s)), old(IIO(io)), ref, IVars(s'), IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? then s.frozenIndirectionTable.value.Repr else {}
  {
    assert ref in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph;
    assert ref !in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs;

    if (!IMM.CappedNode(s.cache[ref])) {
      // TODO we should be able to prove this is impossible by adding an invariant
      // about frozenIndirectionTable (that is, we should never be freezing a table
      // with too-big nodes in it)
      s' := s;
      print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
      return;
    }

    var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
    if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
      // TODO we should be able to prove this is impossible as well
      s' := s;
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    var id, loc := FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]));

    if (id.Some?) {
      AssignRefToLoc(s.ephemeralIndirectionTable, ref, loc.value);
      AssignRefToLoc(s.frozenIndirectionTable.value, ref, loc.value);
      s' := s
        .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)]);

      assert id == Some(io.diskOp().id);
      ImplModelSync.reveal_AssignRefToLoc();
      assert loc == s'.frozenIndirectionTable.value.Contents[ref].0;
    } else {
      s' := s;
      print "sync: giving up; write req failed\n";
    }
  }

  method {:fuel BC.GraphClosed,0} rsync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  ensures WVars(s')
  ensures ImplModelSync.sync(Ic(k), old(IVars(s)), old(IIO(io)), IVars(s'), IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    ImplModelSync.reveal_sync();

    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      print "sync: giving up; frozen table is currently being written\n";
      return;
    }

    if (s.rootBucket != TTT.EmptyTree) {
      s' := flushRootBucket(k, s);
      return;
    }

    if (s.frozenIndirectionTable.None?) {
      s' := syncNotFrozen(k, s, io);
      return;
    }
    var foundInFrozen := FindRefInFrozenWithNoLoc(s);
    ImplModelSync.FindRefInFrozenWithNoLocCorrect(IVars(s));

    if foundInFrozen.Some? {
      s' := syncFoundInFrozen(k, s, io, foundInFrozen.value);
      return;
    } else if (s.outstandingBlockWrites != map[]) {
      s' := s;
      print "sync: giving up; blocks are still being written\n";
      return;
    } else {
      var id := RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        return;
      } else {
        s' := s;
        print "sync: giving up; write back indirection table failed (no id)\n";
        return;
      }
    }
  }

  /*

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
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  ensures WVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IVars(s)), IVars(s'), UI.PushSyncOp(id), io.diskOp())
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    assert stepsBC(k, IVars(s), IVars(s'), UI.PushSyncOp(id), io, BC.PushSyncReqStep(id));
  }

  // == popSync ==

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: int)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  modifies io
  ensures WVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IVars(s)), IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      success := true;
      s' := s.(syncReqs := MapRemove1(s.syncReqs, id));
      assert stepsBC(k, IVars(s), IVars(s'), UI.PopSyncOp(id), io, BC.PopSyncReqStep(id));
    } else {
      success := false;
      s' := sync(k, s, io);
    }
  }
  */
}
