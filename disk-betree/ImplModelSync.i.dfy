include "ImplModel.i.dfy"
include "ImplModelIO.i.dfy"
include "ImplModelSplit.i.dfy"
include "ImplModelFlush.i.dfy"
include "ImplModelFlushRootBucket.i.dfy"
include "ImplModelGrow.i.dfy"
include "ImplModelDealloc.i.dfy"
include "ImplModelLeaf.i.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplModelSync { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelSplit
  import opened ImplModelCache
  import opened ImplModelFlush
  import opened ImplModelFlushRootBucket
  import opened ImplModelDealloc
  import opened ImplModelGrow
  import opened ImplModelLeaf

  import IMM = ImplMarshallingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  lemma lemmaRefHasLoc(k: Constants, s: Variables, ref: BT.G.Reference)
  requires Inv(k, s)
  requires s.Ready?
  requires ref !in s.cache
  requires ref in s.ephemeralIndirectionTable
  ensures s.ephemeralIndirectionTable[ref].0.Some?;
  {
    assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph.Keys;
    assert ref in s.cache.Keys + IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;
    assert ref !in s.cache.Keys;
    assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;
  }

  function {:fuel JoinBucketList,0} fixBigNode(k: Constants, s: Variables, io: IO, ref: BT.G.Reference, parentref: BT.G.Reference)
  : (Variables, IO)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.ephemeralIndirectionTable
  requires ref in s.ephemeralIndirectionTable[parentref].1
  requires s.rootBucket == map[] // FIXME we don't actually need this I think
  requires ref != BT.G.Root()
  requires io.IOInit?
  {
    if (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[ref];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      (s, io)
    ) else (
      lemmaGraphChildInGraph(k, s, parentref, ref);
      assert s.ephemeralIndirectionTable[parentref].1
          == IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref];

      var node := s.cache[ref];
      if i :| 0 <= i < |node.buckets| && !IMM.CappedBucket(node.buckets[i]) then (
        if (node.children.Some?) then (
          // internal node case: flush
          flush(k, s, io, ref, i)
        ) else (
          // leaf case
          var s' := repivotLeaf(k, s, ref, i, node);
          (s', io)
        )
      ) else if |node.buckets| > IMM.CapNumBuckets() as int then (
        if (parentref !in s.cache) then (
          lemmaRefHasLoc(k, s, parentref);
          PageInReq(k, s, io, parentref)
        ) else (
          var parent := s.cache[parentref];

          assert ref in BT.G.Successors(INode(parent));

          var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;
          var s' := doSplit(k, s, parentref, ref, i);
          (s', io)
        )
      ) else (
        (s, io)
      )
    )
  }

  lemma {:fuel JoinBucketList,0} fixBigNodeCorrect(k: Constants, s: Variables, io: IO, ref: BT.G.Reference, parentref: BT.G.Reference)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.ephemeralIndirectionTable
  requires ref in s.ephemeralIndirectionTable[parentref].1
  requires s.rootBucket == map[] // FIXME we don't actually need this I think
  requires ref != BT.G.Root()
  requires io.IOInit?
  ensures var (s', io') := fixBigNode(k, s, io, ref, parentref);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var (s', io') := fixBigNode(k, s, io, ref, parentref);

    if (ref !in s.cache) {
      return;
    }
    if (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[ref];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s));
    }

    lemmaGraphChildInGraph(k, s, parentref, ref);
    assert s.ephemeralIndirectionTable[parentref].1
        == IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref];

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    if i :| 0 <= i < |node.buckets| && !IMM.CappedBucket(node.buckets[i]) {
      if (node.children.Some?) {
        flushCorrect(k, s, io, ref, i);
      } else {
        repivotLeafCorrect(k, s, ref, i, node);
      }
    } else if |node.buckets| > IMM.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        lemmaRefHasLoc(k, s, parentref);
        PageInReqCorrect(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      INodeRootEqINodeForEmptyRootBucket(parent);

      assert ref in BT.G.Successors(INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref
          && s' == doSplit(k, s, parentref, ref, i);
      doSplitCorrect(k, s, parentref, ref, i);

      return;
    } else {
      assert noop(k, IVars(s), IVars(s));
    }
  }

  /*
  method AssignRefToLBA(table: MutIndirectionTable, ref: Reference, loc: BC.Location)
  requires table.Inv()
  ensures table.Inv()
  ensures IIndirectionTable(table) == old(BC.assignRefToLocation(IIndirectionTable(table), ref, loc))
  {
    var locGraph := table.Remove(ref);
    if locGraph.Some? {
      var (_, graph) := locGraph.value;
      assume table.Count as nat < 0x10000000000000000 / 8;
      var _ := table.Insert(ref, (Some(loc), graph));
    }
    assert IIndirectionTable(table) ==
        old(BC.assignRefToLocation(IIndirectionTable(table), ref, loc));
  }

  method FindUncappedNodeInCache(s: Variables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value in s.cache && !Marshalling.CappedNode(s.cache[ref.value])
  ensures ref.None? ==> forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: r !in s.cache || Marshalling.CappedNode(s.cache[r])
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in IIndirectionTable(s.ephemeralIndirectionTable).graph
        && (ephemeralRefs[k] !in s.cache || Marshalling.CappedNode(s.cache[ephemeralRefs[k]])))
    {
      var ref := ephemeralRefs[i];
      if ref in s.cache && !Marshalling.CappedNode(s.cache[ref]) {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: r !in s.cache || Marshalling.CappedNode(s.cache[r]);
    return None;
  }

  method FindRefInFrozenWithNoLba(s: Variables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref.Some? ==> ref.value in IIndirectionTable(s.frozenIndirectionTable.value).graph 
  ensures ref.Some? ==> ref.value !in IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures ref.None? ==> forall r | r in IIndirectionTable(s.frozenIndirectionTable.value).graph
      :: r in IIndirectionTable(s.frozenIndirectionTable.value).locs
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(frozenTable.Keys);

    assume |frozenRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    invariant forall k : nat | k < i as nat :: (
        && frozenRefs[k] in IIndirectionTable(s.frozenIndirectionTable.value).graph
        && frozenRefs[k] in IIndirectionTable(s.frozenIndirectionTable.value).locs)
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
    assert forall r | r in IIndirectionTable(s.frozenIndirectionTable.value).graph
        :: r in IIndirectionTable(s.frozenIndirectionTable.value).locs;
    return None;
  }

  method FindRefNotPointingToRefInEphemeral(s: Variables, ref: Reference) returns (result: Reference)
  requires WFVars(s)
  requires s.Ready?
  requires exists r :: r in IIndirectionTable(s.ephemeralIndirectionTable).graph && 
      ref in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]
  ensures result in IIndirectionTable(s.ephemeralIndirectionTable).graph && 
      ref in IIndirectionTable(s.ephemeralIndirectionTable).graph[result]
  {
    assert s.ephemeralIndirectionTable.Inv();
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();

    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);
    assert forall k | k in ephemeralRefs :: k in ephemeralTable;

    assert forall k | k in ephemeralRefs :: k in IIndirectionTable(s.ephemeralIndirectionTable).graph; // TODO

    // TODO how do we deal with this?
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as nat < |ephemeralRefs|
    invariant i as nat <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        || ephemeralRefs[k] !in IIndirectionTable(s.ephemeralIndirectionTable).graph
        || ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[ephemeralRefs[k]])
    {
      var eRef := ephemeralRefs[i];
      assert eRef in IIndirectionTable(s.ephemeralIndirectionTable).graph;

      var lbaGraph := s.ephemeralIndirectionTable.Get(eRef);
      assert lbaGraph.Some?;

      var (_, graph) := lbaGraph.value;
      if ref in graph {
        assert eRef in IIndirectionTable(s.ephemeralIndirectionTable).graph && 
            ref in IIndirectionTable(s.ephemeralIndirectionTable).graph[eRef];
        return eRef;
      }

      i := i + 1;
    }
    assert false;
  }

  method {:fuel BC.GraphClosed,0} {:fueld BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: Constants, s: Variables, io: IO)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.None?
  ensures WFVars(s')
  ensures ImplADM.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, io.diskOp())
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
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph;
      assert ref in s.cache && !Marshalling.CappedNode(s.cache[foundUncapped.value]);
      if (ref == BT.G.Root()) {
        s' := fixBigRoot(k, s, io);
        return;
      } else {
        assert !deallocable(s, ref);
        assert !(forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph ::
            ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        assert !(forall r :: r in IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        assert (exists r :: !(r in IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]));
        var r := FindRefNotPointingToRefInEphemeral(s, ref);
        assert !(r in IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
        s' := fixBigNode(k, s, io, ref, r);
        return;
      }
    } else {
      var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();
      assert IIndirectionTable(clonedEphemeralIndirectionTable) == IIndirectionTable(s.ephemeralIndirectionTable); // observe

      s' := s
          .(frozenIndirectionTable := Some(clonedEphemeralIndirectionTable))
          .(syncReqs := BC.syncReqs3to2(s.syncReqs));

      assert BC.Freeze(Ik(k), IVars(s), IVars(s'), ImplADM.IDiskOp(io.diskOp()));
      assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, ImplADM.IDiskOp(io.diskOp()), BC.FreezeStep);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.FreezeStep);
      return;
    }
  }

  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: Constants, s: Variables, io: IO, ref: Reference)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.Some?
  requires ref in IIndirectionTable(s.frozenIndirectionTable.value).graph 
  requires ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures WFVars(s')
  ensures ImplADM.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, io.diskOp())
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if (!Marshalling.CappedNode(s.cache[ref])) {
      // TODO we should be able to prove this is impossible by adding an invariant
      // about frozenIndirectionTable (that is, we should never be freezing a table
      // with too-big nodes in it)
      s' := s;
      assert noop(k, IVars(s), IVars(s'));
      print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
      return;
    }

    var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
    if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      // TODO we should be able to prove this is impossible as well
      s' := s;
      assert noop(k, IVars(s), IVars(s'));
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    assert ref !in IIndirectionTable(s.ephemeralIndirectionTable).locs;

    INodeRootEqINodeForEmptyRootBucket(s.cache[ref]);
    var id, loc := FindLocationAndRequestWrite(s, io, SectorBlock(s.cache[ref]));
    if (id.Some?) {
      assert loc.value == ImplADM.IDiskOp(io.diskOp()).reqWrite.loc;
      /* (doc) assert reqWriteLoc.addr != BC.IndirectionTableLBA(); */
      /* (doc) assert BC.ValidAllocation(IVars(s), loc.value); */

      AssignRefToLBA(s.ephemeralIndirectionTable, ref, loc.value);
      assert IIndirectionTable(s.ephemeralIndirectionTable) ==
        BC.assignRefToLocation(IIndirectionTable(s.ephemeralIndirectionTable), ref, loc.value);
      AssignRefToLBA(s.frozenIndirectionTable.value, ref, loc.value);
      assert IIndirectionTable(s.frozenIndirectionTable.value) ==
        BC.assignRefToLocation(IIndirectionTable(s.frozenIndirectionTable.value), ref, loc.value);
      s' := s
        .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)]);

      assert BC.ValidLocationForNode(ImplADM.IDiskOp(io.diskOp()).reqWrite.loc);
      assert BC.WriteBackReq(Ik(k), IVars(s), IVars(s'), ImplADM.IDiskOp(io.diskOp()), ref);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackReqStep(ref));
      return;
    } else {
      s' := s;
      assert noop(k, IVars(s), IVars(s'));
      print "sync: giving up; write req failed\n";
      return;
    }
  }

  method {:fuel BC.GraphClosed,0} sync(k: Constants, s: Variables, io: IO)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  ensures WFVars(s')
  ensures ImplADM.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      assert noop(k, IVars(s), IVars(s'));
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
      assert noop(k, IVars(s), IVars(s'));
      print "sync: giving up; blocks are still being written\n";
      return;
    } else {
      LBAType.reveal_ValidAddr();
      var id := RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        assert BC.WriteBackIndirectionTableReq(Ik(k), IVars(s), IVars(s'), ImplADM.IDiskOp(io.diskOp()));
        assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableReqStep);
        return;
      } else {
        s' := s;
        assert noop(k, IVars(s), IVars(s'));
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

  method pushSync(k: Constants, s: Variables, io: IO)
  returns (s': Variables, id: int)
  requires io.initialized()
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  ensures WFVars(s')
  ensures ImplADM.Next(Ik(k), IVars(s), IVars(s'), UI.PushSyncOp(id), io.diskOp())
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    assert stepsBC(k, IVars(s), IVars(s'), UI.PushSyncOp(id), io, BC.PushSyncReqStep(id));
  }

  // == popSync ==

  method popSync(k: Constants, s: Variables, io: IO, id: int)
  returns (s': Variables, success: bool)
  requires io.initialized()
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  modifies io
  ensures WFVars(s')
  ensures ImplADM.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
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
