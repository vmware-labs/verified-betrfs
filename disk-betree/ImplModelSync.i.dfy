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

  function method getUncappedBucket(buckets: seq<KMTable.KMTable>, i: int) : (res: Option<int>)
  requires 0 <= i <= |buckets|
  ensures res.Some? ==> i <= res.value < |buckets| && !IMM.CappedBucket(buckets[res.value])
  ensures res.None? ==> forall j | i <= j < |buckets| :: IMM.CappedBucket(buckets[j])
  decreases |buckets| - i
  {
    if i == |buckets| then None else (
      if !IMM.CappedBucket(buckets[i]) then Some(i) else getUncappedBucket(buckets, i + 1)
    )
  }

  function {:fuel JoinBucketList,0} {:opaque} fixBigNode(k: Constants, s: Variables, io: IO, ref: BT.G.Reference, parentref: BT.G.Reference)
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
      var i := getUncappedBucket(node.buckets, 0);
      if i.Some? then (
        if (node.children.Some?) then (
          // internal node case: flush
          flush(k, s, io, ref, i.value)
        ) else (
          // leaf case
          var s' := repivotLeaf(k, s, ref, i.value, node);
          (s', io)
        )
      ) else if |node.buckets| > IMM.CapNumBuckets() as int then (
        if (parentref !in s.cache) then (
          lemmaRefHasLoc(k, s, parentref);
          PageInReq(k, s, io, parentref)
        ) else (
          var parent := s.cache[parentref];

          assert ref in BT.G.Successors(INode(parent));

          var j := SeqIndex(parent.children.value, ref);
          var s' := doSplit(k, s, parentref, ref, j.value);
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
    reveal_fixBigNode();

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
      return;
    }

    lemmaGraphChildInGraph(k, s, parentref, ref);
    assert s.ephemeralIndirectionTable[parentref].1
        == IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref];

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    var i := getUncappedBucket(node.buckets, 0);
    if i.Some? {
      if (node.children.Some?) {
        flushCorrect(k, s, io, ref, i.value);
      } else {
        repivotLeafCorrect(k, s, ref, i.value, node);
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
      var j := SeqIndex(parent.children.value, ref);
      doSplitCorrect(k, s, parentref, ref, j.value);

      return;
    } else {
      assert noop(k, IVars(s), IVars(s));
    }
  }

  function {:opaque} AssignRefToLoc(table: IndirectionTable, ref: Reference, loc: BC.Location) : IndirectionTable
  {
    if (ref in table) then (
      table[ref := (Some(loc), table[ref].1)]
    ) else (
      table
    )
  }

  lemma AssignRefToLocCorrect(table: IndirectionTable, ref: Reference, loc: BC.Location)
  ensures var table' := AssignRefToLoc(table, ref, loc);
    IIndirectionTable(table') == BC.assignRefToLocation(IIndirectionTable(table), ref, loc)
  {
    reveal_AssignRefToLoc();
  }

  function {:opaque} FindUncappedNodeInCache(s: Variables) : (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?

  lemma FindUncappedNodeInCacheCorrect(s: Variables)
  requires WFVars(s)
  requires s.Ready?
  ensures var ref := FindUncappedNodeInCache(s);
    && (ref.Some? ==> ref.value in s.ephemeralIndirectionTable)
    && (ref.Some? ==> ref.value in s.cache && !IMM.CappedNode(s.cache[ref.value]))
    && (ref.None? ==> forall r | r in s.ephemeralIndirectionTable :: r !in s.cache || IMM.CappedNode(s.cache[r]))

  function {:opaque} FindRefInFrozenWithNoLoc(s: Variables) : (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?

  lemma FindRefInFrozenWithNoLocCorrect(s: Variables)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures var ref := FindRefInFrozenWithNoLoc(s);
    && (ref.Some? ==> ref.value in s.frozenIndirectionTable.value)
    && (ref.Some? ==> s.frozenIndirectionTable.value[ref.value].0.None?)
    && (ref.None? ==> forall r | r in s.frozenIndirectionTable.value
        :: s.frozenIndirectionTable.value[r].0.Some?)

  function {:opaque} FindParentRef(s: Variables, ref: Reference) : (parentref: Reference)
  requires WFVars(s)
  requires s.Ready?

  lemma FindParentRefCorrect(s: Variables, ref: Reference)
  requires WFVars(s)
  requires s.Ready?
  ensures var parentref := FindParentRef(s, ref);
    && parentref in IIndirectionTable(s.ephemeralIndirectionTable).graph
    && ref in IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref]

  function {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: Constants, s: Variables, io: IO)
  : (res: (Variables, IO))
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == map[]
  requires s.frozenIndirectionTable.None?
  {
    var ephemeralTable := s.ephemeralIndirectionTable;
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? then (
      Dealloc(k, s, io, foundDeallocable.value)
    ) else (
      var foundUncapped := FindUncappedNodeInCache(s);
      FindUncappedNodeInCacheCorrect(s);
      if foundUncapped.Some? then (
        var ref := foundUncapped.value;
        if (ref == BT.G.Root()) then (
          fixBigRoot(k, s, io)
        ) else (
          var r := FindParentRef(s, ref);
          FindParentRefCorrect(s, ref);

          fixBigNode(k, s, io, ref, r)
        )
      ) else (
        var s' := s
            .(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
            .(syncReqs := BC.syncReqs3to2(s.syncReqs));
        (s', io)
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozenCorrect(k: Constants, s: Variables, io: IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == map[]
  requires s.frozenIndirectionTable.None?

  ensures var (s', io') := syncNotFrozen(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var (s', io') := syncNotFrozen(k, s, io);

    var ephemeralTable := s.ephemeralIndirectionTable;
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? {
      DeallocCorrect(k, s, io, foundDeallocable.value);
      return;
    }
    var foundUncapped := FindUncappedNodeInCache(s);
    FindUncappedNodeInCacheCorrect(s);
    if foundUncapped.Some? {
      var ref := foundUncapped.value;
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph;
      assert ref in s.cache && !IMM.CappedNode(s.cache[foundUncapped.value]);
      if (ref == BT.G.Root()) {
        fixBigRootCorrect(k, s, io);
        return;
      } else {
        var r := FindParentRef(s, ref);
        FindParentRefCorrect(s, ref);
        fixBigNodeCorrect(k, s, io, ref, r);
        return;
      }
    } else {
      assert BC.Freeze(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
      assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(diskOp(io')), BC.FreezeStep);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.FreezeStep);
      return;
    }
  }

  predicate {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == map[]
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value
  requires s.frozenIndirectionTable.value[ref].0.None?
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if (!IMM.CappedNode(s.cache[ref])) then (
      // TODO we should be able to prove this is impossible by adding an invariant
      // about frozenIndirectionTable (that is, we should never be freezing a table
      // with too-big nodes in it)
      && s' == s
      && io' == io
    ) else (
      if ref in s.ephemeralIndirectionTable && s.ephemeralIndirectionTable[ref].0.Some? then (
        // TODO we should be able to prove this is impossible as well
        && s' == s
        && io' == io
      ) else (
        if diskOp(io').ReqWriteOp? && s'.Ready? && ref in s'.ephemeralIndirectionTable && s'.ephemeralIndirectionTable[ref].0.Some? then (
          var id := Some(diskOp(io').id);
          var loc := s'.ephemeralIndirectionTable[ref].0;
          && FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]), id, loc, io')

          && s' == s
            .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)])
            .(ephemeralIndirectionTable := AssignRefToLoc(s.ephemeralIndirectionTable, ref, loc.value))
            .(frozenIndirectionTable := Some(AssignRefToLoc(s.frozenIndirectionTable.value, ref, loc.value)))
        ) else (
          && s' == s
          && io' == io
        )
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncFoundInFrozenCorrect(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == map[]
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value
  requires s.frozenIndirectionTable.value[ref].0.None?

  requires syncFoundInFrozen(k, s, io, ref, s', io')

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if (!IMM.CappedNode(s.cache[ref])) {
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    if ref in s.ephemeralIndirectionTable && s.ephemeralIndirectionTable[ref].0.Some? {
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    assert ref !in IIndirectionTable(s.ephemeralIndirectionTable).locs;

    INodeRootEqINodeForEmptyRootBucket(s.cache[ref]);

    if diskOp(io').ReqWriteOp? && s'.Ready? && ref in s'.ephemeralIndirectionTable && s'.ephemeralIndirectionTable[ref].0.Some? {
      var id := Some(diskOp(io').id);
      var loc := s'.ephemeralIndirectionTable[ref].0;
      FindLocationAndRequestWriteCorrect(io, s, SectorBlock(s.cache[ref]), id, loc, io');

      AssignRefToLocCorrect(s.ephemeralIndirectionTable, ref, loc.value);
      AssignRefToLocCorrect(s.frozenIndirectionTable.value, ref, loc.value);

      assert BC.ValidLocationForNode(M.IDiskOp(diskOp(io')).reqWrite.loc);
      assert BC.WriteBackReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')), ref);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.WriteBackReqStep(ref));
    } else {
      assert noop(k, IVars(s), IVars(s));
    }
  }

  predicate {:opaque} {:fuel BC.GraphClosed,0} sync(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (s.Unready?) then (
      // TODO we could just do nothing here instead
      (s', io') == PageInIndirectionTableReq(k, s, io)
    ) else (
      if (s.outstandingIndirectionTableWrite.Some?) then (
        && s' == s
        && io' == io
      ) else (
        if (s.rootBucket != map[]) then (
          && s' == flushRootBucket(k, s)
          && io' == io
        ) else (
          // Plan:
          // - If the indirection table is not frozen then:
          //    - If anything can be unalloc'ed, do it
          //    - If any node is too big, do split/flush/whatever to shrink it
          //    - Freeze the indirection table
          // - Otherwise:
          //    - If any block in the frozen table doesn't have an LBA, Write it to disk
          //    - Write the frozenIndirectionTable to disk

          if (s.frozenIndirectionTable.None?) then (
            (s', io') == syncNotFrozen(k, s, io)
          ) else (
            var foundInFrozen := FindRefInFrozenWithNoLoc(s);
            FindRefInFrozenWithNoLocCorrect(s);
            if foundInFrozen.Some? then (
              syncFoundInFrozen(k, s, io, foundInFrozen.value, s', io')
            ) else if (s.outstandingBlockWrites != map[]) then (
              && s' == s
              && io' == io
            ) else (
              if (diskOp(io').ReqWriteOp?) then (
                var id := Some(diskOp(io').id);
                && RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value), id, io')
                && s' == s.(outstandingIndirectionTableWrite := id)
              ) else (
                && s' == s
                && io' == io
              )
            )
          )
        )
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncCorrect(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)

  requires sync(k, s, io, s', io')

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_sync();
    if (s.Unready?) {
      PageInIndirectionTableReqCorrect(k, s, io);
    } else {
      if (s.outstandingIndirectionTableWrite.Some?) {
        assert noop(k, IVars(s), IVars(s));
      } else {
        if (s.rootBucket != map[]) {
          flushRootBucketCorrect(k, s);
        } else {
          // Plan:
          // - If the indirection table is not frozen then:
          //    - If anything can be unalloc'ed, do it
          //    - If any node is too big, do split/flush/whatever to shrink it
          //    - Freeze the indirection table
          // - Otherwise:
          //    - If any block in the frozen table doesn't have an LBA, Write it to disk
          //    - Write the frozenIndirectionTable to disk

          if (s.frozenIndirectionTable.None?) {
            syncNotFrozenCorrect(k, s, io);
          } else {
            var foundInFrozen := FindRefInFrozenWithNoLoc(s);
            FindRefInFrozenWithNoLocCorrect(s);
            if foundInFrozen.Some? {
              syncFoundInFrozenCorrect(k, s, io, foundInFrozen.value, s', io');
            } else if (s.outstandingBlockWrites != map[]) {
              assert noop(k, IVars(s), IVars(s));
            } else {
              if (diskOp(io').ReqWriteOp?) {
                var id := Some(diskOp(io').id);
                LBAType.reveal_ValidAddr();
                RequestWriteCorrect(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value), id, io');
                assert BC.WriteBackIndirectionTableReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
                assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.WriteBackIndirectionTableReqStep);
              } else {
                assert noop(k, IVars(s), IVars(s));
              }
            }
          }
        }
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

  method pushSync(k: Constants, s: Variables, io: IO)
  returns (s': Variables, id: int)
  requires io.initialized()
  requires WFVars(s)
  requires BBC.Inv(k, IVars(s))
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.PushSyncOp(id), io.diskOp())
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
  ensures M.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
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
