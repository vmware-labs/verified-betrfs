include "ImplModel.i.dfy"
include "ImplModelIO.i.dfy"
include "ImplModelDealloc.i.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplModelSync { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened ImplModelDealloc

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

  function {:opaque} AssignRefToLoc(table: IndirectionTable, ref: Reference, loc: BC.Location) : IndirectionTable
  {
    if (ref in table && table[ref].0.None?) then (
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

  function {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: Constants, s: Variables, io: IO)
  : (res: (Variables, IO))
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.None?
  {
    var ephemeralTable := s.ephemeralIndirectionTable;
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? then (
      Dealloc(k, s, io, foundDeallocable.value)
    ) else (
      var s' := s
          .(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
          .(syncReqs := BC.syncReqs3to2(s.syncReqs));
      (s', io)
    )
  }

  lemma {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozenCorrect(k: Constants, s: Variables, io: IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
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
    assert BC.Freeze(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
    assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(diskOp(io')), BC.FreezeStep);
    assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.FreezeStep);
    return;
  }

  predicate WriteBlockUpdateState(k: Constants, s: Variables, ref: BT.G.Reference,
      id: Option<D.ReqId>, loc: Option<LBAType.Location>, s': Variables)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.cache
  {
    if id.Some? then (
      && loc.Some?
      && s' == s
        .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)])
        .(ephemeralIndirectionTable := AssignRefToLoc(s.ephemeralIndirectionTable, ref, loc.value))
        .(frozenIndirectionTable := if s.frozenIndirectionTable.Some?
            then Some(AssignRefToLoc(s.frozenIndirectionTable.value, ref, loc.value))
            else None)
    ) else (
      && s' == s
    )
  }

  predicate TryToWriteBlock(k: Constants, s: Variables, io: IO, ref: BT.G.Reference,
      s': Variables, io': IO)
  requires s.Ready?
  requires Inv(k, s)
  requires io.IOInit?
  requires ref in s.cache
  {
    exists id, loc ::
      && FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s')
  }

  lemma TryToWriteBlockCorrect(k: Constants, s: Variables, io: IO, ref: BT.G.Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires TryToWriteBlock.requires(k, s, io, ref, s', io')
  requires TryToWriteBlock(k, s, io, ref, s', io')
  requires s.outstandingIndirectionTableWrite.None?
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var id, loc :| 
      && FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s');

    FindLocationAndRequestWriteCorrect(io, s, SectorBlock(s.cache[ref]), id, loc, io');

    if id.Some? {
      AssignRefToLocCorrect(s.ephemeralIndirectionTable, ref, loc.value);
      if (s.frozenIndirectionTable.Some?) {
        AssignRefToLocCorrect(s.frozenIndirectionTable.value, ref, loc.value);
      }

      assert BC.ValidLocationForNode(M.IDiskOp(diskOp(io')).reqWrite.loc);
      assert BC.WriteBackReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')), ref);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.WriteBackReqStep(ref));
    } else {
      assert io == io';
      assert noop(k, IVars(s), IVars(s));
    }
  }

  predicate {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value
  requires s.frozenIndirectionTable.value[ref].0.None?
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable && s.ephemeralIndirectionTable[ref].0.Some? then (
      // TODO we should be able to prove this is impossible as well
      && s' == s
      && io' == io
    ) else (
      TryToWriteBlock(k, s, io, ref, s', io')
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncFoundInFrozenCorrect(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value
  requires s.frozenIndirectionTable.value[ref].0.None?

  requires syncFoundInFrozen(k, s, io, ref, s', io')

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable && s.ephemeralIndirectionTable[ref].0.Some? {
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert noop(k, IVars(s), IVars(s));
    } else {
      TryToWriteBlockCorrect(k, s, io, ref, s', io');
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
        // Plan:
        // - If the indirection table is not frozen then:
        //    - If anything can be unalloc'ed, do it
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

  // == pushSync ==

  function {:opaque} freeId<A>(syncReqs: map<int, A>) : (id: int)
  ensures id !in syncReqs
  {
    var s := syncReqs.Keys;
    if (|s| == 0) then (
      0
    ) else (
      var maxId := maximumInt(syncReqs.Keys);
      maximumIntCorrect(syncReqs.Keys);
      maxId + 1
    )
  }

  function pushSync(k: Constants, s: Variables)
  : (Variables, int)
  requires Inv(k,s )
  {
    var id := freeId(s.syncReqs);
    var s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    (s', id)
  }

  lemma pushSyncCorrect(k: Constants, s: Variables)
  requires Inv(k,s )
  ensures var (s', id) := pushSync(k, s);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.PushSyncOp(id), D.NoDiskOp)
  {
    var (s', id) := pushSync(k, s);
    assert M.NextStep(Ik(k), IVars(s), IVars(s'), UI.PushSyncOp(id), D.NoDiskOp, M.Step(BBC.BlockCacheMoveStep(BC.PushSyncReqStep(id))));
  }

  // == popSync ==

  predicate popSync(k: Constants, s: Variables, io: IO, id: int,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) then (
      && success == true
      && s' == s.(syncReqs := MapRemove1(s.syncReqs, id))
      && io' == io
    ) else (
      && success == false
      && sync(k, s, io, s', io')
    )
  }

  lemma popSyncCorrect(k: Constants, s: Variables, io: IO, id: int,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires popSync(k, s, io, id, s', success, io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, diskOp(io'))
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      assert stepsBC(k, IVars(s), IVars(s'), UI.PopSyncOp(id), io', BC.PopSyncReqStep(id));
    } else {
      syncCorrect(k, s, io, s', io');
    }
  }
}
