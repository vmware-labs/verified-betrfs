include "BookkeepingModel.i.dfy"
include "IOModel.i.dfy"
include "DeallocModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"

// See dependency graph in MainHandlers.dfy

module SyncModel { 
  import opened IOModel
  import opened BookkeepingModel
  import opened DiskOpModel
  import opened Bounds
  import opened ViewOp
  import opened InterpretationDiskOps
  import opened DiskLayout

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  import opened StateSectorModel


  predicate WriteBlockUpdateState(s: BCVariables, ref: BT.G.Reference,
      id: Option<D.ReqId>, loc: Option<Location>, s': BCVariables)
  requires s.Ready?
  requires BCInv(s)
  requires loc.Some? ==> 0 <= loc.value.addr as int / NodeBlockSize() < NumBlocks()
  requires ref in s.cache
  {
    reveal_ConsistentBitmap();

    if id.Some? then (
      && loc.Some?
      && var s0 := AssignRefToLocEphemeral(s, ref, loc.value);
      && var s1 := AssignRefToLocFrozen(s0, ref, loc.value);
      && s' == AssignIdRefLocOutstanding(s1, id.value, ref, loc.value)
    ) else (
      && s' == s
    )
  }

  predicate TryToWriteBlock(s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires s.Ready?
  requires BCInv(s)
  requires io.IOInit?
  requires ref in s.cache
  {
    exists id, loc ::
      && FindLocationAndRequestWrite(io, s, SectorNode(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(s, ref, id, loc, s')
  }

  lemma TryToWriteBlockCorrect(s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires TryToWriteBlock.requires(s, io, ref, s', io')
  requires TryToWriteBlock(s, io, ref, s', io')
  requires s.outstandingIndirectionTableWrite.None?
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
  {
    var id, loc :| 
      && FindLocationAndRequestWrite(io, s, SectorNode(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(s, ref, id, loc, s');

    FindLocationAndRequestWriteCorrect(io, s, SectorNode(s.cache[ref]), id, loc, io');

    if id.Some? {
      reveal_ConsistentBitmap();
      reveal_AssignRefToLocEphemeral();
      reveal_AssignRefToLocFrozen();
      reveal_AssignIdRefLocOutstanding();

      var s0 := AssignRefToLocEphemeral(s, ref, loc.value);
      var s1 := AssignRefToLocFrozen(s0, ref, loc.value);

      LemmaAssignRefToLocEphemeralCorrect(s, ref, loc.value);
      LemmaAssignRefToLocFrozenCorrect(s0, ref, loc.value);
      LemmaAssignIdRefLocOutstandingCorrect(s1, id.value, ref, loc.value);
      
      if s.frozenIndirectionTable.Some? {
        assert s'.frozenIndirectionTable.value.I()
          == BC.assignRefToLocation(s.frozenIndirectionTable.value.I(), ref, loc.value);
      }

      assert ValidNodeLocation(IDiskOp(diskOp(io')).bdop.reqWriteNode.loc);
      assert BC.WriteBackNodeReq(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp, ref);
      assert stepsBC(IBlockCache(s), IBlockCache(s'), StatesInternalOp, io', BC.WriteBackNodeReqStep(ref));
    } else {
      assert io == io';
      assert noop(IBlockCache(s), IBlockCache(s));
    }
  }

  predicate {:fuel BC.GraphClosed,0} syncFoundInFrozen(s: BCVariables, io: IO, ref: Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires BCInv(s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.graph
  requires ref !in s.frozenIndirectionTable.value.locs
  {
    assert ref in s.frozenIndirectionTable.value.I().graph;
    assert ref !in s.frozenIndirectionTable.value.I().locs;

    if ref in s.ephemeralIndirectionTable.locs then (
      // TODO we should be able to prove this is impossible as well
      && s' == s
      && io' == io
    ) else (
      TryToWriteBlock(s, io, ref, s', io')
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncFoundInFrozenCorrect(s: BCVariables, io: IO, ref: Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires BCInv(s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.graph
  requires ref !in s.frozenIndirectionTable.value.locs

  requires syncFoundInFrozen(s, io, ref, s', io')

  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
  {
    assert ref in s.frozenIndirectionTable.value.I().graph;
    assert ref !in s.frozenIndirectionTable.value.I().locs;

    if ref in s.ephemeralIndirectionTable.locs {
      assert ref in s.ephemeralIndirectionTable.I().locs;
      assert noop(IBlockCache(s), IBlockCache(s));
    } else {
      TryToWriteBlockCorrect(s, io, ref, s', io');
    }
  }

  predicate {:opaque} {:fuel BC.GraphClosed,0} sync(s: BCVariables, io: IO,
      s': BCVariables, io': IO, froze: bool)
  requires io.IOInit?
  requires BCInv(s)
  requires s.Ready?
  {
    if s.frozenIndirectionTableLoc.Some? then (
      && s' == s
      && io' == io
      && froze == false
    ) else (
      // Plan:
      // - If the indirection table is not frozen then:
      //    - If anything can be unalloc'ed, do it
      // - Otherwise:
      //    - If any block in the frozen table doesn't have an LBA, Write it to disk
      //    - Write the frozenIndirectionTable to disk

      if (s.frozenIndirectionTable.None?) then (
        (s', io', froze) == maybeFreeze(s, io)
      ) else (
        var (frozen0, ref) := s.frozenIndirectionTable.value.findRefWithNoLoc();
        var s0 := s.(frozenIndirectionTable := Some(frozen0));
        assert BCInv(s0) by { reveal_ConsistentBitmap(); }
        if ref.Some? then (
          syncFoundInFrozen(s0, io, ref.value, s', io')
          && froze == false
        ) else if (s0.outstandingBlockWrites != map[]) then (
          && s' == s0
          && io' == io
          && froze == false
        ) else (
          if (diskOp(io').ReqWriteOp?) then (
            && s'.Ready?
            && var id := Some(diskOp(io').id);
            && var loc := s'.frozenIndirectionTableLoc;
            && FindIndirectionTableLocationAndRequestWrite(
                io, s0, SectorIndirectionTable(s0.frozenIndirectionTable.value),
                id, loc, io')
            && loc.Some?
            && s' ==
                s0.(outstandingIndirectionTableWrite := id)
                  .(frozenIndirectionTableLoc := loc)
            && froze == false
          ) else (
            && s' == s0
            && io' == io
            && froze == false
          )
        )
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncCorrect(s: BCVariables, io: IO,
      s': BCVariables, io': IO, froze: bool)
  requires io.IOInit?
  requires BCInv(s)
  requires s.Ready?

  requires sync(s, io, s', io', froze)

  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?

  ensures (froze ==> BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, FreezeOp))
  ensures (!froze ==>
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp))
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))

  ensures froze ==> s.frozenIndirectionTable.None?
  {
    reveal_sync();
    if s.frozenIndirectionTableLoc.Some? {
      assert noop(IBlockCache(s), IBlockCache(s));
    } else {
      if (s.frozenIndirectionTable.None?) {
        maybeFreezeCorrect(s, io);
      } else {
        var (frozen0, ref) := s.frozenIndirectionTable.value.findRefWithNoLoc();
        var s0 := s.(frozenIndirectionTable := Some(frozen0));
        assert BCInv(s0) by { reveal_ConsistentBitmap(); }
        if ref.Some? {
          syncFoundInFrozenCorrect(s0, io, ref.value, s', io');
        } else if (s0.outstandingBlockWrites != map[]) {
          assert noop(IBlockCache(s), IBlockCache(s0));
        } else {
          if (diskOp(io').ReqWriteOp?) {
            var id := Some(diskOp(io').id);
            var loc := s'.frozenIndirectionTableLoc;
            FindIndirectionTableLocationAndRequestWriteCorrect(
                io, s0, SectorIndirectionTable(s0.frozenIndirectionTable.value),
                id, loc, io');
            assert BC.WriteBackIndirectionTableReq(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp);
            assert stepsBC(IBlockCache(s), IBlockCache(s'), StatesInternalOp, io', BC.WriteBackIndirectionTableReqStep);
          } else {
            assert noop(IBlockCache(s), IBlockCache(s));
          }
        }
      }
    }
  }
}
