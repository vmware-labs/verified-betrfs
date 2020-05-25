include "StateModel.i.dfy"
include "IOModel.i.dfy"
include "DeallocModel.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"

// See dependency graph in MainHandlers.dfy

module SyncModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened DeallocModel
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

//~  lemma lemmaRefHasLoc(k: Constants, s: BCVariables, ref: BT.G.Reference)
//~  requires BCInv(k, s)
//~  requires s.Ready?
//~  requires ref !in s.cache
//~  requires ref in s.ephemeralIndirectionTable.graph
//~  ensures ref in s.ephemeralIndirectionTable.locs
//~  {
//~    /*assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph.Keys;
//~    assert ref in s.cache.Keys + IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;
//~    assert ref !in s.cache.Keys;
//~    assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;*/
//~  }

  function {:opaque} AssignRefToLocEphemeral(k: Constants, s: BCVariables, ref: BT.G.Reference, loc: Location) : (s' : BCVariables)
  requires s.Ready?
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  ensures s'.Ready?
  ensures s'.frozenIndirectionTable == s.frozenIndirectionTable
  ensures s'.blockAllocator.frozen == s.blockAllocator.frozen
  ensures s'.outstandingBlockWrites == s.outstandingBlockWrites
  ensures BlockAllocatorModel.Inv(s'.blockAllocator)
  {
    var table := s.ephemeralIndirectionTable;
    var (table', added) := IndirectionTableModel.AddLocIfPresent(table, ref, loc);
    if added then (
      var blockAllocator' := BlockAllocatorModel.MarkUsedEphemeral(s.blockAllocator, loc.addr as int / NodeBlockSize());
      s.(ephemeralIndirectionTable := table')
       .(blockAllocator := blockAllocator')
    ) else (
      s.(ephemeralIndirectionTable := table')
    )
  }

  function {:opaque} AssignRefToLocFrozen(k: Constants, s: BCVariables, ref: BT.G.Reference, loc: Location) : (s' : BCVariables)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some? ==> IndirectionTableModel.Inv(s.frozenIndirectionTable.value)
  requires s.frozenIndirectionTable.Some? ==> s.blockAllocator.frozen.Some?
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  ensures s'.Ready?
  ensures s'.outstandingBlockWrites == s.outstandingBlockWrites
  ensures BlockAllocatorModel.Inv(s'.blockAllocator)
  {
    if s.frozenIndirectionTable.Some? then (
      var table := s.frozenIndirectionTable.value;
      var (table', added) := IndirectionTableModel.AddLocIfPresent(table, ref, loc);
      if added then (
        var blockAllocator' := BlockAllocatorModel.MarkUsedFrozen(s.blockAllocator, loc.addr as int / NodeBlockSize());
        s.(frozenIndirectionTable := Some(table'))
         .(blockAllocator := blockAllocator')
      ) else (
        s.(frozenIndirectionTable := Some(table'))
      )
    ) else (
      s
    )
  }

  function {:opaque} AssignIdRefLocOutstanding(k: Constants, s: BCVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location) : (s' : BCVariables)
  requires s.Ready?
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  {
    var blockAllocator0 := if id in s.outstandingBlockWrites && s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() < NumBlocks() then
      // This case shouldn't actually occur but it's annoying to prove from this point.
      // So I just chose to handle it instead.
      // Yeah, it's kind of annoying.
      BlockAllocatorModel.MarkFreeOutstanding(s.blockAllocator, s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize())
    else
      s.blockAllocator;

    var outstandingBlockWrites' := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];

    var blockAllocator' := BlockAllocatorModel.MarkUsedOutstanding(blockAllocator0, loc.addr as int / NodeBlockSize());

    s
      .(outstandingBlockWrites := outstandingBlockWrites')
      .(blockAllocator := blockAllocator')
  }

  lemma LemmaAssignIdRefLocOutstandingCorrect(k: Constants, s: BCVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location)
  requires s.Ready?
  requires (forall i: int :: IsLocAllocOutstanding(s.outstandingBlockWrites, i)
          <==> IsLocAllocBitmap(s.blockAllocator.outstanding, i))
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires ValidNodeLocation(loc);
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires BC.AllOutstandingBlockWritesDontOverlap(s.outstandingBlockWrites)
  requires BC.OutstandingWriteValidNodeLocation(s.outstandingBlockWrites)
  ensures var s' := AssignIdRefLocOutstanding(k, s, id, ref, loc);
      && s'.Ready?
      && (forall i: int :: IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.outstanding, i))
      && BlockAllocatorModel.Inv(s'.blockAllocator)
  {
    reveal_AssignIdRefLocOutstanding();
    BitmapModel.reveal_BitUnset();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    var s' := AssignIdRefLocOutstanding(k, s, id, ref, loc);

    var j := loc.addr as int / NodeBlockSize();
    reveal_ValidNodeAddr();
    assert j != 0;
    assert j * NodeBlockSize() == loc.addr as int;

    forall i: int
    | IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
    ensures IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
    {
      if id in s.outstandingBlockWrites && s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() < NumBlocks() && i == s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() {
        if i == j {
          assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
        } else {
          var id0 :| id0 in s'.outstandingBlockWrites && s'.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
          assert ValidNodeAddr(s.outstandingBlockWrites[id0].loc.addr);
          assert ValidNodeAddr(s.outstandingBlockWrites[id].loc.addr);
          assert s.outstandingBlockWrites[id0].loc.addr as int
              == i * NodeBlockSize() as int
              == s.outstandingBlockWrites[id].loc.addr as int;
          assert id == id0;
          assert false;
        }
      } else if i != j {
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
        assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
        assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
      } else {
        assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
      }
    }

    forall i: int
    | IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
    ensures IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
    {
      if i != j {
        assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
        var id0 :| id0 in s.outstandingBlockWrites
          && s.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
        assert id0 != id;
        assert id0 in s'.outstandingBlockWrites;
        assert s'.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
        assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
      } else {
        assert id in s'.outstandingBlockWrites;
        assert s'.outstandingBlockWrites[id].loc.addr as int == i * NodeBlockSize() as int;
        assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
      }
    }
  }

  lemma LemmaAssignRefToLocBitmapConsistent(
      indirectionTable: IndirectionTable,
      bm: BitmapModel.BitmapModelT,
      indirectionTable': IndirectionTable,
      bm': BitmapModel.BitmapModelT,
      ref: BT.G.Reference,
      loc: Location)
  requires IndirectionTableModel.Inv(indirectionTable)
  requires (forall i: int :: IsLocAllocIndirectionTable(indirectionTable, i)
          <==> IsLocAllocBitmap(bm, i))
  requires ValidNodeLocation(loc);
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires ref in indirectionTable.graph
  requires ref !in indirectionTable.locs
  requires (indirectionTable', true) == IndirectionTableModel.AddLocIfPresent(indirectionTable, ref, loc)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires BitmapModel.Len(bm) == NumBlocks()
  requires bm' == BitmapModel.BitSet(bm, loc.addr as int / NodeBlockSize())
  ensures 
      && (forall i: int :: IsLocAllocIndirectionTable(indirectionTable', i)
          <==> IsLocAllocBitmap(bm', i))
  {
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    //assert indirectionTable'.contents == indirectionTable.contents[ref := (Some(loc), indirectionTable.contents[ref].1)];

    var j := loc.addr as int / NodeBlockSize();
    reveal_ValidNodeAddr();
    assert j != 0;
    assert j * NodeBlockSize() == loc.addr as int;

    forall i: int | IsLocAllocIndirectionTable(indirectionTable', i)
    ensures IsLocAllocBitmap(bm', i)
    {
      if i == j {
        assert IsLocAllocBitmap(bm', i);
      } else {
        assert IsLocAllocIndirectionTable(indirectionTable, i);
        assert IsLocAllocBitmap(bm', i);
      }
    }
    forall i: int | IsLocAllocBitmap(bm', i)
    ensures IsLocAllocIndirectionTable(indirectionTable', i)
    {
      if i == j {
        assert ref in indirectionTable'.graph;
        assert ref in indirectionTable'.locs;
        assert indirectionTable'.locs[ref].addr as int == i * NodeBlockSize() as int;
        assert IsLocAllocIndirectionTable(indirectionTable', i);
      } else {
        if 0 <= i < MinNodeBlockIndex() {
          assert IsLocAllocIndirectionTable(indirectionTable', i);
        } else {
          assert IsLocAllocIndirectionTable(indirectionTable, i);
          var r :| r in indirectionTable.locs &&
            indirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            IIndirectionTable(indirectionTable).locs,
            IIndirectionTable(indirectionTable').locs, r);
          assert r in indirectionTable'.locs &&
            indirectionTable'.locs[r].addr as int == i * NodeBlockSize() as int;
          assert IsLocAllocIndirectionTable(indirectionTable', i);
        }
      }
    }
  }

  lemma LemmaAssignRefToLocEphemeralCorrect(k: Constants, s: BCVariables, ref: BT.G.Reference, loc: Location)
  requires s.Ready?
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  requires (forall i: int :: IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i)
          <==> IsLocAllocBitmap(s.blockAllocator.ephemeral, i))
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires ValidNodeLocation(loc);
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  ensures var s' := AssignRefToLocEphemeral(k, s, ref, loc);
      && s'.Ready?
      && (forall i: int :: IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.ephemeral, i))
      && BlockAllocatorModel.Inv(s'.blockAllocator)
  {
    reveal_AssignRefToLocEphemeral();
    reveal_ConsistentBitmap();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    var j := loc.addr as int / NodeBlockSize();

    var table := s.ephemeralIndirectionTable;
    if (ref in table.graph && ref !in table.locs) {
      var (table', added) := IndirectionTableModel.AddLocIfPresent(table, ref, loc);
      assert added;
      var blockAllocator' := BlockAllocatorModel.MarkUsedEphemeral(s.blockAllocator, loc.addr as int / NodeBlockSize());
      var s' := s
      .(ephemeralIndirectionTable := table')
      .(blockAllocator := blockAllocator');

      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s'.blockAllocator.full, i) == (
        || BitmapModel.IsSet(s'.blockAllocator.ephemeral, i)
        || (s'.blockAllocator.frozen.Some? && BitmapModel.IsSet(s'.blockAllocator.frozen.value, i))
        || BitmapModel.IsSet(s'.blockAllocator.persistent, i)
        || BitmapModel.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i != j {
          assert BitmapModel.IsSet(s'.blockAllocator.full, i) == BitmapModel.IsSet(s.blockAllocator.full, i);
          assert BitmapModel.IsSet(s'.blockAllocator.ephemeral, i) == BitmapModel.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> BitmapModel.IsSet(s'.blockAllocator.frozen.value, i) == BitmapModel.IsSet(s.blockAllocator.frozen.value, i);
          assert BitmapModel.IsSet(s'.blockAllocator.persistent, i) == BitmapModel.IsSet(s.blockAllocator.persistent, i);
          assert BitmapModel.IsSet(s'.blockAllocator.outstanding, i) == BitmapModel.IsSet(s.blockAllocator.outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
          s.ephemeralIndirectionTable,
          s.blockAllocator.ephemeral,
          s'.ephemeralIndirectionTable, 
          s'.blockAllocator.ephemeral,
          ref,
          loc);
    } else {
    }
  }

  lemma LemmaAssignRefToLocFrozenCorrect(k: Constants, s: BCVariables, ref: BT.G.Reference, loc: Location)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some? ==> IndirectionTableModel.Inv(s.frozenIndirectionTable.value)
  requires s.frozenIndirectionTable.Some? ==> s.blockAllocator.frozen.Some?
  requires s.frozenIndirectionTable.Some? ==>
        (forall i: int :: IsLocAllocIndirectionTable(s.frozenIndirectionTable.value, i)
          <==> IsLocAllocBitmap(s.blockAllocator.frozen.value, i))
  requires BlockAllocatorModel.Inv(s.blockAllocator)
  requires ValidNodeLocation(loc);
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  ensures var s' := AssignRefToLocFrozen(k, s, ref, loc);
      && s'.Ready?
      && (s'.frozenIndirectionTable.Some? ==> s'.blockAllocator.frozen.Some?)
      && (s'.frozenIndirectionTable.Some? ==>
          (forall i: int :: IsLocAllocIndirectionTable(s'.frozenIndirectionTable.value, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.frozen.value, i)))
      && BlockAllocatorModel.Inv(s'.blockAllocator)
  {
    reveal_AssignRefToLocFrozen();

    if s.frozenIndirectionTable.None? {
      return;
    }

    reveal_ConsistentBitmap();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    var j := loc.addr as int / NodeBlockSize();

    var table := s.frozenIndirectionTable.value;
    var (table', added) := IndirectionTableModel.AddLocIfPresent(table, ref, loc);
    if added {
      var blockAllocator' := BlockAllocatorModel.MarkUsedFrozen(s.blockAllocator, loc.addr as int / NodeBlockSize());
      var s' := s
        .(frozenIndirectionTable := Some(table'))
        .(blockAllocator := blockAllocator');

      assert s' == AssignRefToLocFrozen(k, s, ref, loc);

      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s'.blockAllocator.full, i) == (
        || BitmapModel.IsSet(s'.blockAllocator.frozen.value, i)
        || (s'.blockAllocator.frozen.Some? && BitmapModel.IsSet(s'.blockAllocator.frozen.value, i))
        || BitmapModel.IsSet(s'.blockAllocator.persistent, i)
        || BitmapModel.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i != j {
          assert BitmapModel.IsSet(s'.blockAllocator.full, i) == BitmapModel.IsSet(s.blockAllocator.full, i);
          assert BitmapModel.IsSet(s'.blockAllocator.ephemeral, i) == BitmapModel.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> BitmapModel.IsSet(s'.blockAllocator.frozen.value, i) == BitmapModel.IsSet(s.blockAllocator.frozen.value, i);
          assert BitmapModel.IsSet(s'.blockAllocator.persistent, i) == BitmapModel.IsSet(s.blockAllocator.persistent, i);
          assert BitmapModel.IsSet(s'.blockAllocator.outstanding, i) == BitmapModel.IsSet(s.blockAllocator.outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
          s.frozenIndirectionTable.value,
          s.blockAllocator.frozen.value,
          s'.frozenIndirectionTable.value,
          s'.blockAllocator.frozen.value,
          ref,
          loc);
    } else {
    }
  }

  function {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  maybeFreeze(k: Constants, s: BCVariables, io: IO)
  : (res: (BCVariables, IO, bool))
  requires io.IOInit?
  requires BCInv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.None?
  {
    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? then (
      var (s', io') := Dealloc(k, s, io, foundDeallocable.value);
      (s', io', false)
    ) else (
      var s' := s
          .(frozenIndirectionTable := Some(IndirectionTableModel.clone(s.ephemeralIndirectionTable)))
          .(blockAllocator := BlockAllocatorModel.CopyEphemeralToFrozen(s.blockAllocator));
      (s', io, true)
    )
  }

  lemma {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  maybeFreezeCorrect(k: Constants, s: BCVariables, io: IO)
  requires io.IOInit?
  requires BCInv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.None?

  ensures var (s', io', froze) := maybeFreeze(k, s, io);
    && WFBCVars(s')
    && ValidDiskOp(diskOp(io'))
    && IDiskOp(diskOp(io')).jdop.NoDiskOp?
    && (froze ==> BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, FreezeOp))
    && (!froze ==>
      || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
      || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
    )
  {
    var (s', io', froze) := maybeFreeze(k, s, io);

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? {
      DeallocCorrect(k, s, io, foundDeallocable.value);
      return;
    }

    reveal_ConsistentBitmap();
    assert WFBCVars(s');

    assert BC.Freeze(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, FreezeOp);
    assert BBC.BlockCacheMove(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, FreezeOp, BC.FreezeStep);
    assert stepsBC(k, IBlockCache(s), IBlockCache(s'), FreezeOp, io, BC.FreezeStep);
    return;
  }

  predicate WriteBlockUpdateState(k: Constants, s: BCVariables, ref: BT.G.Reference,
      id: Option<D.ReqId>, loc: Option<Location>, s': BCVariables)
  requires s.Ready?
  requires BCInv(k, s)
  requires loc.Some? ==> 0 <= loc.value.addr as int / NodeBlockSize() < NumBlocks()
  requires ref in s.cache
  {
    reveal_ConsistentBitmap();

    if id.Some? then (
      && loc.Some?
      && var s0 := AssignRefToLocEphemeral(k, s, ref, loc.value);
      && var s1 := AssignRefToLocFrozen(k, s0, ref, loc.value);
      && s' == AssignIdRefLocOutstanding(k, s1, id.value, ref, loc.value)
    ) else (
      && s' == s
    )
  }

  predicate TryToWriteBlock(k: Constants, s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires s.Ready?
  requires BCInv(k, s)
  requires io.IOInit?
  requires ref in s.cache
  {
    exists id, loc ::
      && FindLocationAndRequestWrite(io, s, SectorNode(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s')
  }

  lemma TryToWriteBlockCorrect(k: Constants, s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires TryToWriteBlock.requires(k, s, io, ref, s', io')
  requires TryToWriteBlock(k, s, io, ref, s', io')
  requires s.outstandingIndirectionTableWrite.None?
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
  {
    var id, loc :| 
      && FindLocationAndRequestWrite(io, s, SectorNode(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s');

    FindLocationAndRequestWriteCorrect(io, s, SectorNode(s.cache[ref]), id, loc, io');

    if id.Some? {
      reveal_ConsistentBitmap();
      reveal_AssignRefToLocEphemeral();
      reveal_AssignRefToLocFrozen();
      reveal_AssignIdRefLocOutstanding();

      var s0 := AssignRefToLocEphemeral(k, s, ref, loc.value);
      var s1 := AssignRefToLocFrozen(k, s0, ref, loc.value);

      LemmaAssignRefToLocEphemeralCorrect(k, s, ref, loc.value);
      LemmaAssignRefToLocFrozenCorrect(k, s0, ref, loc.value);
      LemmaAssignIdRefLocOutstandingCorrect(k, s1, id.value, ref, loc.value);
      
      if s.frozenIndirectionTable.Some? {
        assert IIndirectionTable(s'.frozenIndirectionTable.value)
          == BC.assignRefToLocation(IIndirectionTable(s.frozenIndirectionTable.value), ref, loc.value);
      }

      assert ValidNodeLocation(IDiskOp(diskOp(io')).bdop.reqWriteNode.loc);
      assert BC.WriteBackNodeReq(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp, ref);
      assert stepsBC(k, IBlockCache(s), IBlockCache(s'), StatesInternalOp, io', BC.WriteBackNodeReqStep(ref));
    } else {
      assert io == io';
      assert noop(k, IBlockCache(s), IBlockCache(s));
    }
  }

  predicate {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: Constants, s: BCVariables, io: IO, ref: Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires BCInv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.graph
  requires ref !in s.frozenIndirectionTable.value.locs
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable.locs then (
      // TODO we should be able to prove this is impossible as well
      && s' == s
      && io' == io
    ) else (
      TryToWriteBlock(k, s, io, ref, s', io')
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncFoundInFrozenCorrect(k: Constants, s: BCVariables, io: IO, ref: Reference,
      s': BCVariables, io': IO)
  requires io.IOInit?
  requires BCInv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.graph
  requires ref !in s.frozenIndirectionTable.value.locs

  requires syncFoundInFrozen(k, s, io, ref, s', io')

  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable.locs {
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert noop(k, IBlockCache(s), IBlockCache(s));
    } else {
      TryToWriteBlockCorrect(k, s, io, ref, s', io');
    }
  }

  predicate {:opaque} {:fuel BC.GraphClosed,0} sync(k: Constants, s: BCVariables, io: IO,
      s': BCVariables, io': IO, froze: bool)
  requires io.IOInit?
  requires BCInv(k, s)
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
        (s', io', froze) == maybeFreeze(k, s, io)
      ) else (
        var (frozen0, ref) := IndirectionTableModel.FindRefWithNoLoc(s.frozenIndirectionTable.value);
        var s0 := s.(frozenIndirectionTable := Some(frozen0));
        assert BCInv(k, s0) by { reveal_ConsistentBitmap(); }
        if ref.Some? then (
          syncFoundInFrozen(k, s0, io, ref.value, s', io')
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

  lemma {:fuel BC.GraphClosed,0} syncCorrect(k: Constants, s: BCVariables, io: IO,
      s': BCVariables, io': IO, froze: bool)
  requires io.IOInit?
  requires BCInv(k, s)
  requires s.Ready?

  requires sync(k, s, io, s', io', froze)

  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?

  ensures (froze ==> BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, FreezeOp))
  ensures (!froze ==>
    || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp))
    || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))

  ensures froze ==> s.frozenIndirectionTable.None?
  {
    reveal_sync();
    if s.frozenIndirectionTableLoc.Some? {
      assert noop(k, IBlockCache(s), IBlockCache(s));
    } else {
      if (s.frozenIndirectionTable.None?) {
        maybeFreezeCorrect(k, s, io);
      } else {
        var (frozen0, ref) := IndirectionTableModel.FindRefWithNoLoc(s.frozenIndirectionTable.value);
        var s0 := s.(frozenIndirectionTable := Some(frozen0));
        assert BCInv(k, s0) by { reveal_ConsistentBitmap(); }
        if ref.Some? {
          syncFoundInFrozenCorrect(k, s0, io, ref.value, s', io');
        } else if (s0.outstandingBlockWrites != map[]) {
          assert noop(k, IBlockCache(s), IBlockCache(s0));
        } else {
          if (diskOp(io').ReqWriteOp?) {
            var id := Some(diskOp(io').id);
            var loc := s'.frozenIndirectionTableLoc;
            FindIndirectionTableLocationAndRequestWriteCorrect(k,
                io, s0, SectorIndirectionTable(s0.frozenIndirectionTable.value),
                id, loc, io');
            assert BC.WriteBackIndirectionTableReq(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp);
            assert stepsBC(k, IBlockCache(s), IBlockCache(s'), StatesInternalOp, io', BC.WriteBackIndirectionTableReqStep);
          } else {
            assert noop(k, IBlockCache(s), IBlockCache(s));
          }
        }
      }
    }
  }
}
