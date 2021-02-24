include "IOImpl.i.dfy"
include "DeallocImpl.i.dfy"
include "BookkeepingModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"

// See dependency graph in MainHandlers.dfy

module SyncImpl { 
  import opened NodeImpl
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DeallocImpl
  import opened Bounds
  import opened DiskLayout
  import BookkeepingModel
  import BlockAllocatorModel
  import opened DiskOpImpl
  import opened MainDiskIOHandler

  import opened Options
  import opened LinearOption
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened BucketsLib
  import opened NativeTypes

  import opened StateBCImpl
  import opened StateSectorImpl
  import opened DiskOpModel
  import IOModel
  import IT = IndirectionTable

  import opened InterpretationDiskOps
  import opened ViewOp

  lemma LemmaAssignRefToLocBitmapConsistent(
      indirectionTable: IT.IndirectionTable,
      bm: BitmapModel.BitmapModelT,
      indirectionTable': IT.IndirectionTable,
      bm': BitmapModel.BitmapModelT,
      ref: BT.G.Reference,
      loc: Location)
  requires indirectionTable.Inv()
  requires (forall i: int :: indirectionTable.I().IsLocAllocIndirectionTable(i)
          <==> IT.IndirectionTable.IsLocAllocBitmap(bm, i))
  requires ValidNodeLocation(loc);
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires ref in indirectionTable.graph
  requires ref !in indirectionTable.locs
  requires (indirectionTable', true) == indirectionTable.addLocIfPresent(ref, loc)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires BitmapModel.Len(bm) == NumBlocks()
  requires bm' == BitmapModel.BitSet(bm, loc.addr as int / NodeBlockSize())
  ensures (forall i: int :: indirectionTable'.I().IsLocAllocIndirectionTable(i)
          <==> IT.IndirectionTable.IsLocAllocBitmap(bm', i))
  {
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    //assert indirectionTable'.contents == indirectionTable.contents[ref := (Some(loc), indirectionTable.contents[ref].1)];

    var j := loc.addr as int / NodeBlockSize();
    reveal_ValidNodeAddr();
    assert j != 0;
    assert j * NodeBlockSize() == loc.addr as int;

    forall i: int | indirectionTable'.I().IsLocAllocIndirectionTable(i)
    ensures IT.IndirectionTable.IsLocAllocBitmap(bm', i)
    {
      if i == j {
        assert IT.IndirectionTable.IsLocAllocBitmap(bm', i);
      } else {
        assert indirectionTable.I().IsLocAllocIndirectionTable(i);
        assert IT.IndirectionTable.IsLocAllocBitmap(bm', i);
      }
    }
    forall i: int | IT.IndirectionTable.IsLocAllocBitmap(bm', i)
    ensures indirectionTable'.I().IsLocAllocIndirectionTable(i)
    {
      if i == j {
        assert ref in indirectionTable'.graph;
        assert ref in indirectionTable'.locs;
        assert indirectionTable'.locs[ref].addr as int == i * NodeBlockSize() as int;
        assert indirectionTable'.I().IsLocAllocIndirectionTable(i);
      } else {
        if 0 <= i < MinNodeBlockIndex() {
          assert indirectionTable'.I().IsLocAllocIndirectionTable(i);
        } else {
          assert indirectionTable.I().IsLocAllocIndirectionTable(i);
          var r :| r in indirectionTable.locs &&
            indirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            indirectionTable.I().locs,
            indirectionTable'.I().locs, r);
          assert r in indirectionTable'.locs &&
            indirectionTable'.locs[r].addr as int == i * NodeBlockSize() as int;
          assert indirectionTable'.I().IsLocAllocIndirectionTable(i);
        }
      }
    }
  }

  method AssignRefToLocEphemeral(linear inout s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires old_s.W() && old_s.Ready?
  requires old_s.ConsistentBitmap()

  requires ValidNodeLocation(loc);
  requires BlockAllocatorModel.Inv(old_s.blockAllocator.I())

  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()

  ensures s.W() && s.Ready?
  ensures s.ConsistentBitmap()
  ensures BlockAllocatorModel.Inv(s.blockAllocator.I())
  ensures var old_gs := old_s.I();
    s.I() == old_gs.(ephemeralIndirectionTable := BC.assignRefToLocation(old_gs.ephemeralIndirectionTable, ref, loc))
  {
    var added := inout s.ephemeralIndirectionTable.AddLocIfPresent(ref, loc);
    if added {
      inout s.blockAllocator.MarkUsedEphemeral(loc.addr / NodeBlockSizeUint64());
    }

    reveal_ConsistentBitmapInteral();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    ghost var j := loc.addr as int / NodeBlockSize();

    ghost var table := old_s.ephemeralIndirectionTable;
    if (ref in table.graph && ref !in table.locs) {
      assert added;

      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s.blockAllocator.I().full, i) == (
        || BitmapModel.IsSet(s.blockAllocator.I().ephemeral, i)
        || (s.blockAllocator.I().frozen.Some? && BitmapModel.IsSet(s.blockAllocator.I().frozen.value, i))
        || BitmapModel.IsSet(s.blockAllocator.I().persistent, i)
        || BitmapModel.IsSet(s.blockAllocator.I().full, i)
      )
      {
        if i != j {
          assert BitmapModel.IsSet(s.blockAllocator.I().full, i) == BitmapModel.IsSet(old_s.blockAllocator.I().full, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().ephemeral, i) == BitmapModel.IsSet(old_s.blockAllocator.I().ephemeral, i);
          assert s.blockAllocator.I().frozen.Some? ==> BitmapModel.IsSet(s.blockAllocator.I().frozen.value, i) == BitmapModel.IsSet(old_s.blockAllocator.I().frozen.value, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().persistent, i) == BitmapModel.IsSet(old_s.blockAllocator.I().persistent, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().outstanding, i) == BitmapModel.IsSet(old_s.blockAllocator.I().outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
          old_s.ephemeralIndirectionTable,
          old_s.blockAllocator.I().ephemeral,
          s.ephemeralIndirectionTable, 
          s.blockAllocator.I().ephemeral,
          ref,
          loc);
    } else {
      assert !added; // observe
    }
  }

  method AssignRefToLocFrozen(linear inout s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires old_s.W() && old_s.Ready?
  requires old_s.frozenIndirectionTable.lSome?
  requires BlockAllocatorModel.Inv(old_s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  requires ValidNodeLocation(loc);
  requires old_s.ConsistentBitmap()

  ensures s.W() && s.Ready?
  ensures s.frozenIndirectionTable.lSome?
  ensures s.ConsistentBitmap()
  ensures BlockAllocatorModel.Inv(s.blockAllocator.I())
  ensures var old_gs := old_s.I();
    s.I() == old_gs.(frozenIndirectionTable := Some(BC.assignRefToLocation(old_gs.frozenIndirectionTable.value, ref, loc)))
  {
    reveal_ConsistentBitmapInteral();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    ghost var j := loc.addr as int / NodeBlockSize();

    var added := inout s.frozenIndirectionTable.value.AddLocIfPresent(ref, loc);
    if added {
      inout s.blockAllocator.MarkUsedFrozen(loc.addr / NodeBlockSizeUint64());

      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s.blockAllocator.I().full, i) == (
        || BitmapModel.IsSet(s.blockAllocator.I().ephemeral, i)
        || (s.blockAllocator.I().frozen.Some? && BitmapModel.IsSet(s.blockAllocator.I().frozen.value, i))
        || BitmapModel.IsSet(s.blockAllocator.I().persistent, i)
        || BitmapModel.IsSet(s.blockAllocator.I().full, i)
      )
      {
        if i != j {
          assert BitmapModel.IsSet(s.blockAllocator.I().full, i) == BitmapModel.IsSet(old_s.blockAllocator.I().full, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().ephemeral, i) == BitmapModel.IsSet(old_s.blockAllocator.I().ephemeral, i);
          assert s.blockAllocator.I().frozen.Some? ==> BitmapModel.IsSet(s.blockAllocator.I().frozen.value, i) == BitmapModel.IsSet(old_s.blockAllocator.I().frozen.value, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().persistent, i) == BitmapModel.IsSet(old_s.blockAllocator.I().persistent, i);
          assert BitmapModel.IsSet(s.blockAllocator.I().outstanding, i) == BitmapModel.IsSet(old_s.blockAllocator.I().outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
        old_s.frozenIndirectionTable.value,
        old_s.blockAllocator.I().frozen.value,
        s.frozenIndirectionTable.value,
        s.blockAllocator.I().frozen.value,
        ref,
        loc);

      assert (s.blockAllocator.frozen.lSome? <==> s.blockAllocator.I().frozen.Some?) by {
        reveal s.blockAllocator.I();
      }
    }
  }

  method AssignIdRefLocOutstanding(linear inout s: ImplVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location)
  requires old_s.W() && old_s.Ready?
  requires BlockAllocatorModel.Inv(old_s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()

  requires old_s.ConsistentBitmap()

  requires ValidNodeLocation(loc);
  requires BC.AllOutstandingBlockWritesDontOverlap(old_s.outstandingBlockWrites)
  requires BC.OutstandingWriteValidNodeLocation(old_s.outstandingBlockWrites)

  ensures s.W() && s.Ready?
  ensures s.ConsistentBitmap()

  ensures BlockAllocatorModel.Inv(s.blockAllocator.I())
  ensures var old_gs := old_s.I();
    s.I() == old_gs.(outstandingBlockWrites := old_gs.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)])
  {
    reveal_ConsistentBitmapInteral();

    BitmapModel.reveal_BitUnset();
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    if id in s.outstandingBlockWrites {
      var numBlocks := s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64();
      if numBlocks < NumBlocksUint64() {
        inout s.blockAllocator.MarkFreeOutstanding(numBlocks);
      }
    }
    inout s.outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];
    inout s.blockAllocator.MarkUsedOutstanding(loc.addr / NodeBlockSizeUint64());

    ghost var j := loc.addr as int / NodeBlockSize();
    reveal_ValidNodeAddr();
    assert j != 0;
    assert j * NodeBlockSize() == loc.addr as int;

    forall i: int
    | IsLocAllocOutstanding(s.outstandingBlockWrites, i)
    ensures IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i)
    {
      if id in old_s.outstandingBlockWrites && old_s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() < NumBlocks() && i == old_s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() {
        if i == j {
          assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i);
        } else {
          var id0 :| id0 in s.outstandingBlockWrites && s.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
          assert ValidNodeAddr(old_s.outstandingBlockWrites[id0].loc.addr);
          assert ValidNodeAddr(old_s.outstandingBlockWrites[id].loc.addr);
          assert old_s.outstandingBlockWrites[id0].loc.addr as int
              == i * NodeBlockSize() as int
              == old_s.outstandingBlockWrites[id].loc.addr as int;
          assert id == id0;
          assert false;
        }
      } else if i != j {
        assert IsLocAllocOutstanding(old_s.outstandingBlockWrites, i);
        assert IT.IndirectionTable.IsLocAllocBitmap(old_s.blockAllocator.I().outstanding, i);
        assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i);
      } else {
        assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i);
      }
    }

    forall i: int
    | IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i)
    ensures IsLocAllocOutstanding(s.outstandingBlockWrites, i)
    {
      if i != j {
        assert IT.IndirectionTable.IsLocAllocBitmap(old_s.blockAllocator.I().outstanding, i);
        assert IsLocAllocOutstanding(old_s.outstandingBlockWrites, i);
        var id0 :| id0 in old_s.outstandingBlockWrites
          && old_s.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
        assert id0 != id;
        assert id0 in s.outstandingBlockWrites;
        assert s.outstandingBlockWrites[id0].loc.addr as int == i * NodeBlockSize() as int;
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
      } else {
        assert id in s.outstandingBlockWrites;
        assert s.outstandingBlockWrites[id].loc.addr as int == i * NodeBlockSize() as int;
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
      }
    }
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  maybeFreeze(linear inout s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool)
  requires io.initialized()
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.outstandingIndirectionTableWrite.None?
  requires old_s.frozenIndirectionTable.lNone?

  modifies io

  ensures s.W()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures froze ==> BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, FreezeOp)
  ensures !froze ==>
      || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
      || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.NoOp, true))
  {
    var foundDeallocable := FindDeallocable(s);
    if foundDeallocable.Some? {
      Dealloc(inout s, io, foundDeallocable.value);
      froze := false;
    } else {
      // [yizhou7]: is there a better way to perfrom this kind of assignment?
      linear var Ready(
        persistentIndirectionTable,
        frozenIndirectionTable,
        ephemeralIndirectionTable,
        persistentIndirectionTableLoc,
        frozenIndirectionTableLoc,
        outstandingIndirectionTableWrite,
        outstandingBlockWrites,
        outstandingBlockReads,
        cache,
        lru,
        blockAllocator) := s;

      linear var clonedEphemeralIndirectionTable := ephemeralIndirectionTable.Clone();
      dispose_lnone(frozenIndirectionTable);
      frozenIndirectionTable := lSome(clonedEphemeralIndirectionTable);

      s := Ready(
        persistentIndirectionTable,
        frozenIndirectionTable,
        ephemeralIndirectionTable,
        persistentIndirectionTableLoc,
        frozenIndirectionTableLoc,
        outstandingIndirectionTableWrite,
        outstandingBlockWrites,
        outstandingBlockReads,
        cache,
        lru,
        blockAllocator);

      inout s.blockAllocator.CopyEphemeralToFrozen();
      froze := true;

      assert BC.Freeze(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, FreezeOp);
      assert BBC.BlockCacheMove(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, FreezeOp, BC.FreezeStep);
      assert IOModel.stepsBC(old_s.I(), s.I(), FreezeOp, IIO(io), BC.FreezeStep);
    }
  }

  method TryToWriteBlock(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Ready? && old_s.Inv()
  requires io.initialized()
  requires ref in old_s.cache.I()
  requires old_s.outstandingIndirectionTableWrite.None?

  modifies io

  ensures s.W() && s.Ready?
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
  {
    linear var placeholder := Node.EmptyNode();
    linear var node := inout s.cache.ReplaceAndGet(ref, placeholder);
    linear var sector := SectorNode(node);
  
    assert |s.cache.I()| <= 0x10000;
    assert s.cache.ptr(ref).Some?;
    
    var id, loc := FindLocationAndRequestWrite(io, s, sector);

    linear var SectorNode(n) := sector;
    linear var replaced:= inout s.cache.ReplaceAndGet(ref, n);
    var _ := FreeNode(replaced);
    assert s.cache.I() == old_s.cache.I();

    if (id.Some?) {
      reveal_ConsistentBitmapInteral();

      AssignRefToLocEphemeral(inout s, ref, loc.value);
      AssignIdRefLocOutstanding(inout s, id.value, ref, loc.value);
      if s.frozenIndirectionTable.lSome? {
        AssignRefToLocFrozen(inout s, ref, loc.value);
      }

      assert ValidNodeLocation(IDiskOp(diskOp(IIO(io))).bdop.reqWriteNode.loc);
      assert BC.WriteBackNodeReq(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, ref);
      assert IOModel.stepsBC(old_s.I(), s.I(), StatesInternalOp, IIO(io), BC.WriteBackNodeReqStep(ref));
    } else {
      print "sync: giving up; write req failed\n";
      assert IOModel.noop(s.I(), s.I());
    }
  }

  // TODO fix the name of this method
  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(linear inout s: ImplVariables, io: DiskIOHandler, ref: Reference)
  requires io.initialized()
  requires old_s.Ready? && old_s.Inv()
  requires old_s.outstandingIndirectionTableWrite.None?
  requires old_s.frozenIndirectionTable.lSome?
  requires ref in old_s.frozenIndirectionTable.value.I().graph
  requires ref !in old_s.frozenIndirectionTable.value.I().locs
  modifies io
  ensures s.Ready? && s.W()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
  {
    assert ref in s.frozenIndirectionTable.value.I().graph;
    assert ref !in s.frozenIndirectionTable.value.I().locs;

    var ephemeralRef := s.ephemeralIndirectionTable.GetEntry(ref);
    if ephemeralRef.Some? && ephemeralRef.value.loc.Some? {
      // TODO we should be able to prove this is impossible as well
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      assert IOModel.noop(old_s.I(), s.I());
    } else {
      TryToWriteBlock(inout s, io, ref);
    }
  }

  method {:fuel BC.GraphClosed,0} sync(linear inout s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool, wait: bool)
  requires old_s.Ready? && old_s.Inv()
  requires io.initialized()

  modifies io

  ensures s.Ready? && s.W()
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures (froze ==> 
    BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, FreezeOp))
  ensures (!froze ==>
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp))
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.NoOp, true))
  {
    wait := false;
    froze := false;

    if s.frozenIndirectionTableLoc.Some? {
      //print "sync: waiting; frozen table is currently being written\n";
      wait := true;
      assert IOModel.noop(old_s.I(), s.I());
    } else if s.frozenIndirectionTable.lNone? {
      froze := maybeFreeze(inout s, io);
    } else {
      var foundInFrozen := inout s.frozenIndirectionTable.value.FindRefWithNoLoc();
      // ghost var s0 := s;

      assert s.Inv();

      if foundInFrozen.Some? {
        syncFoundInFrozen(inout s, io, foundInFrozen.value);
      } else if (s.outstandingBlockWrites != map[]) {
        //print "sync: waiting; blocks are still being written\n";
        wait := true;
        assert IOModel.noop(old_s.I(), s.I());
      } else {
        var id, loc := FindIndirectionTableLocationAndRequestWrite(
            io, s, SectorIndirectionTable(s.frozenIndirectionTable.value));

        if id.Some? {
          inout s.outstandingIndirectionTableWrite := id;
          inout s.frozenIndirectionTableLoc := loc;

          assert BC.WriteBackIndirectionTableReq(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp);
          assert IOModel.stepsBC(old_s.I(), s.I(), StatesInternalOp, IIO(io), BC.WriteBackIndirectionTableReqStep);
        } else {
          print "sync: giving up; write back indirection table failed (no id)\n";
          assert IOModel.noop(old_s.I(), s.I());
        }
      }
    }
  }
}
