include "StateSectorImpl.i.dfy"
include "StateBCImpl.i.dfy"
include "IOModel.i.dfy"
include "MarshallingImpl.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "DiskOpImpl.i.dfy"

include "../lib/Base/LinearOption.i.dfy"
include "../lib/DataStructures/LruImpl.i.dfy"

module IOImpl { 
  import opened MainDiskIOHandler
  import opened NativeTypes
  import opened Options
  import opened LinearOption
  import opened MapRemove_s
  import opened NodeImpl
  import opened CacheImpl
  import opened DiskLayout
  import opened DiskOpImpl
  import opened InterpretationDiskOps
  import MarshallingImpl
  import IOModel
  import BucketsLib
  import LruModel
  import LruImpl
  import opened Bounds
  import MutableMapModel

  import StateBCModel
  import opened StateBCImpl

  import SSI = StateSectorImpl
  import SSM = StateSectorModel

  import opened ViewOp
  import opened DiskOpModel
  import BucketWeights
  import BlockJournalDisk
  import IMM = MarshallingModel

  predicate LocAvailable(s: ImplVariables, loc: Location, len: uint64)
  requires s.WFBCVars()
  {
    && s.Ready?
    && ValidNodeLocation(loc)
    && BC.ValidAllocation(s.IBlockCache(), loc)
    && loc.len == len
  }

  // TODO does ImplVariables make sense? Should it be a Variables? Or just the fields of a class we live in?
  method getFreeLoc(shared s: ImplVariables, len: uint64)
  returns (loc : Option<Location>)
  requires s.Ready?
  requires s.WFBCVars()
  requires len <= NodeBlockSizeUint64()
  ensures loc.Some? ==> LocAvailable(s, loc.value, len)
  {
    reveal_ConsistentBitmap();
    DiskLayout.reveal_ValidNodeAddr();

    var i := s.blockAllocator.Alloc();
    if i.Some? {
      loc := Some(Location((i.value * NodeBlockSizeUint64()), len));

      ghost var blockAllocatorI := s.blockAllocator.I();
      assert i.value as int == BlockAllocatorModel.Alloc(blockAllocatorI).value;

      BlockAllocatorModel.LemmaAllocResult(blockAllocatorI);
      assert !IT.IndirectionTable.IsLocAllocBitmap(blockAllocatorI.ephemeral, i.value as int);
      assert blockAllocatorI.frozen.Some? ==>
          !IT.IndirectionTable.IsLocAllocBitmap(blockAllocatorI.frozen.value, i.value as int);
      assert !IT.IndirectionTable.IsLocAllocBitmap(blockAllocatorI.persistent, i.value as int);
      assert !IT.IndirectionTable.IsLocAllocBitmap(blockAllocatorI.outstanding, i.value as int);
    } else {
      loc := None;
    }
  }

  method FreeSectorOpt(linear sector: lOption<SSI.Sector>)
  requires sector.lSome? ==> SSI.WFSector(sector.value)
  {
    linear match sector {
      case lSome(value) => { 
        value.Free();
      }
      case lNone() => {}
    }
  }

  method RequestWrite(io: DiskIOHandler, loc: Location, linear sector: SSI.Sector)
  returns (id: D.ReqId)
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires io.initialized()
  requires sector.SectorSuperblock?
  requires ValidSuperblockLocation(loc)
  
  // [yizhou7]: additional precondition
  requires ValidLocation(loc)

  modifies io
  ensures io.diskOp().ReqWriteOp? && io.diskOp().id == id
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures ValidSuperblock1Location(loc) ==>
    IDiskOp(diskOp(IIO(io))) == BlockJournalDisk.DiskOp(BlockDisk.NoDiskOp, JournalDisk.ReqWriteSuperblockOp(id, 0, JournalDisk.ReqWriteSuperblock(sector.superblock)))
  ensures ValidSuperblock2Location(loc) ==>
    IDiskOp(diskOp(IIO(io))) == BlockJournalDisk.DiskOp(BlockDisk.NoDiskOp, JournalDisk.ReqWriteSuperblockOp(id, 1, JournalDisk.ReqWriteSuperblock(sector.superblock)))
  {
    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
    id := io.write(loc.addr, bytes[..]);

    sector.Free();

    IMM.reveal_parseCheckedSector();
    IMM.reveal_parseSector();
    Marshalling.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();
  }

  method FindLocationAndRequestWrite(io: DiskIOHandler, shared s: ImplVariables, shared sector: SSI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.WFBCVars()
  requires s.Ready?
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires io.initialized()
  requires sector.SectorNode?

  modifies io

  ensures id.Some? ==> loc.Some? && io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> IIO(io) == old(IIO(io))
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures id.Some? ==> DiskLayout.ValidLocation(loc.value)
  ensures id.Some? ==> sector.SectorNode? ==> BC.ValidAllocation(s.IBlockCache(), loc.value)
  ensures id.Some? ==> sector.SectorNode? ==> DiskLayout.ValidNodeLocation(loc.value)
  ensures sector.SectorNode? ==> id.Some? ==> IDiskOp(diskOp(IIO(io))) == BlockJournalDisk.DiskOp(BlockDisk.ReqWriteNodeOp(id.value, BlockDisk.ReqWriteNode(loc.value, sector.node.I())), JournalDisk.NoDiskOp)
  {
    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
    if (bytes == null) {
      id := None;
      loc := None;
    } else {
      var len := bytes.Length as uint64;
      loc := getFreeLoc(s, len);
      if (loc.Some?) {
        var i := io.write(loc.value.addr, bytes[..]);
        id := Some(i);
      } else {
        id := None;
      }
    }

    IMM.reveal_parseSector();
    IMM.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();
  }

  method FindIndirectionTableLocationAndRequestWrite(
      io: DiskIOHandler, shared s: ImplVariables, ghost sector: SSI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.Ready?
  requires io.initialized()
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires sector.SectorIndirectionTable?
  requires s.frozenIndirectionTable.lSome? && sector.indirectionTable == s.frozenIndirectionTable.value

  // [yizhou7]: additional precondition
  requires s.BCInv()

  modifies io

  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures id.Some? ==> id.value == old(io.reservedId())
  ensures id.Some? ==> (loc.Some? && io.diskOp().ReqWriteOp? && io.diskOp().id == id.value)
  ensures id.None? ==> IIO(io) == old(IIO(io))

  ensures id.Some? ==> loc.Some?
  ensures id.Some? ==> DiskLayout.ValidIndirectionTableLocation(loc.value)
  ensures id.Some? ==> IDiskOp(diskOp(IIO(io))) == BlockJournalDisk.DiskOp(BlockDisk.ReqWriteIndirectionTableOp(id.value, BlockDisk.ReqWriteIndirectionTable(loc.value, sector.indirectionTable.I())), JournalDisk.NoDiskOp)
  ensures loc.Some? ==> !overlap(loc.value, s.persistentIndirectionTableLoc)
  {
    var bytes := MarshallingImpl.MarshallCheckedSectorIndirectionTable(s.frozenIndirectionTable.value, sector);
    if (bytes == null) {
      id := None;
      loc := None;
    } else {
      var len := bytes.Length as uint64;
      loc := Some(DiskLayout.Location(
        otherIndirectionTableAddr(s.persistentIndirectionTableLoc.addr),
        len));
      var i := io.write(loc.value.addr, bytes[..]);
      id := Some(i);
    }

    IMM.reveal_parseSector();
    IMM.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();

    ghost var dop := diskOp(IIO(io));
    if dop.ReqWriteOp? {
      if overlap(loc.value, s.persistentIndirectionTableLoc) {
        overlappingIndirectionTablesSameAddr(
            loc.value, s.persistentIndirectionTableLoc);
        assert false;
      }
    }
  }

  method RequestRead(io: DiskIOHandler, loc: Location)
  returns (id: D.ReqId)
  requires io.initialized()
  modifies io
  ensures (id, IIO(io)) == IOModel.RequestRead(old(IIO(io)), loc)
  {
    id := io.read(loc.addr, loc.len);
  }

  method PageInIndirectionTableReq(linear inout s: ImplVariables, io: DiskIOHandler)
  requires old_s.WFBCVars()
  requires io.initialized()
  requires old_s.Loading?
  // [yizhou7]: additional precondition
  requires ValidIndirectionTableLocation(old_s.indirectionTableLoc)

  modifies io
  ensures var dop := diskOp(IIO(io));
    && s.WFBCVars()
    && ValidDiskOp(dop)
    && IDiskOp(dop).jdop.NoDiskOp?
    && BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(dop).bdop, StatesInternalOp)
  {
    if (s.indirectionTableRead.None?) {
      var id := RequestRead(io, s.indirectionTableLoc);
      inout s.indirectionTableRead := Some(id);

      IOModel.RequestReadCorrect(old(IIO(io)), old_s.indirectionTableLoc);
      assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.PageInIndirectionTableReqStep);
    } else {
      print "PageInIndirectionTableReq: request already out\n";
      assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
    }
  }

  method PageInNodeReq(linear inout s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  requires io.initialized();
  requires old_s.Ready?
  // requires old_s.WFBCVars()
  requires ref in old_s.ephemeralIndirectionTable.I().locs

  // [yizhou7]: addtional preconditions
  requires old_s.BCInv()
  requires ref !in old_s.cache.I()
  requires old_s.TotalCacheSize() as int <= MaxCacheSize() - 1

  modifies io
  ensures 
    && s.Ready?
    && s.WFBCVars()
    && ValidDiskOp(diskOp(IIO(io)))
    && BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      print "giving up; already an outstanding read for this ref\n";
      assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
    } else {
      var locGraph := s.ephemeralIndirectionTable.GetEntry(ref);
      var loc := locGraph.value.loc;

      assert ref in s.ephemeralIndirectionTable.I().locs;
      assert DiskLayout.ValidNodeLocation(loc.value);
      var id := RequestRead(io, loc.value);

      inout s.outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)];

      assert s.WFBCVars();
      assert BC.PageInNodeReq(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, ref);
      assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.PageInNodeReqStep(ref));
    }
  }
  // == readResponse ==

  function ISectorOpt(sector: Option<SSI.Sector>) : Option<SSM.Sector>
  requires sector.Some? ==> SSI.WFSector(sector.value)
  {
    match sector {
      case None => None
      case Some(sector) => Some(SSI.ISector(sector))
    }
  }

  method ReadSector(io: DiskIOHandler)
  returns (id: D.ReqId, linear sector: lOption<SSI.Sector>)
  requires io.diskOp().RespReadOp?
  ensures sector.lSome? ==> SSI.WFSector(sector.value)
  ensures (id, ISectorOpt(sector.Option())) == IOModel.ReadSector(old(IIO(io)))
  {
    var id1, addr, bytes := io.getReadResult();
    id := id1;
    if |bytes| as uint64 <= LargestBlockSizeOfAnyTypeUint64() {
      var loc := DiskLayout.Location(addr, |bytes| as uint64);
      linear var sectorOpt := MarshallingImpl.ParseCheckedSector(bytes);
      if sectorOpt.lSome? && (
        || (ValidNodeLocation(loc) && sectorOpt.value.SectorNode?)
        || (ValidSuperblockLocation(loc) && sectorOpt.value.SectorSuperblock?)
        || (ValidIndirectionTableLocation(loc) && sectorOpt.value.SectorIndirectionTable?)
      ) {
        sector := sectorOpt;
      } else {
        FreeSectorOpt(sectorOpt);
        sector := lNone;
      }
    } else {
      sector := lNone;
    }
  }

  method PageInIndirectionTableResp(linear inout s: ImplVariables, io: DiskIOHandler)
  // requires old_s.W()
  requires io.diskOp().RespReadOp?
  requires old_s.Loading?

  // [yizhou7]: addtional preconditions
  requires old_s.BCInv()
  requires ValidDiskOp(diskOp(IIO(io)))
  requires ValidIndirectionTableLocation(LocOfRespRead(diskOp(IIO(io)).respRead))

  ensures 
    && s.WFBCVars()
    && ValidDiskOp(diskOp(IIO(io)))
    && IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
    && BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
  {
    linear var sectorOpt; var id;
    id, sectorOpt := ReadSector(io);

    IOModel.ReadSectorCorrect(IIO(io));

    Marshalling.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_Parse();

    if (Some(id) == s.indirectionTableRead && sectorOpt.lSome? && sectorOpt.value.SectorIndirectionTable?) {
      linear var lSome(sector: SSI.Sector) := sectorOpt;
      linear var SectorIndirectionTable(ephemeralIndirectionTable) := sector;

      linear var bm; var succ;
      succ, bm := ephemeralIndirectionTable.InitLocBitmap();
      assert (succ, bm.I()) == ephemeralIndirectionTable.initLocBitmap(); // TODO(andreal) unnecessary

      if succ {
        linear var Loading(indirectionTableLoc, indirectionTableRead) := s;
  
        linear var blockAllocator := BlockAllocatorImpl.BlockAllocator.Constructor(bm);
        linear var persistentIndirectionTable := ephemeralIndirectionTable.Clone();
        linear var lru := LinearLru.LinearLru.Alloc();
        linear var cache := CacheImpl.LMutCache.NewCache();

        s := Variables.Ready(
          persistentIndirectionTable,
          lNone,
          ephemeralIndirectionTable,
          indirectionTableLoc,
          None,
          None,
          map[],
          map[],
          cache,
          lru,
          blockAllocator);

        BucketWeights.WeightBucketEmpty();

        assert ConsistentBitmap(s.ephemeralIndirectionTable.I(), lNone,
          s.persistentIndirectionTable.I(), s.outstandingBlockWrites, s.blockAllocator.I()) by {
          reveal_ConsistentBitmap();
        }

        assert s.WFBCVars();
        assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.PageInIndirectionTableRespStep);
        assert BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp);
      } else {
        bm.Free();
        ephemeralIndirectionTable.Free();
        print "InitLocBitmap failed\n";

        assert old_s == s;
        assert ValidDiskOp(diskOp(IIO(io)));
        assert BC.NoOp(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp);
        assert BBC.BlockCacheMove(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, BC.NoOpStep);
        assert BBC.NextStep(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
        assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
      }
    } else {

      assert old_s == s;
      assert ValidDiskOp(diskOp(IIO(io)));
      assert BC.NoOp(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp);
      assert BBC.BlockCacheMove(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, BC.NoOpStep);
      assert BBC.NextStep(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
      assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);

      FreeSectorOpt(sectorOpt);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  // [yizhou7][fixme]: this takes a long time to go through
  method PageInNodeResp(linear inout s: ImplVariables, io: DiskIOHandler)
  requires old_s.WFBCVars()
  requires io.diskOp().RespReadOp?
  requires old_s.Ready?

  // [yizhou7]: addtional preconditions
  requires old_s.BCInv()
  requires ValidDiskOp(diskOp(IIO(io)))

  ensures && s.WFBCVars()
    && ValidDiskOp(diskOp(IIO(io)))
    && BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
  {
    var id; linear var sector;
    id, sector := ReadSector(io);
    assert sector.lSome? ==> SSI.WFSector(sector.value);

    IOModel.ReadSectorCorrect(IIO(io));

    Marshalling.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_Parse();

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it
    if (id in s.outstandingBlockReads) {
      var ref := s.outstandingBlockReads[id].ref;
      var lbaGraph := s.ephemeralIndirectionTable.GetEntry(ref);
      if (lbaGraph.Some? && lbaGraph.value.loc.Some?) {
        var cacheLookup := s.cache.InCache(ref);
        if cacheLookup {
          FreeSectorOpt(sector);
          print "PageInNodeResp: ref in s.cache\n";
          assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
        } else {
          assert sector.lSome? ==> SSI.WFSector(sector.value);

          var lba := lbaGraph.value.loc.value;
          var graph := lbaGraph.value.succs;

          if (sector.lSome? && sector.value.SectorNode?) {
            linear var lSome(value: SSI.Sector) := sector;
            linear var SectorNode(node) := value;

            var children := node.children;
            if (graph == (if children.Some? then children.value else [])) {
              inout s.lru.Use(ref);
              inout s.cache.Insert(ref, node);
              inout s.outstandingBlockReads := ComputeMapRemove1(s.outstandingBlockReads, id);

              BucketWeights.WeightBucketEmpty();

              LruModel.LruUse(old_s.lru.Queue(), ref);

              assert |s.cache.I()| == |old_s.cache.I()| + 1;
              assert |s.outstandingBlockReads| == |old_s.outstandingBlockReads| - 1;

              assert s.WFBCVars();
              assert BC.PageInNodeResp(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp);
              assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.PageInNodeRespStep);
            } else {
              var _ := FreeNode(node);
              print "giving up; block does not match graph\n";
              assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
            }
          } else {
            FreeSectorOpt(sector);
            print "giving up; block read in was not block\n";
            assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
          }
        }
      } else {
        FreeSectorOpt(sector);
        print "PageInNodeResp: ref !in lbas\n";
        assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
      }
    } else {
      FreeSectorOpt(sector);
      print "PageInNodeResp: unrecognized id from Read\n";
      assert IOModel.stepsBC(old_s.IBlockCache(), s.IBlockCache(), StatesInternalOp, IIO(io), BC.NoOpStep);
    }
  }
/*

  // == writeResponse ==

  method writeNodeResponse(linear inout s: ImplVariables, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires old_s.Inv()
  requires old_s.Ready? && IIO(io).id in old_s.outstandingBlockWrites
  ensures s.W()
  ensures s.I() == IOModel.writeNodeResponse(old_s.I(), IIO(io))
  {
    var id, addr, len := io.getWriteResult();
    IOModel.lemmaOutstandingLocIndexValid(s.I(), id);

    var i := s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64();
    inout s.blockAllocator.MarkFreeOutstanding(i);
    inout s.outstandingBlockWrites := ComputeMapRemove1(s.outstandingBlockWrites, id);
  }

  method writeIndirectionTableResponse(linear inout s: ImplVariables, io: DiskIOHandler)
  returns (loc: Location)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.frozenIndirectionTableLoc.Some?
  ensures s.W()
  ensures (s.I(), loc) == IOModel.writeIndirectionTableResponse(
      old_s.I(), IIO(io))
  {
    inout s.outstandingIndirectionTableWrite := None;
    loc := s.frozenIndirectionTableLoc.value;
  }

  // [yizhou7]: this might not be the best way is to decompose and recompose
  method cleanUp(linear inout s: ImplVariables)
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.frozenIndirectionTable.lSome?
  requires old_s.frozenIndirectionTableLoc.Some?
  ensures s.W()
  ensures s.I() == IOModel.cleanUp(old_s.I())
  {
    IOModel.lemmaBlockAllocatorFrozenSome(s.I());

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

    persistentIndirectionTable.Free();
    linear var value := unwrap_value(frozenIndirectionTable);

    s := Ready(
      value,
      lNone,
      ephemeralIndirectionTable,
      frozenIndirectionTableLoc.value,
      None,
      outstandingIndirectionTableWrite,
      outstandingBlockWrites,
      outstandingBlockReads,
      cache,
      lru,
      blockAllocator);

    inout s.blockAllocator.MoveFrozenToPersistent();
  }
  */
}
