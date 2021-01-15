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

  // TODO does ImplVariables make sense? Should it be a Variables? Or just the fields of a class we live in?
  method getFreeLoc(shared s: ImplVariables, len: uint64)
  returns (loc : Option<Location>)
  requires s.ready
  requires s.WF()
  requires len <= NodeBlockSizeUint64()
  ensures loc == IOModel.getFreeLoc(s.I(), len)
  {
    IOModel.reveal_getFreeLoc();
    var i := s.blockAllocator.Alloc();
    if i.Some? {
      loc := Some(Location((i.value * NodeBlockSizeUint64()), len));
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
  modifies io
  ensures IOModel.RequestWrite(old(IIO(io)), loc, old(SSI.ISector(sector)), id, IIO(io))
  ensures io.diskOp().ReqWriteOp? && io.diskOp().id == id
  {
    IOModel.reveal_RequestWrite();

    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
    id := io.write(loc.addr, bytes[..]);

    sector.Free();
  }

  method FindLocationAndRequestWrite(io: DiskIOHandler, shared s: ImplVariables, shared sector: SSI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.WF()
  requires s.ready
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires io.initialized()
  requires sector.SectorNode?
  modifies io
  ensures s.W()
  ensures IOModel.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(SSI.ISector(sector)), id, loc, IIO(io))
  ensures old(s.I()) == s.I();
  ensures id.Some? ==> loc.Some? && io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> IIO(io) == old(IIO(io))
  {
    IOModel.reveal_FindLocationAndRequestWrite();

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
  }

  method FindIndirectionTableLocationAndRequestWrite(
      io: DiskIOHandler, shared s: ImplVariables, linear sector: SSI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.WF()
  requires s.ready
  requires SSI.WFSector(sector)
  requires SSM.WFSector(SSI.ISector(sector))
  requires io.initialized()
  requires sector.SectorIndirectionTable?
  requires sector.SectorIndirectionTable? ==> (s.frozenIndirectionTable.lSome? && sector.indirectionTable == s.frozenIndirectionTable.value)

  modifies io

  // ensures sector.SectorIndirectionTable? ==> (sector.indirectionTable.Inv() && sector.indirectionTable.I() == old(sector.indirectionTable.I()))
  ensures id.Some? ==> id.value == old(io.reservedId())
  ensures s.W()
  ensures IOModel.FindIndirectionTableLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(SSI.ISector(sector)), id, loc, IIO(io))
  ensures old(s.I()) == s.I();
  ensures id.Some? ==> loc.Some? && io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> IIO(io) == old(IIO(io))
  {
    IOModel.reveal_FindIndirectionTableLocationAndRequestWrite();

    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
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
    sector.Free();
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
  requires old_s.WF()
  requires io.initialized()
  requires !old_s.ready
  requires old_s.loading
  requires ValidIndirectionTableLocation(old_s.indirectionTableLoc)
  modifies io
  ensures s.WF()
  ensures (s.I(), IIO(io)) == IOModel.PageInIndirectionTableReq(
      old_s.I(), old(IIO(io)))
  {
    IOModel.reveal_PageInIndirectionTableReq();

    if (s.indirectionTableRead.None?) {
      var id := RequestRead(io, s.indirectionTableLoc);
      inout s.indirectionTableRead := Some(id);
    } else {
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  method PageInNodeReq(linear inout s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  requires io.initialized();
  requires old_s.ready
  requires old_s.WF()
  requires ref in old_s.ephemeralIndirectionTable.I().locs

  // [yizhou7]: this addtional precondition is needed
  requires old_s.TotalCacheSize() as int <= MaxCacheSize() - 1

  modifies io
  ensures s.WF()
  ensures s.ready
  ensures (s.I(), IIO(io)) == IOModel.PageInNodeReq(old_s.I(), old(IIO(io)), ref)
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var locGraph := s.ephemeralIndirectionTable.GetEntry(ref);
      var loc := locGraph.value.loc;
      var id := RequestRead(io, loc.value);
      inout s.outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)];
    }
  }
/*

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

  method PageInIndirectionTableResp(s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires io.diskOp().RespReadOp?
  requires !s.ready
  requires s.loading
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInIndirectionTableResp(old(s.I()), old(IIO(io)))
  {
    var id;
    linear var sectorOpt;
    id, sectorOpt := ReadSector(io);

    if (Some(id) == s.indirectionTableRead && sectorOpt.lSome? && sectorOpt.value.SectorIndirectionTable?) {
      linear var lSome(sector: SSI.Sector) := sectorOpt;
      linear var SectorIndirectionTable(ephemeralIndirectionTable) := sector;
      assert SSI.SectorRepr(sector) == 
        {ephemeralIndirectionTable} + ephemeralIndirectionTable.Repr; // why is this needed??

      var succ, bm := ephemeralIndirectionTable.InitLocBitmap();
      assert (succ, bm.I()) == ephemeralIndirectionTable.ReadWithInv().initLocBitmap(); // TODO(andreal) unnecessary
      if succ {
        var blockAllocator := new BlockAllocatorImpl.BlockAllocator(bm);
        var persistentIndirectionTable := ephemeralIndirectionTable.Clone();

        s.ready := true;
        s.persistentIndirectionTable := persistentIndirectionTable;
        s.frozenIndirectionTable := null;
        s.persistentIndirectionTableLoc := s.indirectionTableLoc;
        s.frozenIndirectionTableLoc := None;
        s.ephemeralIndirectionTable := ephemeralIndirectionTable;
        s.outstandingIndirectionTableWrite := None;
        s.outstandingBlockWrites := map[];
        s.outstandingBlockReads := map[];
        s.cache := new MutCache();
        assert s.cache.I() == map[];
        s.lru := new LruImpl.LruImplQueue();
        s.blockAllocator := blockAllocator;
        assert s.I() == IOModel.PageInIndirectionTableResp(old(s.I()), old(IIO(io))); // TODO(andreal)
      } else {
        print "InitLocBitmap failed\n";
      }
    } else {
      FreeSectorOpt(sectorOpt);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInNodeResp(s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires s.WF()
  requires io.diskOp().RespReadOp?
  requires s.ready
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInNodeResp(old(s.I()), old(IIO(io)))
  {
    var id;
    linear var sector;
    id, sector := ReadSector(io);
    assert sector.lSome? ==> SSI.WFSector(sector.value);
    assert sector.lSome? ==> SSI.SectorRepr(sector.value) !! s.Repr();

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
        } else {
          assert sector.lSome? ==> SSI.WFSector(sector.value);
          assert sector.lSome? ==> SSI.SectorRepr(sector.value) !! s.Repr();

          var lba := lbaGraph.value.loc.value;
          var graph := lbaGraph.value.succs;

          if (sector.lSome? && sector.value.SectorNode?) {
            linear var lSome(value: SSI.Sector) := sector;
            linear var SectorNode(node) := value;

            var children := node.children;
            if (graph == (if children.Some? then children.value else [])) {
              assert|LruModel.I(s.lru.Queue)| <= 0x10000;
              assert sector.lSome? ==> SSI.WFSector(value);
              assert sector.lSome? ==> SSI.SectorRepr(value) !! s.Repr();
              s.lru.Use(ref);

              assert sector.lSome? ==> SSI.WFSector(value);
              assert sector.lSome? ==> SSI.SectorRepr(value) !! s.Repr();

              assert |s.cache.I()| <= MaxCacheSize();
              s.cache.Insert(ref, node);

              s.outstandingBlockReads := ComputeMapRemove1(s.outstandingBlockReads, id);
            } else {
              var _ := FreeNode(node);
              print "giving up; block does not match graph\n";
            }
          } else {
            FreeSectorOpt(sector);
            print "giving up; block read in was not block\n";
          }
        }
      } else {
        FreeSectorOpt(sector);
        print "PageInNodeResp: ref !in lbas\n";
      }
    } else {
      FreeSectorOpt(sector);
      print "PageInNodeResp: unrecognized id from Read\n";
    }
  }

  // == writeResponse ==

  method writeNodeResponse(s: ImplVariables, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires Inv(s)
  requires s.ready && IIO(io).id in s.outstandingBlockWrites
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.writeNodeResponse(old(s.I()), IIO(io))
  {
    var id, addr, len := io.getWriteResult();
    IOModel.lemmaOutstandingLocIndexValid(s.I(), id);

    s.blockAllocator.MarkFreeOutstanding(s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64());
    s.outstandingBlockWrites := ComputeMapRemove1(s.outstandingBlockWrites, id);
  }

  method writeIndirectionTableResponse(s: ImplVariables, io: DiskIOHandler)
  returns (loc: Location)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires Inv(s)
  requires s.ready
  requires s.frozenIndirectionTableLoc.Some?
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), loc) == IOModel.writeIndirectionTableResponse(
      old(s.I()), IIO(io))
  {
    s.outstandingIndirectionTableWrite := None;
    loc := s.frozenIndirectionTableLoc.value;
  }

  method cleanUp(s: ImplVariables)
  requires Inv(s)
  requires s.ready
  requires s.frozenIndirectionTable != null
  requires s.frozenIndirectionTableLoc.Some?
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.cleanUp(old(s.I()))
  {
    IOModel.lemmaBlockAllocatorFrozenSome(s.I());
    s.persistentIndirectionTableLoc := s.frozenIndirectionTableLoc.value;
    s.persistentIndirectionTable := s.frozenIndirectionTable;
    s.frozenIndirectionTable := null;
    s.frozenIndirectionTableLoc := None;
    s.blockAllocator.MoveFrozenToPersistent();
  }
  */
}
