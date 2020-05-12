include "StateImpl.i.dfy"
include "IOModel.i.dfy"
include "MarshallingImpl.i.dfy"

module IOImpl { 
  import opened MainDiskIOHandler
  import opened NativeTypes
  import opened Options
  import opened Maps
  import opened NodeImpl
  import opened CacheImpl
  import opened DiskLayout
  import opened DiskOpImpl
  import StateModel
  import opened InterpretationDiskOps
  import MarshallingImpl
  import IOModel
  import BucketsLib
  import LruModel
  import LruImpl
  import opened Bounds
  import opened SI = StateImpl
  import MutableMapModel

  // TODO does ImplVariables make sense? Should it be a Variables? Or just the fields of a class we live in?
  method getFreeLoc(s: ImplVariables, len: uint64)
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

  method RequestWrite(io: DiskIOHandler, loc: Location, sector: SI.Sector)
  returns (id: D.ReqId)
  requires SI.WFSector(sector)
  requires IM.WFSector(SI.ISector(sector))
  requires io.initialized()
  requires sector.SectorSuperblock?
  requires ValidSuperblockLocation(loc)
  modifies io
  ensures IOModel.RequestWrite(old(IIO(io)), loc, old(ISector(sector)), id, IIO(io))
  ensures io.diskOp().ReqWriteOp? && io.diskOp().id == id
  {
    IOModel.reveal_RequestWrite();

    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
    id := io.write(loc.addr, bytes[..]);
  }

  method FindLocationAndRequestWrite(io: DiskIOHandler, s: ImplVariables, sector: SI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.WF()
  requires s.ready
  requires SI.WFSector(sector)
  requires IM.WFSector(SI.ISector(sector))
  requires io.initialized()
  requires io !in s.Repr()
  requires sector.SectorNode?
  modifies io
  ensures s.W()
  ensures IOModel.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(ISector(sector)), id, loc, IIO(io))
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
      io: DiskIOHandler, s: ImplVariables, sector: SI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<Location>)
  requires s.WF()
  requires s.ready
  requires SI.WFSector(sector)
  requires IM.WFSector(SI.ISector(sector))
  requires io.initialized()
  requires io !in s.Repr()
  requires sector.SectorIndirectionTable?
  modifies io
  ensures id.Some? ==> id.value == old(io.reservedId())
  ensures s.W()
  ensures IOModel.FindIndirectionTableLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(ISector(sector)), id, loc, IIO(io))
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
  }

  method RequestRead(io: DiskIOHandler, loc: Location)
  returns (id: D.ReqId)
  requires io.initialized()
  modifies io
  ensures (id, IIO(io)) == IOModel.RequestRead(old(IIO(io)), loc)
  {
    id := io.read(loc.addr, loc.len);
  }

  method PageInIndirectionTableReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.WF()
  requires io.initialized();
  requires !s.ready
  requires s.loading
  requires io !in s.Repr()
  requires ValidIndirectionTableLocation(s.indirectionTableLoc)
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io)) == IOModel.PageInIndirectionTableReq(
      Ic(k), old(s.I()), old(IIO(io)))
  {
    IOModel.reveal_PageInIndirectionTableReq();

    if (s.indirectionTableRead.None?) {
      var id := RequestRead(io, s.indirectionTableLoc);
      s.indirectionTableRead := Some(id);
    } else {
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  method PageInNodeReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  requires io.initialized();
  requires s.ready
  requires s.WF()
  requires ref in SI.IIndirectionTable(s.ephemeralIndirectionTable).locs
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == IOModel.PageInNodeReq(Ic(k), old(s.I()), old(IIO(io)), ref)
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var locGraph := s.ephemeralIndirectionTable.GetEntry(ref);
      assert locGraph.Some?;
      var loc := locGraph.value.loc;
      var id := RequestRead(io, loc.value);
      s.outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)];
    }
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<SI.Sector>) : Option<IM.Sector>
  reads if sector.Some? then SectorObjectSet(sector.value) else {}
  reads if sector.Some? then SectorRepr(sector.value) else {}
  requires sector.Some? ==> SI.WFSector(sector.value)
  {
    match sector {
      case None => None
      case Some(sector) => Some(SI.ISector(sector))
    }
  }

  method ReadSector(io: DiskIOHandler)
  returns (id: D.ReqId, sector: Option<SI.Sector>)
  requires io.diskOp().RespReadOp?
  ensures sector.Some? ==> SI.WFSector(sector.value)
  ensures sector.Some? ==> fresh(SectorRepr(sector.value))
  ensures (id, ISectorOpt(sector)) == IOModel.ReadSector(old(IIO(io)))
  {
    var id1, addr, bytes := io.getReadResult();
    id := id1;
    if |bytes| as uint64 <= LargestBlockSizeOfAnyTypeUint64() {
      var loc := DiskLayout.Location(addr, |bytes| as uint64);
      var sectorOpt := MarshallingImpl.ParseCheckedSector(bytes);
      if sectorOpt.Some? && (
        || (ValidNodeLocation(loc) && sectorOpt.value.SectorNode?)
        || (ValidSuperblockLocation(loc) && sectorOpt.value.SectorSuperblock?)
        || (ValidIndirectionTableLocation(loc) && sectorOpt.value.SectorIndirectionTable?)
      ) {
        sector := sectorOpt;
      } else {
        sector := None;
      }
    } else {
      sector := None;
    }
  }

  method PageInIndirectionTableResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires io.diskOp().RespReadOp?
  requires !s.ready
  requires s.loading
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInIndirectionTableResp(Ic(k), old(s.I()), old(IIO(io)))
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.indirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      //assert fresh(SectorRepr(sector.value));
      assert SectorRepr(sector.value) == {ephemeralIndirectionTable} + ephemeralIndirectionTable.Repr; // why is this needed??
      //assert fresh({ephemeralIndirectionTable} + ephemeralIndirectionTable.Repr);
      //assert fresh(ephemeralIndirectionTable.Repr);

      var succ, bm := ephemeralIndirectionTable.InitLocBitmap();
      if succ {
        var blockAllocator := new BlockAllocatorImpl.BlockAllocator(bm);
        var persistentIndirectionTable := sector.value.indirectionTable.Clone();
        //assert fresh(ephemeralIndirectionTable.Repr);
        //assert fresh(persistentIndirectionTable.Repr);

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
        s.lru := new LruImpl.LruImplQueue();
        s.blockAllocator := blockAllocator;
      } else {
        print "InitLocBitmap failed\n";
      }
    } else {
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInNodeResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires s.WF()
  requires io.diskOp().RespReadOp?
  requires s.ready
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInNodeResp(Ic(k), old(s.I()), old(IIO(io)))
  {
    var id, sector := ReadSector(io);
    assert sector.Some? ==> SI.WFSector(sector.value);
    assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

    if (id !in s.outstandingBlockReads) {
      print "PageInNodeResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;

    var lbaGraph := s.ephemeralIndirectionTable.GetEntry(ref);
    if (lbaGraph.None? || lbaGraph.value.loc.None?) {
      print "PageInNodeResp: ref !in lbas\n";
      return;
    }
    var cacheLookup := s.cache.GetOpt(ref);
    if cacheLookup.Some? {
      print "PageInNodeResp: ref in s.cache\n";
      return;
    }

    assert sector.Some? ==> SI.WFSector(sector.value);
    assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

    var lba := lbaGraph.value.loc.value;
    var graph := lbaGraph.value.succs;

    if (sector.Some? && sector.value.SectorNode?) {
      var node := sector.value.node;
      if (graph == (if node.children.Some? then node.children.value else [])) {
        assert|LruModel.I(s.lru.Queue)| <= 0x10000;
        assert sector.Some? ==> SI.WFSector(sector.value);
        assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();
        s.lru.Use(ref);

        assert sector.Some? ==> SI.WFSector(sector.value);
        assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

        assert |s.cache.I()| <= MaxCacheSize();
        s.cache.Insert(ref, sector.value.node);

        s.outstandingBlockReads := ComputeMapRemove1(s.outstandingBlockReads, id);
      } else {
        print "giving up; block does not match graph\n";
      }
    } else {
      print "giving up; block read in was not block\n";
    }
  }

  // == writeResponse ==

  method writeNodeResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires SI.Inv(k, s)
  requires s.ready && IIO(io).id in s.outstandingBlockWrites
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.writeNodeResponse(Ic(k), old(s.I()), IIO(io))
  {
    var id, addr, len := io.getWriteResult();
    IOModel.lemmaOutstandingLocIndexValid(Ic(k), s.I(), id);

    s.blockAllocator.MarkFreeOutstanding(s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64());
    s.outstandingBlockWrites := ComputeMapRemove1(s.outstandingBlockWrites, id);
  }

  method writeIndirectionTableResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (loc: Location)
  requires io.diskOp().RespWriteOp?
  requires ValidDiskOp(io.diskOp())
  requires SI.Inv(k, s)
  requires s.ready
  requires s.frozenIndirectionTableLoc.Some?
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), loc) == IOModel.writeIndirectionTableResponse(
      Ic(k), old(s.I()), IIO(io))
  {
    s.outstandingIndirectionTableWrite := None;
    loc := s.frozenIndirectionTableLoc.value;
  }

  method cleanUp(k: ImplConstants, s: ImplVariables)
  requires SI.Inv(k, s)
  requires s.ready
  requires s.frozenIndirectionTable != null
  requires s.frozenIndirectionTableLoc.Some?
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.cleanUp(Ic(k), old(s.I()))
  {
    IOModel.lemmaBlockAllocatorFrozenSome(Ic(k), s.I());
    s.persistentIndirectionTableLoc := s.frozenIndirectionTableLoc.value;
    s.persistentIndirectionTable := s.frozenIndirectionTable;
    s.frozenIndirectionTable := null;
    s.frozenIndirectionTableLoc := None;
    s.blockAllocator.MoveFrozenToPersistent();
  }
}
