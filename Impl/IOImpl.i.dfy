include "StateImpl.i.dfy"
include "IOModel.i.dfy"
include "MarshallingImpl.i.dfy"

module IOImpl { 
  import MainDiskIOHandler
  import opened NativeTypes
  import opened Options
  import opened Maps
  import opened NodeImpl
  import opened CacheImpl
  import opened LBAType
  import StateModel
  import MarshallingImpl
  import IOModel
  import BucketsLib
  import LruModel
  import LruImpl
  import opened Bounds
  import opened SI = StateImpl
  import MutableMapModel

  type DiskIOHandler = MainDiskIOHandler.DiskIOHandler

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
      loc := Some(LBAType.Location((i.value * NodeBlockSizeUint64()), len));
    } else {
      loc := None;
    }
  }

  method RequestWrite(io: DiskIOHandler, loc: LBAType.Location, sector: SI.Sector)
  returns (id: Option<D.ReqId>)
  requires SI.WFSector(sector)
  requires IM.WFSector(SI.ISector(sector))
  requires io.initialized()
  modifies io
  ensures IOModel.RequestWrite(old(IIO(io)), loc, old(ISector(sector)), id, IIO(io))
  ensures id.Some? ==> io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> old(IIO(io)) == IIO(io)
  {
    IOModel.reveal_RequestWrite();

    var bytes := MarshallingImpl.MarshallCheckedSector(sector);
    if (bytes == null || bytes.Length as uint64 != loc.len) {
      id := None;
    } else {
      var i := io.write(loc.addr, bytes);
      id := Some(i);
    }
  }

  method FindLocationAndRequestWrite(io: DiskIOHandler, s: ImplVariables, sector: SI.Sector)
  returns (id: Option<D.ReqId>, loc: Option<LBAType.Location>)
  requires s.WF()
  requires s.ready
  requires SI.WFSector(sector)
  requires IM.WFSector(SI.ISector(sector))
  requires io.initialized()
  requires io !in s.Repr()
  requires sector.SectorBlock?
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
        var i := io.write(loc.value.addr, bytes);
        id := Some(i);
      } else {
        id := None;
      }
    }
  }

  method RequestRead(io: DiskIOHandler, loc: LBAType.Location)
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
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io)) == IOModel.PageInIndirectionTableReq(Ic(k), old(s.I()), old(IIO(io)))
  {
    IOModel.reveal_PageInIndirectionTableReq();

    if (s.outstandingIndirectionTableRead.None?) {
      var id := RequestRead(io, IndirectionTableLocation());
      s.outstandingIndirectionTableRead := Some(id);
    } else {
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  method PageInReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  requires io.initialized();
  requires s.ready
  requires s.WF()
  requires ref in SI.IIndirectionTable(s.ephemeralIndirectionTable).locs
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == IOModel.PageInReq(Ic(k), old(s.I()), old(IIO(io)), ref)
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
    var id1, bytes := io.getReadResult();
    id := id1;
    if |bytes| as uint64 <= IndirectionTableBlockSizeUint64() {
      var sectorOpt := MarshallingImpl.ParseCheckedSector(bytes);
      sector := sectorOpt;
    } else {
      sector := None;
    }
  }

  method PageInIndirectionTableResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires io.diskOp().RespReadOp?
  requires !s.ready
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInIndirectionTableResp(Ic(k), old(s.I()), old(IIO(io)))
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
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

  method PageInResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires s.WF()
  requires io.diskOp().RespReadOp?
  requires s.ready
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.PageInResp(Ic(k), old(s.I()), old(IIO(io)))
  {
    var id, sector := ReadSector(io);
    assert sector.Some? ==> SI.WFSector(sector.value);
    assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

    if (id !in s.outstandingBlockReads) {
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;

    var lbaGraph := s.ephemeralIndirectionTable.GetEntry(ref);
    if (lbaGraph.None? || lbaGraph.value.loc.None?) {
      print "PageInResp: ref !in lbas\n";
      return;
    }
    var cacheLookup := s.cache.GetOpt(ref);
    if cacheLookup.Some? {
      print "PageInResp: ref in s.cache\n";
      return;
    }

    assert sector.Some? ==> SI.WFSector(sector.value);
    assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

    var lba := lbaGraph.value.loc.value;
    var graph := lbaGraph.value.succs;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])) {
        assert|LruModel.I(s.lru.Queue)| <= 0x10000;
        assert sector.Some? ==> SI.WFSector(sector.value);
        assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();
        s.lru.Use(ref);

        assert sector.Some? ==> SI.WFSector(sector.value);
        assert sector.Some? ==> SectorRepr(sector.value) !! s.Repr();

        assert |s.cache.I()| <= MaxCacheSize();
        s.cache.Insert(ref, sector.value.block);

        s.outstandingBlockReads := ComputeMapRemove1(s.outstandingBlockReads, id);
      } else {
        print "giving up; block does not match graph\n";
      }
    } else {
      print "giving up; block read in was not block\n";
    }
  }


  method readResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires io.diskOp().RespReadOp?
  requires s.W()
  requires s.WF()
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.readResponse(Ic(k), old(s.I()), IIO(io))
  {
    if (!s.ready) {
      PageInIndirectionTableResp(k, s, io);
    } else {
      PageInResp(k, s, io);
    }
  }

  // == writeResponse ==

  method writeResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires SI.Inv(k, s)
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == IOModel.writeResponse(Ic(k), old(s.I()), IIO(io))
  {
    var id := io.getWriteResult();
    if (s.ready && s.outstandingIndirectionTableWrite == Some(id)) {
      IOModel.lemmaBlockAllocatorFrozenSome(Ic(k), s.I());

      s.outstandingIndirectionTableWrite := None;
      s.persistentIndirectionTable := s.frozenIndirectionTable;
      s.frozenIndirectionTable := null;
      s.syncReqs := SyncReqs2to1(s.syncReqs);

      s.blockAllocator.MoveFrozenToPersistent();
    } else if (s.ready && id in s.outstandingBlockWrites) {
      IOModel.lemmaOutstandingLocIndexValid(Ic(k), s.I(), id);

      s.blockAllocator.MarkFreeOutstanding(s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64());
      s.outstandingBlockWrites := ComputeMapRemove1(s.outstandingBlockWrites, id);
    } else {
    }
  }
}
