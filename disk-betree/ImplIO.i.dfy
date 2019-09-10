include "Impl.i.dfy"
include "ImplState.i.dfy"
include "ImplModelIO.i.dfy"
include "ImplMarshalling.i.dfy"

module ImplIO { 
  import opened Impl
  import MainDiskIOHandler
  import opened NativeTypes
  import opened Options
  import opened Maps
  import ImplModel
  import ImplMarshalling
  import IMM = ImplMarshallingModel
  import ImplModelIO
  import BucketsLib
  import LruModel
  import MutableLru
  import opened Bounds
  import opened IS = ImplState
  import Native

  type DiskIOHandler = MainDiskIOHandler.DiskIOHandler

  method addrUsedInIndirectionTable(addr: uint64, indirectionTable:IS.MutIndirectionTable) returns (used:bool)
    requires indirectionTable.Inv()
    ensures !used == ImplModelIO.addrNotUsedInIndirectionTable(addr, IS.IIndirectionTable(indirectionTable))
  {
    var table := indirectionTable.ToMap();
    return !(forall ref | ref in table && table[ref].0.Some?  ::
          table[ref].0.value.addr != addr);
  }

  function method MaxOffset() : (maxOffset:uint64)
    ensures maxOffset as int * LBAType.BlockSize() as int == 0x1_0000_0000_0000_0000;
  {
    // TODO I suspect we constructed a BigInteger to assign this.
    var maxOffset:uint64 := (0x1_0000_0000_0000_0000 / LBAType.BlockSize() as int) as uint64;
    maxOffset
  }

    // TODO does ImplVariables make sense? Should it be a Variables? Or just the fields of a class we live in?
  method getFreeLoc(s: ImplVariables, len: uint64)
  returns (loc : Option<BC.Location>)
  requires s.ready
  requires s.WF()
  requires len <= LBAType.BlockSize()
  ensures loc == ImplModelIO.getFreeLoc(s.I(), len)
  {
    ImplModelIO.reveal_getFreeLoc();
    var tryOffset:uint64 := 0;
    while true
        invariant tryOffset as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
        invariant ImplModelIO.getFreeLoc(s.I(), len)
               == ImplModelIO.getFreeLocIterate(s.I(), len, tryOffset)
        decreases 0x1_0000_0000_0000_0000 - tryOffset as int
    {
      var addr : uint64 := tryOffset * LBAType.BlockSize();
      var persistentUsed := addrUsedInIndirectionTable(addr, s.persistentIndirectionTable);
      var ephemeralUsed := addrUsedInIndirectionTable(addr, s.ephemeralIndirectionTable);
      var frozenUsed := false;
      if s.frozenIndirectionTable != null {
        frozenUsed := addrUsedInIndirectionTable(addr, s.frozenIndirectionTable);
      }
      var outstandingUsed := !(forall id | id in s.outstandingBlockWrites :: s.outstandingBlockWrites[id].loc.addr != addr);
      if (
          && BC.ValidLBAForNode(addr)
          && !persistentUsed
          && !ephemeralUsed
          && !frozenUsed
          && !outstandingUsed
        ) {
        var result := Some(LBAType.Location(addr, len));
        assert result == ImplModelIO.getFreeLocIterate(s.I(), len, tryOffset);

        return result;
      }
      if (tryOffset+1) as int >= 0x1_0000_0000_0000_0000 as int / LBAType.BlockSize() as int {
        return None;
      }

      tryOffset := tryOffset + 1;     
    }
  }

  method RequestWrite(io: DiskIOHandler, loc: LBAType.Location, sector: IS.Sector)
  returns (id: Option<D.ReqId>)
  requires IS.WFSector(sector)
  requires IM.WFSector(IS.ISector(sector))
  requires io.initialized()
  modifies io
  ensures ImplModelIO.RequestWrite(old(IIO(io)), loc, old(ISector(sector)), id, IIO(io))
  ensures id.Some? ==> io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> old(IIO(io)) == IIO(io)
  {
    ImplModelIO.reveal_RequestWrite();

    var bytes := ImplMarshalling.MarshallCheckedSector(sector);
    if (bytes == null || bytes.Length as uint64 != loc.len) {
      id := None;
    } else {
      var i := io.write(loc.addr, bytes);
      id := Some(i);
    }
  }

  method FindLocationAndRequestWrite(io: DiskIOHandler, s: ImplVariables, sector: IS.Sector)
  returns (id: Option<D.ReqId>, loc: Option<LBAType.Location>)
  requires s.WF()
  requires s.ready
  requires IS.WFSector(sector)
  requires IM.WFSector(IS.ISector(sector))
  requires io.initialized()
  requires io !in s.Repr()
  modifies io
  ensures s.W()
  ensures ImplModelIO.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(ISector(sector)), id, loc, IIO(io))
  ensures old(s.I()) == s.I();
  ensures id.Some? ==> loc.Some? && io.diskOp().ReqWriteOp? && io.diskOp().id == id.value
  ensures id.None? ==> IIO(io) == old(IIO(io))
  {
    ImplModelIO.reveal_FindLocationAndRequestWrite();

    var bytes := ImplMarshalling.MarshallCheckedSector(sector);
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
  ensures (id, IIO(io)) == ImplModelIO.RequestRead(old(IIO(io)), loc)
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
  ensures (s.I(), IIO(io)) == ImplModelIO.PageInIndirectionTableReq(Ic(k), old(s.I()), old(IIO(io)))
  {
    ImplModelIO.reveal_PageInIndirectionTableReq();

    if (s.outstandingIndirectionTableRead.None?) {
      var id := RequestRead(io, BC.IndirectionTableLocation());
      s.outstandingIndirectionTableRead := Some(id);
    } else {
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  method PageInReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  requires io.initialized();
  requires s.ready
  requires s.WF()
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable)
  requires IS.IIndirectionTable(s.ephemeralIndirectionTable)[ref].0.Some?
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == ImplModelIO.PageInReq(Ic(k), old(s.I()), old(IIO(io)), ref)
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      var id := RequestRead(io, lba.value);
      s.outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)];
    }
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<IS.Sector>) : Option<IM.Sector>
  requires sector.Some? ==> IS.WFSector(sector.value)
  reads if sector.Some? && sector.value.SectorIndirectionTable? then {sector.value.indirectionTable} else {}
  reads if sector.Some? && sector.value.SectorIndirectionTable? then sector.value.indirectionTable.Repr else {}
  reads if sector.Some? && sector.value.SectorBlock? then set i | 0 <= i < |sector.value.block.buckets| :: sector.value.block.buckets[i] else {}
  reads if sector.Some? && sector.value.SectorBlock? then set i, o | 0 <= i < |sector.value.block.buckets| && o in sector.value.block.buckets[i].Repr :: o else {}
  {
    match sector {
      case None => None
      case Some(sector) => Some(IS.ISector(sector))
    }
  }

  method ReadSector(io: DiskIOHandler)
  returns (id: D.ReqId, sector: Option<IS.Sector>)
  requires io.diskOp().RespReadOp?
  ensures sector.Some? ==> IS.WFSector(sector.value)
  //ensures sector.Some? ==> forall o | o in IS.SectorRepr(sector.value) :: fresh(o)
  ensures sector.Some? && sector.value.SectorBlock? ==> forall i, o | 0 <= i < |sector.value.block.buckets| && o in sector.value.block.buckets[i].Repr :: fresh(o)
  ensures (id, ISectorOpt(sector)) == ImplModelIO.ReadSector(IIO(io))
  {
    var id1, bytes := io.getReadResult();
    id := id1;
    if |bytes| <= ImplADM.M.BlockSize() {
      var sectorOpt := ImplMarshalling.ParseCheckedSector(bytes);
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
  ensures s.I() == ImplModelIO.PageInIndirectionTableResp(Ic(k), old(s.I()), old(IIO(io)))
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var persistentIndirectionTable := sector.value.indirectionTable.Clone();
      var ephemeralIndirectionTable := sector.value.indirectionTable.Clone(); // TODO one of these clones is not necessary, we just need to shhow that sector.value.indirectionTable is fresh

      s.ready := true;
      s.persistentIndirectionTable := persistentIndirectionTable;
      s.frozenIndirectionTable := null;
      s.ephemeralIndirectionTable := ephemeralIndirectionTable;
      s.outstandingIndirectionTableWrite := None;
      s.outstandingBlockWrites := map[];
      s.outstandingBlockReads := map[];
      s.cache := new MM.ResizingHashMap(128);
      s.lru := new MutableLru.MutableLruQueue();

      assert ICache(s.cache) == map[];
    } else {
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires s.W()
  requires io.diskOp().RespReadOp?
  requires s.ready
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelIO.PageInResp(Ic(k), old(s.I()), IIO(io))
  {
    var id, sector := ReadSector(io);

    /*if (sector.Some? && sector.value.SectorBlock?) {
      /*assert fresh(IS.SectorRepr(sector.value));
      assert forall o | o in IS.SectorRepr(sector.value) :: fresh(o);
      assert IS.SectorRepr(sector.value) == NodeRepr(sector.value.block);
      assert fresh(NodeRepr(sector.value.block));
      assert fresh(set i, o | 0 <= i < |sector.value.block.buckets| && o in sector.value.block.buckets[i].Repr :: o);*/
      //assert forall i | 0 <= i < |sector.value.block.buckets| :: fresh(sector.value.block.buckets[i].Repr);
      assert forall i, o | 0 <= i < |sector.value.block.buckets| && o in sector.value.block.buckets[i].Repr :: fresh(o);
    }
    assume false;*/

    if (id !in s.outstandingBlockReads) {
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;
    
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if (lbaGraph.None? || lbaGraph.value.0.None?) {
      print "PageInResp: ref !in lbas\n";
      return;
    }
    var cacheLookup := s.cache.Get(ref);
    if cacheLookup.Some? {
      print "PageInResp: ref in s.cache\n";
      return;
    }

    var lba := lbaGraph.value.0.value;
    var graph := lbaGraph.value.1;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])) {

        assume |LruModel.I(s.lru.Queue)| <= 0x10000;
        s.lru.Use(ref);

        assert forall o | o in CacheRepr(s.cache.Contents) :: o in old(CacheRepr(s.cache.Contents)) || fresh(o);

        assume |s.cache.Contents| <= MaxCacheSize();
        var _ := s.cache.Insert(ref, sector.value.block);

        assert forall i | 0 <= i < |sector.value.block.buckets| :: fresh(sector.value.block.buckets[i].Repr);
        assert forall o | o in CacheRepr(s.cache.Contents) :: o in old(CacheRepr(s.cache.Contents)) || fresh(o);

        s.outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id);

        assert s.I().cache == ImplModelIO.PageInResp(Ic(k), old(s.I()), IIO(io)).cache;
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
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelIO.readResponse(Ic(k), old(s.I()), IIO(io))
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
  requires IS.Inv(k, s)
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelIO.writeResponse(Ic(k), old(s.I()), IIO(io))
  {
    var id := io.getWriteResult();
    if (s.ready && s.outstandingIndirectionTableWrite == Some(id)) {
      s.outstandingIndirectionTableWrite := None;
      s.persistentIndirectionTable := s.frozenIndirectionTable;
      s.frozenIndirectionTable := null;
      s.syncReqs := BC.syncReqs2to1(s.syncReqs);
    } else if (s.ready && id in s.outstandingBlockWrites) {
      s.outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id);
    } else {
    }
  }
}
