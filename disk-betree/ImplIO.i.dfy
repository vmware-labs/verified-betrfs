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
  import opened IS = ImplState

  type DiskIOHandler = MainDiskIOHandler.DiskIOHandler

  method addrUsedInIndirectionTable(addr: uint64, indirectionTable:IS.MutIndirectionTable) returns (used:bool)
    ensures !used == ImplModelIO.addrNotUsedInIndirectionTable(addr, IS.IIndirectionTable(indirectionTable))
  {
  }

  method addrUsedInOutstandingBlockWrites(s: ImplVariables, addr: uint64) returns (used:bool)
    requires s.Ready?
    ensures forall id | id in s.outstandingBlockWrites :: s.outstandingBlockWrites[id].loc.addr != addr
  {
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
  requires s.Ready?
  requires IS.WFVars(s)
  requires len <= LBAType.BlockSize()
  ensures loc == ImplModelIO.getFreeLoc(IS.IVars(s), len)
  {
    ImplModelIO.reveal_getFreeLoc();
    var maxOffset := MaxOffset();
    var tryOffset:uint64 := 0;
    while (tryOffset < maxOffset)
        invariant tryOffset as int * LBAType.BlockSize() as int <= 0x1_0000_0000_0000_0000
        invariant forall offset :: 0 <= offset < tryOffset
            ==> ImplModelIO.getFreeLocIterate(IS.IVars(s), len, offset).None?
    {
        var addr : uint64 := tryOffset * LBAType.BlockSize();
        var persistentUsed := addrUsedInIndirectionTable(addr, s.persistentIndirectionTable);
        var ephemeralUsed := addrUsedInIndirectionTable(addr, s.ephemeralIndirectionTable);
        var frozenUsed := false;
        if s.frozenIndirectionTable.Some? {
          frozenUsed := addrUsedInIndirectionTable(addr, s.frozenIndirectionTable.value);
        }
        var outstandingUsed := addrUsedInOutstandingBlockWrites(s, addr);
        if (
            && BC.ValidLBAForNode(addr)
            && !persistentUsed
            && !ephemeralUsed
            && !frozenUsed
            && !outstandingUsed
          ) {
            var result := Some(LBAType.Location(addr, len));
            assert result == ImplModelIO.getFreeLocIterate(IS.IVars(s), len, tryOffset);
            return result;
          }
      assert ImplModelIO.getFreeLocIterate(IS.IVars(s), len, tryOffset).None?;
      tryOffset := tryOffset + 1;     
    }
    return None;
  }

  method RequestWrite(io: DiskIOHandler, loc: LBAType.Location, sector: IS.Sector)
  returns (id: Option<D.ReqId>)
  requires IS.WFSector(sector)
  requires IM.WFSector(IS.ISector(sector))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block);
  requires io.initialized()
  modifies io
  ensures ImplModelIO.RequestWrite(old(IIO(io)), loc, ISector(sector), id, IIO(io))
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
  requires IS.WFVars(s)
  requires s.Ready?
  requires IS.WFSector(sector)
  requires IM.WFSector(IS.ISector(sector))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block);
  requires io.initialized()
  modifies io
  ensures ImplModelIO.FindLocationAndRequestWrite(old(IIO(io)), IS.IVars(s), ISector(sector), id, loc, IIO(io))
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
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures IS.WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelIO.PageInIndirectionTableReq(Ic(k), old(IVars(s)), old(IIO(io)))
  {
    ImplModelIO.reveal_PageInIndirectionTableReq();

    if (s.outstandingIndirectionTableRead.None?) {
      var id := RequestRead(io, BC.IndirectionTableLocation());
      s' := IS.Unready(Some(id), s.syncReqs);
    } else {
      s' := s;
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  /*
  method PageInReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': ImplVariables)
  requires io.initialized();
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).locs
  requires ref !in s.cache
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      s' := s;
      assert noop(k, IS.IVars(s), IS.IVars(s'));
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      assert lba.Some?;
      assert BC.ValidLocationForNode(lba.value);
      var id := RequestRead(io, lba.value);
      s' := s.(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);

      assert BC.PageInReq(k, IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.PageInReqStep(ref));
    }
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<IS.Sector>) : Option<BC.Sector>
  requires sector.Some? ==> IS.WFSector(sector.value)
  reads if sector.Some? && sector.value.SectorIndirectionTable? then sector.value.indirectionTable.Repr else {}
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
  ensures ImplADM.M.IDiskOp(io.diskOp()) == SD.RespReadOp(id, SD.RespRead(ISectorOpt(sector)))
  {
    Marshalling.reveal_parseCheckedSector();
    ImplADM.M.reveal_IBytes();
    ImplADM.M.reveal_ValidCheckedBytes();
    ImplADM.M.reveal_Parse();
    D.reveal_ChecksumChecksOut();

    var id1, bytes := io.getReadResult();
    id := id1;
    if |bytes| <= ImplADM.M.BlockSize() {
      var sectorOpt := Marshalling.ParseCheckedSector(bytes);
      sector := sectorOpt;
    } else {
      sector := None;
    }
  }

  method PageInIndirectionTableResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.diskOp().RespReadOp?
  requires s.Unready?
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var persistentIndirectionTable := sector.value.indirectionTable.Clone();
      var ephemeralIndirectionTable := sector.value.indirectionTable.Clone();
      s' := IS.Ready(persistentIndirectionTable, None, ephemeralIndirectionTable, None, map[], map[], s.syncReqs, map[], TTT.EmptyTree);
      assert IS.WFVars(s');
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableRespStep);
      assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp());
    } else {
      s' := s;
      assert ImplADM.M.NextStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp(), ImplADM.M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)));
      assert stepsBC(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);

    if (id !in s.outstandingBlockReads) {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;
    
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if (lbaGraph.None? || lbaGraph.value.0.None? || ref in s.cache) { // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: ref !in lbas or ref in s.cache\n";
      return;
    }

    assert lbaGraph.Some? && lbaGraph.value.0.Some?;
    var lba := lbaGraph.value.0.value;
    var graph := lbaGraph.value.1;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.value.block])
               .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id));

        INodeRootEqINodeForEmptyRootBucket(node);

        assert BC.PageInResp(k, old(IS.IVars(s)), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.PageInRespStep);
      } else {
        s' := s;
        assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
      print "giving up; block read in was not block\n";
    }
  }

  method readResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableResp(k, s, io);
    } else {
      s' := PageInResp(k, s, io);
    }
  }

  // == writeResponse ==

  method writeResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespWriteOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id := io.getWriteResult();
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      s' := s.(outstandingIndirectionTableWrite := None)
             .(frozenIndirectionTable := None) // frozenIndirectiontable is moved to persistentIndirectionTable
             .(persistentIndirectionTable := s.frozenIndirectionTable.value)
             .(syncReqs := BC.syncReqs2to1(s.syncReqs));
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      s' := s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id));
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.WriteBackRespStep);
    } else {
      s' := s;
      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.NoOpStep);
    }
  }
*/
}
