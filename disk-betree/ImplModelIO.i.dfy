include "ImplModel.i.dfy"
include "ByteBetreeBlockCache.i.dfy"

module ImplIO { 
  import opened ImplModel
  import opened NativeTypes
  import opened Options
  import opened Maps
  import IMM = ImplMarshallingModel
  import Marshalling = Marshalling
  import LBAType
  import BucketsLib
  import M = ByteBetreeBlockCache
  import UI

  predicate LocAvailable(s: Variables, loc: BC.Location, len: uint64)
  {
    && s.Ready?
    && BC.ValidLocationForNode(loc)
    && BC.ValidAllocation(IVars(s), loc)
    && loc.len == len
  }

  predicate addrNotUsedInIndirectionTable(addr: uint64, indirectionTable: IndirectionTable)
  {
    && (forall ref | ref in indirectionTable && indirectionTable[ref].0.Some?  ::
          indirectionTable[ref].0.value.addr != addr)
  }

  function getFreeLocIterate(s: Variables, len: uint64, i: uint64)
  : (loc : Option<BC.Location>)
  requires s.Ready?
  requires WFVars(s)
  requires len <= LBAType.BlockSize()
  requires i as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
  ensures loc.Some? ==> LocAvailable(s, loc.value, len)
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if (
      && var addr := i * LBAType.BlockSize();
      && BC.ValidLBAForNode(addr)
      && addrNotUsedInIndirectionTable(addr, s.persistentIndirectionTable)
      && addrNotUsedInIndirectionTable(addr, s.ephemeralIndirectionTable)
      && (s.frozenIndirectionTable.Some? ==> addrNotUsedInIndirectionTable(addr, s.frozenIndirectionTable.value))
      && (forall id | id in s.outstandingBlockWrites :: s.outstandingBlockWrites[id].loc.addr != addr)
    ) then (
      Some(LBAType.Location(i * LBAType.BlockSize(), len))
    ) else if (i+1) as int >= 0x1_0000_0000_0000_0000 as int / LBAType.BlockSize() as int then (
      None
    ) else (
      getFreeLocIterate(s, len, i+1)
    )
  }

  function {:opaque} getFreeLoc(s: Variables, len: uint64)
  : (loc : Option<BC.Location>)
  requires s.Ready?
  requires WFVars(s)
  requires len <= LBAType.BlockSize()
  ensures loc.Some? ==> LocAvailable(s, loc.value, len)
  {
    getFreeLocIterate(s, len, 0)
  }

  predicate RequestWrite(loc: LBAType.Location, sector: Sector, id: Option<D.ReqId>, dop: D.DiskOp)
  {
    && (dop.NoDiskOp? || dop.ReqWriteOp?)
    && (dop.NoDiskOp? ==> id == None)
    && (dop.ReqWriteOp? ==> (
      var bytes: seq<byte> := dop.reqWrite.bytes;
      && |bytes| <= IMM.BlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes) == Some(sector)

      && |bytes| == loc.len as int
      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.addr, bytes))
    ))
  }

  lemma RequestWriteCorrect(loc: LBAType.Location, sector: Sector, id: Option<D.ReqId>, dop: D.DiskOp)
  requires WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(INode(sector.block))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block)
  requires LBAType.ValidLocation(loc)
  requires RequestWrite(loc, sector, id, dop);
  ensures M.ValidDiskOp(dop)
  ensures id.Some? ==> M.IDiskOp(dop) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc, ISector(sector)))
  ensures id.None? ==> M.IDiskOp(dop) == SD.NoDiskOp
  {
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();
  }

  predicate FindLocationAndRequestWrite(s: Variables, sector: Sector, id: Option<D.ReqId>, loc: Option<LBAType.Location>, dop: D.DiskOp)
  requires s.Ready?
  requires WFVars(s)
  {
    && (dop.NoDiskOp? || dop.ReqWriteOp?)
    && (dop.NoDiskOp? ==> id == None && loc == None)
    && (dop.ReqWriteOp? ==> (
      var bytes: seq<byte> := dop.reqWrite.bytes;
      && |bytes| <= IMM.BlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes) == Some(sector)

      && var len := |bytes| as uint64;
      && loc == getFreeLoc(s, len)
      && loc.Some?

      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.value.addr, bytes))
    ))
  }

  lemma FindLocationAndRequestWriteCorrect(s: Variables, sector: Sector, id: Option<D.ReqId>, loc: Option<LBAType.Location>, dop: D.DiskOp)
  requires WFVars(s)
  requires s.Ready?
  requires WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(INode(sector.block))
  requires sector.SectorBlock? ==> IMM.CappedNode(sector.block)
  requires FindLocationAndRequestWrite(s, sector, id, loc, dop)
  ensures M.ValidDiskOp(dop)
  ensures id.Some? ==> loc.Some?
  ensures id.Some? ==> LBAType.ValidLocation(loc.value)
  ensures id.Some? ==> BC.ValidAllocation(IVars(s), loc.value)
  ensures id.Some? ==> loc.value.addr != BC.IndirectionTableLBA()
  ensures id.Some? ==> M.IDiskOp(dop) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc.value, ISector(sector)))
  ensures id.None? ==> M.IDiskOp(dop) == SD.NoDiskOp
  {
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();
  }

  function RequestRead(io: IO, loc: LBAType.Location)
  : (res : (D.ReqId, IO))
  requires io.IOInit?
  requires LBAType.ValidLocation(loc)
  ensures var (id, io) := res;
    && M.ValidDiskOp(diskOp(io))
    && M.IDiskOp(diskOp(io)) == SD.ReqReadOp(id, SD.ReqRead(loc))
  {
    (io.id, IOReqRead(io.id, D.ReqRead(loc.addr, loc.len)))
  }

  lemma LemmaIndirectionTableLBAValid()
  ensures M.ValidAddr(BC.IndirectionTableLBA())
  {
    LBAType.reveal_ValidAddr();
    assert BC.IndirectionTableLBA() as int == 0 * M.BlockSize();
  }

  function PageInIndirectionTableReq(k: Constants, s: Variables, io: IO)
  : (res : (Variables, IO))
  requires io.IOInit?
  requires s.Unready?
  {
    if (s.outstandingIndirectionTableRead.None?) then (
      LemmaIndirectionTableLBAValid();
      var (id, io') := RequestRead(io, BC.IndirectionTableLocation());
      var s' := Unready(Some(id), s.syncReqs);
      (s', io')
    ) else (
      (s, io)
    )
  }

  lemma PageInIndirectionTableReqCorrect(k: Constants, s: Variables, io: IO)
  requires WFVars(s)
  requires io.IOInit?
  requires s.Unready?
  ensures var (s', io') := PageInIndirectionTableReq(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp, diskOp(io'))
  {
    /*if (s.outstandingIndirectionTableRead.None?) {
      LemmaIndirectionTableLBAValid();
      var id := RequestRead(io, BC.IndirectionTableLocation());
      s' := IS.Unready(Some(id), s.syncReqs);

      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableReqStep);
    } else {
      s' := s;
      assert noop(k, IS.IVars(s), IS.IVars(s'));
      print "PageInIndirectionTableReq: request already out\n";
    }*/
    assume false;
  }

  /*method PageInReq(k: ImplConstants, s: Variables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': Variables)
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
  }*/

  /*
  lemma INodeRootEqINodeForEmptyRootBucket(node: IS.Node)
  requires IS.WFNode(node)
  ensures IS.INodeRoot(node, TTT.EmptyTree) == IS.INode(node);
  {
    BucketsLib.BucketListFlushParentEmpty(KMTable.ISeq(node.buckets), node.pivotTable);
  }

  /*lemma LemmaPageInBlockCacheSet(s: Variables, ref: BT.G.Reference, node: IS.Node)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref !in s.cache
  requires IS.WFNode(node)
  ensures IS.ICache(s.cache, s.rootBucket)[ref := IS.INode(node)]
       == IS.ICache(s.cache[ref := node], s.rootBucket);
  {
    if (ref == BT.G.Root()) {
      //assert TTT.I(rootBucket) == map[];
      //assert BT.AddMessagesToBuckets(node.pivotTable, |node.buckets|, SSTable.ISeq(node.buckets),
      //    map[]) == IS.INode(node).buckets;
      INodeRootEqINodeForEmptyRootBucket(node);
      assert IS.INodeRoot(node, s.rootBucket) == IS.INode(node);
    }
    assert IS.INodeForRef(s.cache[ref := node], ref, s.rootBucket) == IS.INode(node);
    assert IS.ICache(s.cache[ref := node], s.rootBucket)[ref] == IS.INode(node);
  }*/

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

  method PageInIndirectionTableResp(k: ImplConstants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
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

  method PageInResp(k: ImplConstants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
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

  method readResponse(k: ImplConstants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
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

  method writeResponse(k: ImplConstants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
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
