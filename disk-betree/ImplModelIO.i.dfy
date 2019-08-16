include "ImplModel.i.dfy"

module ImplIO { 
  import opened ImplModel
  import opened NativeTypes
  import opened Options
  import opened Maps
  import BucketsLib

  predicate LocAvailable(k: Constants, s: Variables, loc: BC.Location, len: uint64)
  {
    && s.Ready?
    && BC.ValidLocationForNode(loc)
    && BC.ValidAllocation(I(k, s), loc)
    && loc.len == len
  }

  predicate addrNotUsedInIndirectionTable(addr: uint64, indirectionTable: IndirectionTable)
  {
    && (forall ref | ref in indirectionTable && indirectionTable[ref].0.Some?  ::
          indirectionTable[ref].0.addr != addr)
  }

  function getFreeLocIterate(s: Variables, len: uint64, i: uint64)
  requires s.Ready?
  requires IS.WFVars(s)
  requires len <= LBAType.BlockSize()
  requires i as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
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
    ) else if i >= 0x1_0000_0000_0000_0000 / LBAType.BlockSize()
      None
    ) else (
      getFreeLocIterate(s, i+1)
    )
  }

  function {:opaque} getFreeLoc(s: ImplVariables, len: uint64)
  : (loc : Option<BC.Location>)
  requires s.Ready?
  requires IS.WFVars(s)
  requires len <= LBAType.BlockSize()
  ensures loc.Some? ==> LocAvailable(k, s, loc.value, len)
  {
    getFreeLocIterate(s, len, 0)
  }

  function RequestWrite(loc: LBAType.Location, sector: IS.Sector)
  returns (id: Option<D.ReqId>, diskOp: DiskOp)
  requires IS.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(IS.INode(sector.block))
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  requires io.initialized()
  requires LBAType.ValidLocation(loc)
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures id.Some? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc, IS.ISector(sector)))
  ensures id.None? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.NoDiskOp
  {
    Marshalling.reveal_parseCheckedSector();
    ImplADM.M.reveal_IBytes();
    ImplADM.M.reveal_ValidCheckedBytes();
    ImplADM.M.reveal_Parse();
    D.reveal_ChecksumChecksOut();

    var bytes: seq<byte> := MarshallingModel.MarshallCheckedSector(sector);
    if (bytes == null || bytes.Length as uint64 != loc.len) {
      id := None;
    } else {
      var i := io.write(loc.addr, bytes);
      id := Some(i);
    }
  }

  method FindLocationAndRequestWrite(s: ImplVariables, io: DiskIOHandler, sector: IS.Sector)
  returns (id: Option<D.ReqId>, loc: Option<LBAType.Location>)
  requires IS.WFVars(s)
  requires s.Ready?
  requires IS.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(IS.INode(sector.block))
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  requires io.initialized()
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures id.Some? ==> loc.Some?
  ensures id.Some? ==> LBAType.ValidLocation(loc.value)
  ensures id.Some? ==> BC.ValidAllocation(old(IS.IVars(s)), loc.value)
  ensures id.Some? ==> loc.value.addr != BC.IndirectionTableLBA()
  ensures id.Some? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc.value, IS.ISector(sector)))
  ensures id.None? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.NoDiskOp
  {
    Marshalling.reveal_parseCheckedSector();
    ImplADM.M.reveal_IBytes();
    ImplADM.M.reveal_ValidCheckedBytes();
    ImplADM.M.reveal_Parse();
    D.reveal_ChecksumChecksOut();

    var bytes := Marshalling.MarshallCheckedSector(sector);
    if (bytes == null) {
      id := None;
      loc := None;
    } else {
      var len := bytes.Length as uint64;
      loc := getFreeLba(s, len);
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
  requires LBAType.ValidLocation(loc)
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqReadOp(id, SD.ReqRead(loc))
  {
    id := io.read(loc.addr, loc.len);
  }

  lemma LemmaIndirectionTableLBAValid()
  ensures ImplADM.M.ValidAddr(BC.IndirectionTableLBA())
  {
    LBAType.reveal_ValidAddr();
    assert BC.IndirectionTableLBA() as int == 0 * ImplADM.M.BlockSize();
  }

  method PageInIndirectionTableReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.outstandingIndirectionTableRead.None?) {
      LemmaIndirectionTableLBAValid();
      var id := RequestRead(io, BC.IndirectionTableLocation());
      s' := IS.Unready(Some(id), s.syncReqs);

      assert stepsBC(k, IS.IVars(s), IS.IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableReqStep);
    } else {
      s' := s;
      assert noop(k, IS.IVars(s), IS.IVars(s'));
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

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

  lemma INodeRootEqINodeForEmptyRootBucket(node: IS.Node)
  requires IS.WFNode(node)
  ensures IS.INodeRoot(node, TTT.EmptyTree) == IS.INode(node);
  {
    BucketsLib.BucketListFlushParentEmpty(KMTable.ISeq(node.buckets), node.pivotTable);
  }

  /*lemma LemmaPageInBlockCacheSet(s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
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
}
