include "Impl.i.dfy"

module ImplIO { 
  import opened Impl
  import opened MainDiskIOHandler
  import opened NativeTypes
  import opened Options
  import IS = ImplState

  method getFreeLba(s: ImplVariables, len: uint64)
  returns (loc : Option<BC.Location>)
  requires s.Ready?
  requires IS.WFVars(s)
  requires len <= LBAType.BlockSize()
  ensures loc.Some? ==> BC.ValidLocationForNode(loc.value)
  ensures loc.Some? ==> BC.ValidAllocation(IS.IVars(s), loc.value)
  ensures loc.Some? ==> loc.value.len == len
  {
    var persistent': map<uint64, (Option<BC.Location>, seq<IS.Reference>)> := s.persistentIndirectionTable.ToMap();
    var persistent: map<uint64, BC.Location> := map ref | ref in persistent' && persistent'[ref].0.Some? :: persistent'[ref].0.value;

    var ephemeral': map<uint64, (Option<BC.Location>, seq<IS.Reference>)> := s.ephemeralIndirectionTable.ToMap();
    var ephemeral := map ref | ref in ephemeral' && ephemeral'[ref].0.Some? :: ephemeral'[ref].0.value;

    var frozen: Option<map<uint64, BC.Location>> := None;
    if (s.frozenIndirectionTable.Some?) {
      var m := s.frozenIndirectionTable.value.ToMap();
      var frozen' := m;
      frozen := Some(map ref | ref in frozen' && frozen'[ref].0.Some? :: frozen'[ref].0.value);
    }

    if i: uint64 :| (
      && i as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
      && var l := i * LBAType.BlockSize();
      && BC.ValidLBAForNode(l)
      && (forall ref | ref in persistent :: persistent[ref].addr != l)
      && (forall ref | ref in ephemeral :: ephemeral[ref].addr != l)
      && (frozen.Some? ==> (forall ref | ref in frozen.value :: frozen.value[ref].addr != l))
      && (forall id | id in s.outstandingBlockWrites :: s.outstandingBlockWrites[id].loc.addr != l)
    ) {
      loc := Some(LBAType.Location(i * LBAType.BlockSize(), len));

      assert IS.IVars(s).persistentIndirectionTable.locs == persistent;
      assert IS.IVars(s).ephemeralIndirectionTable.locs == ephemeral;
      assert IS.IVars(s).frozenIndirectionTable.Some? ==>
          IS.IVars(s).frozenIndirectionTable.value.locs == frozen.value;
    } else {
      loc := None;
    }
  }

  method RequestWrite(io: DiskIOHandler, loc: LBAType.Location, sector: IS.Sector)
  returns (id: Option<D.ReqId>)
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

    var bytes := Marshalling.MarshallCheckedSector(sector);
    if (bytes == null || bytes.Length as uint64 != loc.len) {
      id := None;
    } else {
      var i := io.write(loc.addr, bytes);
      id := Some(i);

      //assert ImplADM.M.ValidReqWrite(io.diskOp().reqWrite);
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
    assume false;
  }
  /*{
    assert BT.AddMessagesToBuckets(node.pivotTable, |node.buckets|, SSTable.ISeq(node.buckets),
          map[]) == SSTable.ISeq(node.buckets);
  }*/

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
}
