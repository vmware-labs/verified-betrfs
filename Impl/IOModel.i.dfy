include "StateModel.i.dfy"
include "ByteBetreeBlockCache.i.dfy"
//
// IO functions used by various StateModel verbs.
// Updates data structures as defined in StateModel.
// Interacts with the disk via StateModel.IO, which abstracts
// MainDiskIOHandlers.s.dfy.
//
// Also, the code that reads in indirection tables and nodes.
//

module IOModel { 
  import opened StateModel
  import opened NativeTypes
  import opened Options
  import opened Maps
  import opened Bounds
  import opened BucketWeights
  import IMM = MarshallingModel
  import Marshalling = Marshalling
  import LBAType
  import BucketsLib
  import LruModel
  import M = ByteBetreeBlockCache
  import UI

  // Misc utilities

  predicate stepsBetree(k: Constants, s: BBC.Variables, s': BBC.Variables, uiop: UI.Op, step: BT.BetreeStep)
  {
    M.NextStep(Ik(k), s, s', uiop, D.NoDiskOp, M.Step(BBC.BetreeMoveStep(step)))
  }

  predicate stepsBC(k: Constants, s: BBC.Variables, s': BBC.Variables, uiop: UI.Op, io: IO, step: BC.Step)
  {
    M.NextStep(Ik(k), s, s', uiop, diskOp(io), M.Step(BBC.BlockCacheMoveStep(step)))
  }

  predicate noop(k: Constants, s: BBC.Variables, s': BBC.Variables)
  {
    M.NextStep(Ik(k), s, s', UI.NoOp, D.NoDiskOp, M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)))
  }

  // models of IO-related methods

  predicate LocAvailable(s: Variables, loc: BC.Location, len: uint64)
  requires WFVars(s)
  {
    && s.Ready?
    && BC.ValidLocationForNode(loc)
    && BC.ValidAllocation(IVars(s), loc)
    && loc.len == len
  }

  function {:opaque} getFreeLoc(s: Variables, len: uint64)
  : (res : Option<BC.Location>)
  requires s.Ready?
  requires WFVars(s)
  requires len <= LBAType.BlockSize()
  ensures res.Some? ==> 0 <= res.value.addr as int / BlockSize() < NumBlocks()
  {
    var i := BlockAllocatorModel.Alloc(s.blockAllocator);
    if i.Some? then
      Some(LBAType.Location((i.value * BlockSize()) as uint64, len))
    else
      None
  }

  lemma getFreeLocCorrect(s: Variables, len: uint64)
  requires getFreeLoc.requires(s, len);
  ensures var loc := getFreeLoc(s, len);
    && (loc.Some? ==> LocAvailable(s, loc.value, len))
  {
    reveal_getFreeLoc();
    reveal_ConsistentBitmap();
    LBAType.reveal_ValidAddr();

    var loc := getFreeLoc(s, len);
    if loc.Some? {
      var i := BlockAllocatorModel.Alloc(s.blockAllocator);

      BlockAllocatorModel.LemmaAllocResult(s.blockAllocator);
      assert !IsLocAllocBitmap(s.blockAllocator.ephemeral, i.value);
      assert s.blockAllocator.frozen.Some? ==>
          !IsLocAllocBitmap(s.blockAllocator.frozen.value, i.value);
      assert !IsLocAllocBitmap(s.blockAllocator.persistent, i.value);
      assert !IsLocAllocBitmap(s.blockAllocator.outstanding, i.value);

      //assert BC.ValidLocationForNode(loc.value);
      //assert BC.ValidAllocation(IVars(s), loc.value);
    }
  }

  predicate {:opaque} RequestWrite(io: IO, loc: LBAType.Location, sector: Sector,
      id: Option<D.ReqId>, io': IO)
  {
    var dop := diskOp(io');
    && (dop.NoDiskOp? || dop.ReqWriteOp?)
    && (dop.NoDiskOp? ==>
      && id == None
      && io' == io
    )
    && (dop.ReqWriteOp? ==> (
      var bytes: seq<byte> := dop.reqWrite.bytes;
      && |bytes| <= BlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes).Some?
      && WFSector(sector)
      // Note: we have to say this instead of just
      //     IMM.parseCheckedSector(bytes).value == sector
      // because the indirection table might not parse to an indirection table
      // with exactly the same internals.
      && ISector(IMM.parseCheckedSector(bytes).value) == ISector(sector)

      && |bytes| == loc.len as int
      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.addr, bytes))
      && io' == IOReqWrite(id.value, dop.reqWrite)
    ))
  }

  lemma RequestWriteCorrect(io: IO, loc: LBAType.Location, sector: Sector,
      id: Option<D.ReqId>, io': IO)
  requires WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(INode(sector.block))
  requires LBAType.ValidLocation(loc)
  requires RequestWrite(io, loc, sector, id, io');
  ensures M.ValidDiskOp(diskOp(io'))
  ensures id.Some? ==> M.IDiskOp(diskOp(io')) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc, ISector(sector)))
  ensures id.None? ==> M.IDiskOp(diskOp(io')) == SD.NoDiskOp
  {
    reveal_RequestWrite();
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();
  }

  predicate {:opaque} FindLocationAndRequestWrite(io: IO, s: Variables, sector: Sector,
      id: Option<D.ReqId>, loc: Option<LBAType.Location>, io': IO)
  requires s.Ready?
  requires WFVars(s)
  ensures FindLocationAndRequestWrite(io, s, sector, id, loc, io') ==>
      loc.Some? ==> 0 <= loc.value.addr as int / BlockSize() < NumBlocks()
  {
    && var dop := diskOp(io');
    && (dop.NoDiskOp? || dop.ReqWriteOp?)
    && (dop.NoDiskOp? ==> (
      && id == None
      && loc == None
      && io' == io
    ))
    && (dop.ReqWriteOp? ==> (
      var bytes: seq<byte> := dop.reqWrite.bytes;
      && |bytes| <= BlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes).Some?
      && WFSector(sector)
      && ISector(IMM.parseCheckedSector(bytes).value) == ISector(sector)

      && var len := |bytes| as uint64;
      && loc == getFreeLoc(s, len)
      && loc.Some?

      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.value.addr, bytes))
      && io' == IOReqWrite(id.value, dop.reqWrite)
    ))
  }

  lemma FindLocationAndRequestWriteCorrect(io: IO, s: Variables, sector: Sector, id: Option<D.ReqId>, loc: Option<LBAType.Location>, io': IO)
  requires WFVars(s)
  requires s.Ready?
  requires WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(INode(sector.block))
  requires FindLocationAndRequestWrite(io, s, sector, id, loc, io')
  ensures M.ValidDiskOp(diskOp(io'))
  ensures id.Some? ==> loc.Some?
  ensures id.Some? ==> LBAType.ValidLocation(loc.value)
  ensures id.Some? ==> BC.ValidAllocation(IVars(s), loc.value)
  ensures id.Some? ==> loc.value.addr != BC.IndirectionTableLBA()
  ensures id.Some? ==> M.IDiskOp(diskOp(io')) == SD.ReqWriteOp(id.value, SD.ReqWrite(loc.value, ISector(sector)))
  ensures id.None? ==> io' == io
  {
    reveal_FindLocationAndRequestWrite();
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
    Marshalling.reveal_parseSector();

    var dop := diskOp(io');
    if dop.ReqWriteOp? {
      var bytes: seq<byte> := dop.reqWrite.bytes;
      var len := |bytes| as uint64;

      getFreeLocCorrect(s, len);
    }
  }

  function {:opaque} RequestRead(io: IO, loc: LBAType.Location)
  : (res : (D.ReqId, IO))
  requires io.IOInit?
  {
    (io.id, IOReqRead(io.id, D.ReqRead(loc.addr, loc.len)))
  }

  lemma RequestReadCorrect(io: IO, loc: LBAType.Location)
  requires io.IOInit?
  requires LBAType.ValidLocation(loc)
  ensures var (id, io) := RequestRead(io, loc);
    && M.ValidDiskOp(diskOp(io))
    && M.IDiskOp(diskOp(io)) == SD.ReqReadOp(id, SD.ReqRead(loc))
  {
    reveal_RequestRead();
  }

  lemma LemmaIndirectionTableLBAValid()
  ensures M.ValidAddr(BC.IndirectionTableLBA())
  {
    LBAType.reveal_ValidAddr();
    assert BC.IndirectionTableLBA() as int == 0 * M.BlockSize();
  }

  function {:opaque} PageInIndirectionTableReq(k: Constants, s: Variables, io: IO)
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
    reveal_PageInIndirectionTableReq();
    reveal_RequestRead();
    var (s', io') := PageInIndirectionTableReq(k, s, io);
    if (s.outstandingIndirectionTableRead.None?) {
      LemmaIndirectionTableLBAValid();

      //assert BC.PageInIndirectionTableReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
      //assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(diskOp(io')), BC.PageInIndirectionTableReqStep);
      //assert BBC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(diskOp(io')), BBC.BlockCacheMoveStep(BC.PageInIndirectionTableReqStep));
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.PageInIndirectionTableReqStep);
    } else {
      assert noop(k, IVars(s), IVars(s'));
    }
  }

  function {:opaque} PageInReq(k: Constants, s: Variables, io: IO, ref: BC.Reference)
  : (res : (Variables, IO))
  requires s.Ready?
  requires io.IOInit?
  requires ref in s.ephemeralIndirectionTable.locs;
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) then (
      (s, io)
    ) else (
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var (id, io') := RequestRead(io, loc);
      var s' := s
        .(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);
      (s', io')
    )
  }

  lemma PageInReqCorrect(k: Constants, s: Variables, io: IO, ref: BC.Reference)
  requires io.IOInit?
  requires s.Ready?
  requires WFVars(s)
  requires BBC.Inv(Ik(k), IVars(s))
  requires ref in s.ephemeralIndirectionTable.locs;
  requires ref !in s.cache
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures var (s', io') := PageInReq(k, s, io, ref);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_PageInReq();
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var loc := s.ephemeralIndirectionTable.locs[ref];
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert BC.ValidLocationForNode(loc);
      var (id, io') := RequestRead(io, loc);
      reveal_RequestRead();
      var s' := s.(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);

      assert WFVars(s');

      assert BC.PageInReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')), ref);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.PageInReqStep(ref));
    }
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<Sector>) : Option<BC.Sector>
  requires sector.Some? ==> WFSector(sector.value)
  {
    match sector {
      case None => None
      case Some(sector) => Some(ISector(sector))
    }
  }

  function {:opaque} ReadSector(io: IO)
  : (res : (D.ReqId, Option<Sector>))
  requires diskOp(io).RespReadOp?
  {
    var id := io.id;
    var bytes := io.respRead.bytes;
    if |bytes| <= M.BlockSize() then (
      var sector := IMM.parseCheckedSector(bytes);
      (id, sector)
    ) else (
      (id, None)
    )
  }

  lemma ReadSectorCorrect(io: IO)
  requires diskOp(io).RespReadOp?
  ensures var (id, sector) := ReadSector(io);
    && sector.Some? ==> WFSector(sector.value)
    && M.IDiskOp(diskOp(io)) == SD.RespReadOp(id, SD.RespRead(ISectorOpt(sector)))
  {
    reveal_ReadSector();
    Marshalling.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
  }

  function {:opaque} PageInIndirectionTableResp(k: Constants, s: Variables, io: IO)
  : (s' : Variables)
  requires diskOp(io).RespReadOp?
  requires s.Unready?
  {
    ReadSectorCorrect(io);
    var (id, sector) := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) then (
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      var (succ, bm) := IndirectionTableModel.InitLocBitmap(ephemeralIndirectionTable);
      if succ then (
        var blockAllocator := BlockAllocatorModel.InitBlockAllocator(bm);
        var persistentIndirectionTable :=
            IndirectionTableModel.clone(sector.value.indirectionTable);
        Ready(persistentIndirectionTable, None, ephemeralIndirectionTable, None, map[], map[], s.syncReqs, map[], LruModel.Empty(), blockAllocator)
      ) else (
        s
      )
    ) else (
      s
    )
  }

  lemma PageInIndirectionTableRespCorrect(k: Constants, s: Variables, io: IO)
  requires Inv(k, s)
  requires diskOp(io).RespReadOp?
  requires s.Unready?
  ensures var s' := PageInIndirectionTableResp(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    reveal_PageInIndirectionTableResp(); 
    reveal_ReadSector(); 
    var (id, sector) := ReadSector(io);
    ReadSectorCorrect(io);

    Marshalling.reveal_parseSector();
    M.reveal_IBytes();
    M.reveal_Parse();

    var s' := PageInIndirectionTableResp(k, s, io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      var (succ, bm) := IndirectionTableModel.InitLocBitmap(ephemeralIndirectionTable);
      if succ {
        WeightBucketEmpty();

        reveal_ConsistentBitmap();
        IndirectionTableModel.InitLocBitmapCorrect(ephemeralIndirectionTable);
        assert ConsistentBitmap(s'.ephemeralIndirectionTable, s'.frozenIndirectionTable,
          s'.persistentIndirectionTable, s'.outstandingBlockWrites, s'.blockAllocator);

        assert WFVars(s');
        assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableRespStep);
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));

        return;
      }
    }

    assert s == s';
    assert BC.NoOp(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io)));
    assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s), UI.NoOp, M.IDiskOp(diskOp(io)), BC.NoOpStep);
    assert M.NextStep(Ik(k), IVars(s), IVars(s), UI.NoOp, diskOp(io), M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)));
    assert stepsBC(k, IVars(s), IVars(s), UI.NoOp, io, BC.NoOpStep);
  }

  function {:opaque} PageInResp(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires diskOp(io).RespReadOp?
  requires s.Ready?
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  {
    var (id, sector) := ReadSector(io);

    if (id !in s.outstandingBlockReads) then (
      s
    ) else (
      // TODO we should probably remove the id from outstandingBlockReads
      // even in the case we don't do anything with it

      var ref := s.outstandingBlockReads[id].ref;

      var locGraph := IndirectionTableModel.GetEntry(s.ephemeralIndirectionTable, ref);
      if (locGraph.None? || locGraph.value.loc.None? || ref in s.cache) then ( // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
        s
      ) else (
        var succs := locGraph.value.succs;
        if (sector.Some? && sector.value.SectorBlock?) then (
          var node := sector.value.block;
          if (succs == (if node.children.Some? then node.children.value else [])
              && id in s.outstandingBlockReads) then (
            s.(cache := s.cache[ref := sector.value.block])
             .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id))
             .(lru := LruModel.Use(s.lru, ref))
          ) else (
            s
          )
        ) else (
          s
        )
      )
    )
  }

  lemma PageInRespCorrect(k: Constants, s: Variables, io: IO)
  requires diskOp(io).RespReadOp?
  requires s.Ready?
  requires WFVars(s)
  requires BBC.Inv(Ik(k), IVars(s))
  ensures var s' := PageInResp(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    reveal_PageInResp();
    var s' := PageInResp(k, s, io);

    var (id, sector) := ReadSector(io);
    ReadSectorCorrect(io);

    Marshalling.reveal_parseSector();
    M.reveal_IBytes();
    M.reveal_Parse();

    if (id !in s.outstandingBlockReads) {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
      return;
    }

    var ref := s.outstandingBlockReads[id].ref;
    
    var locGraph := IndirectionTableModel.GetEntry(s.ephemeralIndirectionTable, ref);
    if (locGraph.None? || locGraph.value.loc.None? || ref in s.cache) { // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
      return;
    }

    var succs := locGraph.value.succs;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (succs == (if node.children.Some? then node.children.value else [])
          && id in s.outstandingBlockReads) {
        WeightBucketEmpty();

        LruModel.LruUse(s.lru, ref);

        assert |s'.cache| == |s.cache| + 1;
        assert |s'.outstandingBlockReads| == |s.outstandingBlockReads| - 1;

        assert WFVars(s');
        assert BC.PageInResp(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io)));
        assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.PageInRespStep);
      } else {
        assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
      }
    } else {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
    }
  }

  function {:opaque} readResponse(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires diskOp(io).RespReadOp?
  requires s.Ready? ==> IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  {
    if (s.Unready?) then (
      PageInIndirectionTableResp(k, s, io)
    ) else (
      PageInResp(k, s, io)
    )
  }

  lemma readResponseCorrect(k: Constants, s: Variables, io: IO)
  requires diskOp(io).RespReadOp?
  requires Inv(k, s)
  ensures var s' := readResponse(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    reveal_readResponse();
    if (s.Unready?) {
      PageInIndirectionTableRespCorrect(k, s, io);
    } else {
      PageInRespCorrect(k, s, io);
    }
  }

  // == writeResponse ==

  lemma lemmaOutstandingLocIndexValid(k: Constants, s: Variables, id: uint64)
  requires Inv(k, s)
  requires s.Ready?
  requires id in s.outstandingBlockWrites
  ensures 0 <= s.outstandingBlockWrites[id].loc.addr as int / BlockSize() < NumBlocks()
  {
    reveal_ConsistentBitmap();
    var i := s.outstandingBlockWrites[id].loc.addr as int / BlockSize();
    LBAType.reveal_ValidAddr();
    assert i * BlockSize() == s.outstandingBlockWrites[id].loc.addr as int;
    assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
  }

  lemma lemmaBlockAllocatorFrozenSome(k: Constants, s: Variables)
  requires Inv(k, s)
  requires s.Ready?
  ensures s.outstandingIndirectionTableWrite.Some?
      ==> s.blockAllocator.frozen.Some?
  {
    reveal_ConsistentBitmap();
  }

  function SyncReqs2to1Iterate(
      m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>,
      it: MutableMapModel.Iterator<BC.SyncReqStatus>,
      m0: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
    : (m' : MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  requires MutableMapModel.WFIter(m, it)
  requires MutableMapModel.Inv(m0)
  requires m0.contents.Keys == it.s
  ensures MutableMapModel.Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      MutableMapModel.LemmaIterIndexLtCount(m, it);
      MutableMapModel.CountBound(m);
      SyncReqs2to1Iterate(
        m,
        MutableMapModel.IterInc(m, it),
        MutableMapModel.Insert(m0, it.next.key,
            (if it.next.value == BC.State2 then BC.State1 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs2to1(m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
      : (m' : MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  ensures MutableMapModel.Inv(m')
  {
    SyncReqs2to1Iterate(m,
      MutableMapModel.IterStart(m),
      MutableMapModel.Constructor(128))
  }

  lemma SyncReqs2to1Correct(m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  ensures SyncReqs2to1(m).contents == BC.syncReqs2to1(m.contents)
  {
    reveal_SyncReqs2to1();
    var it := MutableMapModel.IterStart(m);
    var m0 := MutableMapModel.Constructor(128);
    while !it.next.Done?
    invariant MutableMapModel.Inv(m)
    invariant MutableMapModel.WFIter(m, it)
    invariant MutableMapModel.Inv(m0)
    invariant m0.contents.Keys == it.s
    invariant forall id | id in it.s ::
        m0.contents[id] == (if m.contents[id] == BC.State2 then BC.State1 else m.contents[id])
    invariant SyncReqs2to1(m) == SyncReqs2to1Iterate(m, it, m0)
    decreases it.decreaser
    {
      MutableMapModel.LemmaIterIndexLtCount(m, it);
      MutableMapModel.CountBound(m);
      m0 := MutableMapModel.Insert(m0, it.next.key,
          (if it.next.value == BC.State2 then BC.State1 else it.next.value));
      it := MutableMapModel.IterInc(m, it);
    }
  }

  function SyncReqs3to2Iterate(
      m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>,
      it: MutableMapModel.Iterator<BC.SyncReqStatus>,
      m0: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
    : (m' : MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  requires MutableMapModel.WFIter(m, it)
  requires MutableMapModel.Inv(m0)
  requires m0.contents.Keys == it.s
  ensures MutableMapModel.Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      MutableMapModel.LemmaIterIndexLtCount(m, it);
      MutableMapModel.CountBound(m);
      SyncReqs3to2Iterate(
        m,
        MutableMapModel.IterInc(m, it),
        MutableMapModel.Insert(m0, it.next.key,
            (if it.next.value == BC.State3 then BC.State2 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs3to2(m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
      : (m' : MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  ensures MutableMapModel.Inv(m')
  {
    SyncReqs3to2Iterate(m,
      MutableMapModel.IterStart(m),
      MutableMapModel.Constructor(128))
  }

  lemma SyncReqs3to2Correct(m: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  requires MutableMapModel.Inv(m)
  ensures SyncReqs3to2(m).contents == BC.syncReqs3to2(m.contents)
  {
    reveal_SyncReqs3to2();
    var it := MutableMapModel.IterStart(m);
    var m0 := MutableMapModel.Constructor(128);
    while !it.next.Done?
    invariant MutableMapModel.Inv(m)
    invariant MutableMapModel.WFIter(m, it)
    invariant MutableMapModel.Inv(m0)
    invariant m0.contents.Keys == it.s
    invariant forall id | id in it.s ::
        m0.contents[id] == (if m.contents[id] == BC.State3 then BC.State2 else m.contents[id])
    invariant SyncReqs3to2(m) == SyncReqs3to2Iterate(m, it, m0)
    decreases it.decreaser
    {
      MutableMapModel.LemmaIterIndexLtCount(m, it);
      MutableMapModel.CountBound(m);
      m0 := MutableMapModel.Insert(m0, it.next.key,
          (if it.next.value == BC.State3 then BC.State2 else it.next.value));
      it := MutableMapModel.IterInc(m, it);
    }
  }

  function {:opaque} writeResponse(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires Inv(k, s)
  requires diskOp(io).RespWriteOp?
  requires s.Ready? && s.outstandingIndirectionTableWrite.Some? ==> s.frozenIndirectionTable.Some?
  {
    var id := io.id;

    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) then (
      lemmaBlockAllocatorFrozenSome(k, s);
      s.(outstandingIndirectionTableWrite := None)
             .(frozenIndirectionTable := None) // frozenIndirectiontable is moved to persistentIndirectionTable
             .(persistentIndirectionTable := s.frozenIndirectionTable.value)
             .(syncReqs := SyncReqs2to1(s.syncReqs))
             .(blockAllocator := BlockAllocatorModel.MoveFrozenToPersistent(s.blockAllocator))
    ) else if (s.Ready? && id in s.outstandingBlockWrites) then (
      lemmaOutstandingLocIndexValid(k, s, id);
      s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id))
       .(blockAllocator := BlockAllocatorModel.MarkFreeOutstanding(s.blockAllocator, s.outstandingBlockWrites[id].loc.addr as int / BlockSize()))
    ) else (
      s
    )
  }

  lemma writeResponseCorrect(k: Constants, s: Variables, io: IO)
  requires Inv(k, s)
  requires diskOp(io).RespWriteOp?
  ensures var s' := writeResponse(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    reveal_writeResponse();
    reveal_ConsistentBitmap();
    var id := io.id;
    var s' := writeResponse(k, s, io);
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      lemmaBlockAllocatorFrozenSome(k, s);
      SyncReqs2to1Correct(s.syncReqs);
      assert WFVars(s');
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      var locIdx := s.outstandingBlockWrites[id].loc.addr as int / BlockSize();
      lemmaOutstandingLocIndexValid(k, s, id);

      LBAType.reveal_ValidAddr();
      assert locIdx * BlockSize() == s.outstandingBlockWrites[id].loc.addr as int;

      BitmapModel.reveal_BitUnset();
      BitmapModel.reveal_IsSet();

      /*forall i | 0 <= i < NumBlocks()
      ensures Bitmap.IsSet(s'.blockAllocator.full, i) == (
          || Bitmap.IsSet(s'.blockAllocator.ephemeral, i)
          || (s'.blockAllocator.frozen.Some? && Bitmap.IsSet(s'.blockAllocator.frozen.value, i))
          || Bitmap.IsSet(s'.blockAllocator.persistent, i)
          || Bitmap.IsSet(s'.blockAllocator.full, i)
        )
      {
        if i == locIdx {
          assert Bitmap.IsSet(s'.blockAllocator.full, i) == (
              || Bitmap.IsSet(s'.blockAllocator.ephemeral, i)
              || (s'.blockAllocator.frozen.Some? && Bitmap.IsSet(s'.blockAllocator.frozen.value, i))
              || Bitmap.IsSet(s'.blockAllocator.persistent, i)
              || Bitmap.IsSet(s'.blockAllocator.full, i)
          );
        } else {
          assert Bitmap.IsSet(s'.blockAllocator.full, i) == Bitmap.IsSet(s.blockAllocator.full, i);
          assert Bitmap.IsSet(s'.blockAllocator.ephemeral, i) == Bitmap.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> Bitmap.IsSet(s'.blockAllocator.frozen.value, i) == Bitmap.IsSet(s.blockAllocator.frozen.value, i);
          assert Bitmap.IsSet(s'.blockAllocator.persistent, i) == Bitmap.IsSet(s.blockAllocator.persistent, i);
          assert Bitmap.IsSet(s'.blockAllocator.outstanding, i) == Bitmap.IsSet(s.blockAllocator.outstanding, i);
        }
      }*/

      forall i: int
      | IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
      ensures IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
      {
        if i != locIdx {
          assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
          assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
          assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
        } else {
          var id1 :| id1 in s'.outstandingBlockWrites && s'.outstandingBlockWrites[id1].loc.addr as int == i * BlockSize() as int;
          assert BC.OutstandingBlockWritesDontOverlap(s.outstandingBlockWrites, id, id1);
          /*assert s.outstandingBlockWrites[id1].loc.addr as int
              == s'.outstandingBlockWrites[id1].loc.addr as int
              == i * BlockSize() as int;
          assert id == id1;
          assert id !in s'.outstandingBlockWrites;
          assert false;*/
        }
      }

      forall i: int
      | IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
      ensures IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
      {
        if i != locIdx {
          assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
          assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
        } else {
          assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
        }
      }

      assert WFVars(s');
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackRespStep);
    } else {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
    }
  }
}
