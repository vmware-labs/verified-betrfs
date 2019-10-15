include "ImplModel.i.dfy"
include "ByteBetreeBlockCache.i.dfy"

module ImplModelIO { 
  import opened ImplModel
  import opened NativeTypes
  import opened Options
  import opened Maps
  import opened Bounds
  import opened BucketWeights
  import IMM = ImplMarshallingModel
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
  : (res : (Variables, Option<BC.Location>))
  requires s.Ready?
  requires WFVars(s)
  requires len <= LBAType.BlockSize()
  {
    var (i, bm') := Bitmap.BitAlloc(s.locBitmap);
    var loc := if i.Some? then
      Some(LBAType.Location((i.value * BlockSize()) as uint64, len))
    else
      None;
    var s' := s.(locBitmap := bm');
    (s', loc)
  }

  lemma getFreeLocCorrect(s: Variables, len: uint64)
  requires getFreeLoc.requires(s, len);
  ensures var (s', loc) := getFreeLoc(s, len);
    && (loc.Some? ==> LocAvailable(s, loc.value, len))
  {
    reveal_getFreeLoc();
    reveal_ConsistentBitmap();
    LBAType.reveal_ValidAddr();

    Bitmap.LemmaBitAllocResult(s.locBitmap);

    var (s', loc) := getFreeLoc(s, len);
    if loc.Some? {
      var (i, bm') := Bitmap.BitAlloc(s.locBitmap);
      assert !Bitmap.IsSet(s.locBitmap, i.value);
      //assert IsLocFree(s, i.value);
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
      s': Variables, id: Option<D.ReqId>, loc: Option<LBAType.Location>, io': IO)
  requires s.Ready?
  requires WFVars(s)
  {
    && var dop := diskOp(io');
    && (dop.NoDiskOp? || dop.ReqWriteOp?)
    && (dop.NoDiskOp? ==> (
      && id == None
      && loc == None
      && io' == io
      && s' == s
    ))
    && (dop.ReqWriteOp? ==> (
      var bytes: seq<byte> := dop.reqWrite.bytes;
      && |bytes| <= BlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes).Some?
      && WFSector(sector)
      && ISector(IMM.parseCheckedSector(bytes).value) == ISector(sector)

      && var len := |bytes| as uint64;
      && (s', loc) == getFreeLoc(s, len)
      && loc.Some?

      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.value.addr, bytes))
      && io' == IOReqWrite(id.value, dop.reqWrite)
    ))
  }

  lemma FindLocationAndRequestWriteCorrect(io: IO, s: Variables, sector: Sector, s': Variables, id: Option<D.ReqId>, loc: Option<LBAType.Location>, io': IO)
  requires WFVars(s)
  requires s.Ready?
  requires WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(INode(sector.block))
  requires FindLocationAndRequestWrite(io, s, sector, s', id, loc, io')
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

  function RequestRead(io: IO, loc: LBAType.Location)
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

  function PageInReq(k: Constants, s: Variables, io: IO, ref: BC.Reference)
  : (res : (Variables, IO))
  requires s.Ready?
  requires io.IOInit?
  requires ref in s.ephemeralIndirectionTable.contents;
  requires s.ephemeralIndirectionTable.contents[ref].0.Some?;
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) then (
      (s, io)
    ) else (
      var loc := s.ephemeralIndirectionTable.contents[ref].0.value;
      var (id, io') := RequestRead(io, loc);
      var s' := s
        .(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);
        .(locBitmap := 
      (s', io')
    )
  }

  lemma PageInReqCorrect(k: Constants, s: Variables, io: IO, ref: BC.Reference)
  requires io.IOInit?
  requires s.Ready?
  requires WFVars(s)
  requires BBC.Inv(Ik(k), IVars(s))
  requires ref in s.ephemeralIndirectionTable.contents;
  requires s.ephemeralIndirectionTable.contents[ref].0.Some?;
  requires ref !in s.cache
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures var (s', io') := PageInReq(k, s, io, ref);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var loc := s.ephemeralIndirectionTable.contents[ref].0.value;
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert BC.ValidLocationForNode(loc);
      var (id, io') := RequestRead(io, loc);
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

  function ReadSector(io: IO)
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
    Marshalling.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    IMM.reveal_parseCheckedSector();
    M.reveal_IBytes();
    M.reveal_ValidCheckedBytes();
    M.reveal_Parse();
    D.reveal_ChecksumChecksOut();
  }

  function initLocBitmapIterate(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<(Option<BC.Location>, seq<Reference>)>,
      bm: Bitmap.BitmapModel)
  : (bool, Bitmap.BitmapModel)
  requires MutableMapModel.Inv(indirectionTable)
  requires MutableMapModel.WFIter(indirectionTable, it)
  requires BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
  requires Bitmap.Len(bm) == NumBlocks()
  {
    if it.next.None? then (
      (true, bm)
    ) else (
      var loc: uint64 := it.next.value.1.0.value.addr;
      var locIndex: uint64 := loc / BlockSize() as uint64;
      if locIndex < NumBlocks() as uint64 then (
        initLocBitmapIterate(indirectionTable,
            MutableMapModel.IterInc(indirectionTable, it),
            Bitmap.BitSet(bm, locIndex as int))
      ) else (
        (false, bm)
      )
    )
  }

  function initLocBitmap(indirectionTable: IndirectionTable) : (bool, Bitmap.BitmapModel)
  requires MutableMapModel.Inv(indirectionTable)
  {
    initLocBitmapIterate(indirectionTable,
        MutableMapModel.IterStart(indirectionTable),
        Bitmap.EmptyBitmap(NumBlocks()))
  }

  function PageInIndirectionTableResp(k: Constants, s: Variables, io: IO)
  : (s' : Variables)
  requires diskOp(io).RespReadOp?
  requires s.Unready?
  {
    var (id, sector) := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) then (
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      var (succ, bm) := initLocBitmap(ephemeralIndirectionTable);
      if succ then (
        var persistentIndirectionTable := sector.value.indirectionTable;
        Ready(persistentIndirectionTable, None, ephemeralIndirectionTable, None, map[], map[], s.syncReqs, map[], LruModel.Empty(), bm)
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
    var (id, sector) := ReadSector(io);
    ReadSectorCorrect(io);

    Marshalling.reveal_parseSector();
    M.reveal_IBytes();
    M.reveal_Parse();

    var s' := PageInIndirectionTableResp(k, s, io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      WeightBucketEmpty();
      assert WFVars(s');
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.PageInIndirectionTableRespStep);
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else {
      assert s == s';
      assert BC.NoOp(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io)));
      assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s), UI.NoOp, M.IDiskOp(diskOp(io)), BC.NoOpStep);
      assert M.NextStep(Ik(k), IVars(s), IVars(s), UI.NoOp, diskOp(io), M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)));
      assert stepsBC(k, IVars(s), IVars(s), UI.NoOp, io, BC.NoOpStep);
    }
  }

  function PageInResp(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires diskOp(io).RespReadOp?
  requires s.Ready?
  {
    var (id, sector) := ReadSector(io);

    if (id !in s.outstandingBlockReads) then (
      s
    ) else (
      // TODO we should probably remove the id from outstandingBlockReads
      // even in the case we don't do anything with it

      var ref := s.outstandingBlockReads[id].ref;

      var locGraph := MapLookupOption(s.ephemeralIndirectionTable.contents, ref);
      if (locGraph.None? || locGraph.value.0.None? || ref in s.cache) then ( // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
        s
      ) else (
        var graph := locGraph.value.1;
        if (sector.Some? && sector.value.SectorBlock?) then (
          var node := sector.value.block;
          if (graph == (if node.children.Some? then node.children.value else [])
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
    
    var locGraph := MapLookupOption(s.ephemeralIndirectionTable.contents, ref);
    if (locGraph.None? || locGraph.value.0.None? || ref in s.cache) { // ref !in I(s.ephemeralIndirectionTable).locs || ref in s.cache
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
      return;
    }

    var graph := locGraph.value.1;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])
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

  function readResponse(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires diskOp(io).RespReadOp?
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
    if (s.Unready?) {
      PageInIndirectionTableRespCorrect(k, s, io);
    } else {
      PageInRespCorrect(k, s, io);
    }
  }

  // == writeResponse ==

  function writeResponse(k: Constants, s: Variables, io: IO)
  : (s': Variables)
  requires diskOp(io).RespWriteOp?
  requires s.Ready? && s.outstandingIndirectionTableWrite.Some? ==> s.frozenIndirectionTable.Some?
  {
    var id := io.id;
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) then (
      s.(outstandingIndirectionTableWrite := None)
             .(frozenIndirectionTable := None) // frozenIndirectiontable is moved to persistentIndirectionTable
             .(persistentIndirectionTable := s.frozenIndirectionTable.value)
             .(syncReqs := BC.syncReqs2to1(s.syncReqs))
    ) else if (s.Ready? && id in s.outstandingBlockWrites) then (
      s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id))
    ) else (
      s
    )
  }

  lemma writeResponseCorrect(k: Constants, s: Variables, io: IO)
  requires diskOp(io).RespWriteOp?
  requires WFVars(s)
  requires BBC.Inv(Ik(k), IVars(s))
  ensures var s' := writeResponse(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    var id := io.id;
    var s' := writeResponse(k, s, io);
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackRespStep);
    } else {
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.NoOpStep);
    }
  }
}
