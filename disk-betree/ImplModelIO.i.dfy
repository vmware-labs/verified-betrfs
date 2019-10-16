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
    var i := BlockAllocator.Alloc(s.blockAllocator);
    if i.Some? then
      (
        s.(blockAllocator := BlockAllocator.MarkUsed(s.blockAllocator, i.value)),
        Some(LBAType.Location((i.value * BlockSize()) as uint64, len))
      )
    else
      (s, None)
  }

  lemma getFreeLocCorrect(s: Variables, len: uint64)
  requires getFreeLoc.requires(s, len);
  ensures var (s', loc) := getFreeLoc(s, len);
    && (loc.Some? ==> LocAvailable(s, loc.value, len))
  {
    reveal_getFreeLoc();
    reveal_ConsistentBitmap();
    LBAType.reveal_ValidAddr();

    var (s', loc) := getFreeLoc(s, len);
    if loc.Some? {
      var i := BlockAllocator.Alloc(s.blockAllocator);

      BlockAllocator.LemmaAllocResult(s.blockAllocator);
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

  function InitLocBitmapIterate(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<(Option<BC.Location>, seq<BT.G.Reference>)>,
      bm: Bitmap.BitmapModel)
  : (res : (bool, Bitmap.BitmapModel))
  requires MutableMapModel.Inv(indirectionTable)
  requires MutableMapModel.WFIter(indirectionTable, it)
  requires BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
  requires Bitmap.Len(bm) == NumBlocks()
  ensures Bitmap.Len(res.1) == NumBlocks()
  decreases it.decreaser
  {
    if it.next.None? then (
      (true, bm)
    ) else (
      var kv := it.next.value;
      assert kv.0 in IIndirectionTable(indirectionTable).locs;

      var loc: uint64 := kv.1.0.value.addr;
      var locIndex: uint64 := loc / BlockSize() as uint64;
      if locIndex < NumBlocks() as uint64 && !Bitmap.IsSet(bm, locIndex as int) then (
        InitLocBitmapIterate(indirectionTable,
            MutableMapModel.IterInc(indirectionTable, it),
            Bitmap.BitSet(bm, locIndex as int))
      ) else (
        (false, bm)
      )
    )
  }

  function {:opaque} InitLocBitmap(indirectionTable: IndirectionTable) : (res : (bool, Bitmap.BitmapModel))
  requires MutableMapModel.Inv(indirectionTable)
  requires BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
  ensures Bitmap.Len(res.1) == NumBlocks()
  {
    var bm := Bitmap.EmptyBitmap(NumBlocks());
    var bm' := Bitmap.BitSet(bm, 0);
    InitLocBitmapIterate(indirectionTable,
        MutableMapModel.IterStart(indirectionTable),
        bm')
  }

  predicate IsLocAllocIndirectionTablePartial(indirectionTable: IndirectionTable, i: int, s: set<uint64>)
  {
    || i == 0 // block 0 is always implicitly allocated
    || !(
      forall ref | ref in indirectionTable.contents && indirectionTable.contents[ref].0.Some? && ref in s ::
        indirectionTable.contents[ref].0.value.addr as int != i * BlockSize() as int
    )
  }

  lemma InitLocBitmapIterateCorrect(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<(Option<BC.Location>, seq<BT.G.Reference>)>,
      bm: Bitmap.BitmapModel)
  requires InitLocBitmapIterate.requires(indirectionTable, it, bm);
  requires (forall i: int ::
        (IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)) <==> IsLocAllocBitmap(bm, i)
      )
  requires 
    forall r1, r2 | r1 in IIndirectionTable(indirectionTable).locs && r2 in IIndirectionTable(indirectionTable).locs ::
        r1 in it.s && r2 in it.s ==>
        BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(indirectionTable), r1, r2)
  ensures var (succ, bm') := InitLocBitmapIterate(indirectionTable, it, bm);
    (succ ==>
      && (forall i: int ::
        (IsLocAllocIndirectionTable(indirectionTable, i)
        <==> IsLocAllocBitmap(bm', i)
      ))
      && BC.AllLocationsForDifferentRefsDontOverlap(IIndirectionTable(indirectionTable))
    )
  decreases it.decreaser
  {
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var (succ, bm') := InitLocBitmapIterate(indirectionTable, it, bm);
    if it.next.None? {
      forall i: int | IsLocAllocIndirectionTable(indirectionTable, i)
      ensures IsLocAllocBitmap(bm', i)
      {
      }

      forall i: int
      | IsLocAllocBitmap(bm', i)
      ensures IsLocAllocIndirectionTable(indirectionTable, i)
      {
      }
    } else {
      if (succ) {
        var kv := it.next.value;
        assert kv.0 in IIndirectionTable(indirectionTable).locs;
        var loc: uint64 := kv.1.0.value.addr;
        var locIndex: uint64 := loc / BlockSize() as uint64;

        //assert IIndirectionTable(indirectionTable).locs[kv.0] == kv.1.0.value;
        LBAType.reveal_ValidAddr();
        assert BC.ValidLocationForNode(kv.1.0.value);
        assert locIndex as int * BlockSize() == loc as int;

        //assert locIndex < NumBlocks() as uint64;
        //assert !Bitmap.IsSet(bm, locIndex as int);

        var bm0 := Bitmap.BitSet(bm, locIndex as int);
        var it0 := MutableMapModel.IterInc(indirectionTable, it);

        forall i: int
        | IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s)
        ensures IsLocAllocBitmap(bm0, i)
        {
          // This triggers all the right stuff:
          if IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s) { }
          /*
          if i != 0 {
            var ref :| ref in indirectionTable.contents && indirectionTable.contents[ref].0.Some? && ref in it0.s && indirectionTable.contents[ref].0.value.addr as int == i * BlockSize() as int;
            if (ref == kv.0) {
              assert IsLocAllocBitmap(bm0, i);
            } else {
              assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s);
              assert IsLocAllocBitmap(bm0, i);
            }
          } else {
            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s);
          }
          */
        }

        forall i: int
        | IsLocAllocBitmap(bm0, i)
        ensures IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s)
        {
          if IsLocAllocBitmap(bm, i) { }
          if IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s) { }

          if i == locIndex as int {
            var ref := kv.0;
            assert ref in indirectionTable.contents;
            assert indirectionTable.contents[ref].0.Some?;
            assert ref in it0.s;
            assert indirectionTable.contents[ref] == kv.1;
            assert indirectionTable.contents[ref].0.value.addr as int == i * BlockSize() as int;

            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s);
          } else {
            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s);
          }
        }

        forall r1, r2 | r1 in IIndirectionTable(indirectionTable).locs && r2 in IIndirectionTable(indirectionTable).locs && r1 in it0.s && r2 in it0.s
        ensures BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(indirectionTable), r1, r2)
        {
          if r1 in it.s && r2 in it.s {
            assert BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(indirectionTable), r1, r2);
          } else {
            if r1 != r2 && IIndirectionTable(indirectionTable).locs[r1] == IIndirectionTable(indirectionTable).locs[r2] {
              var j1 := LBAType.ValidAddrDivisor(IIndirectionTable(indirectionTable).locs[r1].addr);
              var j2 := LBAType.ValidAddrDivisor(IIndirectionTable(indirectionTable).locs[r2].addr);
              if r1 !in it.s {
                assert r2 in it.s;
                assert !Bitmap.IsSet(bm, j1);
                assert IsLocAllocBitmap(bm, j2);
                assert Bitmap.IsSet(bm, j2);
                assert false;
              } else {
                assert r1 in it.s;
                assert !Bitmap.IsSet(bm, j2);
                assert IsLocAllocBitmap(bm, j1);
                assert Bitmap.IsSet(bm, j1);
                assert false;
              }
            }
          }
        }

        InitLocBitmapIterateCorrect(indirectionTable, it0, bm0);
        assert (succ, bm') == InitLocBitmapIterate(indirectionTable, it0, bm0);
      }
    }
  }

  lemma InitLocBitmapCorrect(indirectionTable: IndirectionTable)
  requires MutableMapModel.Inv(indirectionTable)
  requires BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
  ensures var (succ, bm) := InitLocBitmap(indirectionTable);
    (succ ==>
      && (forall i: int :: IsLocAllocIndirectionTable(indirectionTable, i)
        <==> IsLocAllocBitmap(bm, i)
      )
      && BC.AllLocationsForDifferentRefsDontOverlap(IIndirectionTable(indirectionTable))
    )
  {
    reveal_InitLocBitmap();
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var it := MutableMapModel.IterStart(indirectionTable);

    var bm := Bitmap.EmptyBitmap(NumBlocks());
    var bm' := Bitmap.BitSet(bm, 0);

    /*forall i: int | IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    ensures IsLocAllocBitmap(bm', i)
    {
      assert i == 0;
    }*/

    forall i: int | IsLocAllocBitmap(bm', i)
    ensures IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    {
      if i != 0 {
        assert Bitmap.IsSet(bm', i)
            == Bitmap.IsSet(bm, i)
            == false;
      }
      assert i == 0;
    }

    InitLocBitmapIterateCorrect(indirectionTable, it, bm');
  }

  function PageInIndirectionTableResp(k: Constants, s: Variables, io: IO)
  : (s' : Variables)
  requires diskOp(io).RespReadOp?
  requires s.Unready?
  {
    var (id, sector) := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) then (
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      var (succ, bm) := InitLocBitmap(ephemeralIndirectionTable);
      if succ then (
        var blockAllocator := BlockAllocator.InitBlockAllocator(bm);
        var persistentIndirectionTable := sector.value.indirectionTable;
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
    var (id, sector) := ReadSector(io);
    ReadSectorCorrect(io);

    Marshalling.reveal_parseSector();
    M.reveal_IBytes();
    M.reveal_Parse();

    var s' := PageInIndirectionTableResp(k, s, io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      var ephemeralIndirectionTable := sector.value.indirectionTable;
      var (succ, bm) := InitLocBitmap(ephemeralIndirectionTable);
      if succ {
        WeightBucketEmpty();

        reveal_ConsistentBitmap();
        InitLocBitmapCorrect(ephemeralIndirectionTable);
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

  function writeResponse(k: Constants, s: Variables, io: IO)
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
             .(syncReqs := BC.syncReqs2to1(s.syncReqs))
             .(blockAllocator := BlockAllocator.MoveFrozenToPersistent(s.blockAllocator))
    ) else if (s.Ready? && id in s.outstandingBlockWrites) then (
      lemmaOutstandingLocIndexValid(k, s, id);
      s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id))
       .(blockAllocator := BlockAllocator.MarkFreeOutstanding(s.blockAllocator, s.outstandingBlockWrites[id].loc.addr as int / BlockSize()))
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
    reveal_ConsistentBitmap();
    var id := io.id;
    var s' := writeResponse(k, s, io);
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      lemmaBlockAllocatorFrozenSome(k, s);
      assert WFVars(s');
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      var locIdx := s.outstandingBlockWrites[id].loc.addr as int / BlockSize();
      lemmaOutstandingLocIndexValid(k, s, id);

      LBAType.reveal_ValidAddr();
      assert locIdx * BlockSize() == s.outstandingBlockWrites[id].loc.addr as int;

      Bitmap.reveal_BitUnset();
      Bitmap.reveal_IsSet();

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
