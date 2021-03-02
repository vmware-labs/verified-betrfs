include "../ByteBlockCacheSystem/ByteCache.i.dfy"
include "MarshallingModel.i.dfy"
include "DiskOpModel.i.dfy"
include "StateBCImpl.i.dfy"

//
// IO functions used by various StateModel verbs.
// Updates data structures as defined in StateModel.
// Interacts with the disk via StateModel.IO, which abstracts
// MainDiskIOHandlers.s.dfy.
//
// Also, the code that reads in indirection tables and nodes.
//

module IOModel {
  // import opened StateModel
  import opened DiskOpModel
  import opened NativeTypes
  import opened Options
  import opened LinearOption
  import opened Maps
  import opened Bounds
  import opened BucketWeights
  import opened ViewOp
  import IMM = MarshallingModel
  import Marshalling = Marshalling
  import opened DiskLayout
  import opened InterpretationDiskOps
  import BucketsLib
  import LruModel
  import M = ByteCache
  import BlockDisk
  import JournalDisk
  import BlockJournalDisk
  import UI
  // Misc utilities
  import BBC = BetreeCache
  import SSM = StateSectorModel
  import IndirectionTable

  import opened StateBCImpl

  type Sector = SSM.Sector
  
  predicate stepsBetree(s: BBC.Variables, s': BBC.Variables, vop: VOp, step: BT.BetreeStep)
  {
    BBC.NextStep(s, s', BlockDisk.NoDiskOp, vop, BBC.BetreeMoveStep(step))
  }

  predicate stepsBC(s: BBC.Variables, s': BBC.Variables, vop: VOp, io: IO, step: BC.Step)
  {
    && ValidDiskOp(diskOp(io))
    && BBC.NextStep(s, s', IDiskOp(diskOp(io)).bdop, vop, BBC.BlockCacheMoveStep(step))
  }

  predicate noop(s: BBC.Variables, s': BBC.Variables)
  {
    BBC.NextStep(s, s', BlockDisk.NoDiskOp, StatesInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep))
  }

  // TODO(jonh): rename to indicate this is only nops.
  predicate betree_next(s: BBC.Variables, s': BBC.Variables)
  {
    || BBC.Next(s, s', BlockDisk.NoDiskOp, StatesInternalOp)
    || BBC.Next(s, s', BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true))
  }

  predicate betree_next_dop(s: BBC.Variables, s': BBC.Variables, dop: BlockDisk.DiskOp)
  {
    || BBC.Next(s, s', dop, StatesInternalOp)
    || BBC.Next(s, s', dop, AdvanceOp(UI.NoOp, true))
  }

  // models of IO-related methods
  predicate LocAvailable(s: ImplVariables, loc: Location, len: uint64)
  requires s.WFBCVars()
  {
    && s.Ready?
    && ValidNodeLocation(loc)
    && BC.ValidAllocation(s.I(), loc)
    && loc.len == len
  }

  function {:opaque} getFreeLoc(s: ImplVariables, len: uint64)
  : (res : Option<Location>)
  requires s.Ready?
  requires s.WFBCVars()
  requires len <= NodeBlockSizeUint64()
  ensures res.Some? ==> 0 <= res.value.addr as int / NodeBlockSize() < NumBlocks()
  {
    var i := BlockAllocatorModel.Alloc(s.blockAllocator.I());
    if i.Some? then
      Some(DiskLayout.Location((i.value * NodeBlockSize()) as uint64, len))
    else
      None
  }

  predicate {:opaque} FindLocationAndRequestWrite(io: IO, s: ImplVariables, sector: Sector,
      id: Option<D.ReqId>, loc: Option<DiskLayout.Location>, io': IO)
  requires s.Ready?
  requires s.WFBCVars()
  ensures FindLocationAndRequestWrite(io, s, sector, id, loc, io') ==>
      loc.Some? ==> 0 <= loc.value.addr as int / NodeBlockSize() < NumBlocks()
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
      && |bytes| <= NodeBlockSize() as int
      && 32 <= |bytes|
      && IMM.parseCheckedSector(bytes).Some?
      && SSM.WFSector(sector)
      && SSM.ISector(IMM.parseCheckedSector(bytes).value) == SSM.ISector(sector)

      && var len := |bytes| as uint64;
      && loc == getFreeLoc(s, len)
      && loc.Some?

      && id == Some(dop.id)
      && dop == D.ReqWriteOp(id.value, D.ReqWrite(loc.value.addr, bytes))
      && io' == IOReqWrite(id.value, dop.reqWrite)
    ))
  }

  function RequestRead(io: IO, loc: DiskLayout.Location)
  : (res : (D.ReqId, IO))
  requires io.IOInit?
  {
    (io.id, IOReqRead(io.id, D.ReqRead(loc.addr, loc.len)))
  }

  lemma RequestReadCorrect(io: IO, loc: DiskLayout.Location)
  requires io.IOInit?
  requires DiskLayout.ValidLocation(loc)
  ensures var (id, io') := RequestRead(io, loc);
    && ValidDiskOp(diskOp(io'))
    && (ValidNodeLocation(loc) ==> IDiskOp(diskOp(io')) == BlockJournalDisk.DiskOp(BlockDisk.ReqReadNodeOp(id, loc), JournalDisk.NoDiskOp))
    && (ValidIndirectionTableLocation(loc) ==> IDiskOp(diskOp(io')) == BlockJournalDisk.DiskOp(BlockDisk.ReqReadIndirectionTableOp(id, loc), JournalDisk.NoDiskOp))
    && (ValidSuperblock1Location(loc) ==> IDiskOp(diskOp(io')) == BlockJournalDisk.DiskOp(BlockDisk.NoDiskOp, JournalDisk.ReqReadSuperblockOp(id, 0)))
    && (ValidSuperblock2Location(loc) ==> IDiskOp(diskOp(io')) == BlockJournalDisk.DiskOp(BlockDisk.NoDiskOp, JournalDisk.ReqReadSuperblockOp(id, 1)))
  {
  }

  function PageInNodeReq(s: BBC.Variables, io: IO, ref: BC.Reference)
  : (res : (BBC.Variables, IO))
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

  lemma PageInNodeReqCorrect(s: BBC.Variables, io: IO, ref: BC.Reference)
  requires io.IOInit?
  requires s.Ready?
  requires BBC.Inv(s)
  requires ref in s.ephemeralIndirectionTable.locs;
  requires ref !in s.cache
  ensures var (s', io') := PageInNodeReq(s, io, ref);
    && ValidDiskOp(diskOp(io'))
    && BBC.Next(s, s', IDiskOp(diskOp(io')).bdop, StatesInternalOp)
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      assert noop(s, s);
    } else {
      // assert ref in s.ephemeralIndirectionTable.locs;
      var loc := s.ephemeralIndirectionTable.locs[ref];
      assert ValidNodeLocation(loc);
      var (id, io') := RequestRead(io, loc);
      var s' := s.(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);

      assert BC.PageInNodeReq(s, s', IDiskOp(diskOp(io')).bdop, StatesInternalOp, ref);
      assert stepsBC(s, s', StatesInternalOp, io', BC.PageInNodeReqStep(ref));
    }
  }

  // == readResponse ==

  function ISectorOpt(sector: Option<Sector>) : Option<SectorType.Sector>
  requires sector.Some? ==> SSM.WFSector(sector.value)
  {
    match sector {
      case None => None
      case Some(sector) => Some(SSM.ISector(sector))
    }
  }

  function ReadSector(io: IO)
  : (res : (D.ReqId, Option<Sector>))
  requires diskOp(io).RespReadOp?
  {
    var id := io.id;
    var bytes := io.respRead.bytes;
    if |bytes| <= IndirectionTableBlockSize() then (
      var loc := DiskLayout.Location(io.respRead.addr, |io.respRead.bytes| as uint64);
      var sector := IMM.parseCheckedSector(bytes);
      if sector.Some? && (
        || (ValidNodeLocation(loc) && sector.value.SectorNode?)
        || (ValidSuperblockLocation(loc) && sector.value.SectorSuperblock?)
        || (ValidIndirectionTableLocation(loc) && sector.value.SectorIndirectionTable?)
      )
      then
        (id, sector)
      else
        (id, None)
    ) else (
      (id, None)
    )
  }

  lemma ReadSectorCorrect(io: IO)
  requires diskOp(io).RespReadOp?
  requires ValidDiskOp(diskOp(io))
  ensures var (id, sector) := ReadSector(io);
    && (sector.Some? ==> (
      && SSM.WFSector(sector.value)
      && ValidDiskOp(diskOp(io))
      && (sector.value.SectorNode? ==> IDiskOp(diskOp(io)) == BlockJournalDisk.DiskOp(BlockDisk.RespReadNodeOp(id, Some(sector.value.node )), JournalDisk.NoDiskOp))
      && (sector.value.SectorIndirectionTable? ==> IDiskOp(diskOp(io)) == BlockJournalDisk.DiskOp(BlockDisk.RespReadIndirectionTableOp(id, Some(sector.value.indirectionTable.I())), JournalDisk.NoDiskOp))
      && (sector.value.SectorSuperblock? ==>
        && IDiskOp(diskOp(io)).bdop == BlockDisk.NoDiskOp
        && IDiskOp(diskOp(io)).jdop.RespReadSuperblockOp?
        && IDiskOp(diskOp(io)).jdop.id == id
        && IDiskOp(diskOp(io)).jdop.superblock == Some(sector.value.superblock)
      )
    ))
    && ((IDiskOp(diskOp(io)).jdop.RespReadSuperblockOp? && IDiskOp(diskOp(io)).jdop.superblock.Some?) ==> (
      && sector.Some?
      && sector.value.SectorSuperblock?
    ))
  {
    IMM.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    IMM.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();
    D.reveal_ChecksumChecksOut();
  }

  // == writeResponse ==

  lemma lemmaOutstandingLocIndexValid(s: ImplVariables, id: uint64)
  requires s.Inv()
  requires s.Ready?
  requires id in s.outstandingBlockWrites
  ensures 0 <= s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize() < NumBlocks()
  {
    reveal_ConsistentBitmapInteral();
    var i := s.outstandingBlockWrites[id].loc.addr as int / NodeBlockSize();
    DiskLayout.reveal_ValidNodeAddr();
    assert i * NodeBlockSize() == s.outstandingBlockWrites[id].loc.addr as int;
    assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().outstanding, i);
  }

  lemma lemmaBlockAllocatorFrozenSome(s: ImplVariables)
  requires s.Inv()
  requires s.Ready?
  ensures s.frozenIndirectionTable.lSome?
      ==> s.blockAllocator.frozen.lSome?
  {
    reveal_ConsistentBitmapInteral();
    reveal s.blockAllocator.Inv();
    reveal s.blockAllocator.I();
  }
}
