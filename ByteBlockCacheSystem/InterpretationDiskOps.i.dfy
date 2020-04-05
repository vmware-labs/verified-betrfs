include "AsyncDiskModel.s.dfy"
include "../BlockCacheSystem/BlockJournalDisk.i.dfy"
include "Marshalling.i.dfy"
include "JournalBytes.i.dfy"

module InterpretationDiskOps {
  import opened NativeTypes
  import opened Options

  import BJD = BlockJournalDisk
  import BlockDisk
  import JournalDisk
  import BC = BlockCache
  import Marshalling
  import D = AsyncDisk

  import opened DiskLayout
  import opened JournalRanges
  import opened SectorType
  import opened JournalIntervals
  import JournalBytes

  function {:opaque} Parse(bytes: seq<byte>) : Option<Sector>
  {
    Marshalling.parseSector(bytes)
  }

  predicate {:opaque} ValidCheckedBytes(bytes: seq<byte>)
  requires 32 <= |bytes| < 0xffff_ffff_ffff_ffff
  {
    && D.ChecksumChecksOut(bytes)
    && Parse(bytes[32..]).Some?
  }

  predicate ValidBytes(bytes: seq<byte>)
  {
    && 32 <= |bytes| < 0xffff_ffff_ffff_ffff
    && ValidCheckedBytes(bytes)
  }

  function {:opaque} SectorOfBytes(bytes: seq<byte>) : Sector
  requires ValidBytes(bytes)
  {
    reveal_ValidCheckedBytes();
    Parse(bytes[32..]).value
  }

  predicate ValidSuperblockBytes(bytes: seq<byte>)
  {
    && ValidBytes(bytes)
    && SectorOfBytes(bytes).SectorSuperblock?
  }

  predicate ValidJournalBytes(bytes: seq<byte>)
  {
    JournalBytes.JournalRangeOfByteSeq(bytes).Some?
  }

  predicate ValidIndirectionTableBytes(bytes: seq<byte>)
  {
    && ValidBytes(bytes)
    && SectorOfBytes(bytes).SectorIndirectionTable?
  }

  predicate ValidNodeBytes(bytes: seq<byte>)
  {
    && ValidBytes(bytes)
    && SectorOfBytes(bytes).SectorNode?
  }

  function SuperblockOfBytes(bytes: seq<byte>) : Superblock
  requires ValidSuperblockBytes(bytes)
  {
    SectorOfBytes(bytes).superblock
  }

  function IndirectionTableOfBytes(bytes: seq<byte>) : IndirectionTable
  requires ValidIndirectionTableBytes(bytes)
  {
    SectorOfBytes(bytes).indirectionTable
  }

  function NodeOfBytes(bytes: seq<byte>) : BC.Node
  requires ValidNodeBytes(bytes)
  {
    SectorOfBytes(bytes).node
  }

  function SuperblockOptOfBytes(bytes: seq<byte>) : Option<Superblock>
  {
    if ValidSuperblockBytes(bytes) then
      Some(SuperblockOfBytes(bytes))
    else
      None
  }

  function IndirectionTableOptOfBytes(bytes: seq<byte>) : Option<IndirectionTable>
  {
    if ValidIndirectionTableBytes(bytes) then
      Some(IndirectionTableOfBytes(bytes))
    else
      None
  }

  function NodeOptOfBytes(bytes: seq<byte>) : Option<BC.Node>
  {
    if ValidNodeBytes(bytes) then
      Some(NodeOfBytes(bytes))
    else
      None
  }

  // Loc reqs / resps

  function LocOfReqRead(reqRead: D.ReqRead) : Location
  {
    Location(reqRead.addr, reqRead.len)
  }

  function LocOfReqWrite(reqWrite: D.ReqWrite) : Location
  requires |reqWrite.bytes| < 0x1_0000_0000_0000_0000
  {
    Location(reqWrite.addr, |reqWrite.bytes| as uint64)
  }

  function LocOfRespRead(respRead: D.RespRead) : Location
  requires |respRead.bytes| < 0x1_0000_0000_0000_0000
  {
    Location(respRead.addr, |respRead.bytes| as uint64)
  }

  function LocOfRespWrite(respWrite: D.RespWrite) : Location
  {
    Location(respWrite.addr, respWrite.len)
  }

  // Validity of Reqs / Resps

  predicate ValidReqRead(reqRead: D.ReqRead)
  {
    && ValidLocation(LocOfReqRead(reqRead))
  }

  predicate ValidReqWrite(reqWrite: D.ReqWrite)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && var loc := LocOfReqWrite(reqWrite);
    && ValidLocation(loc)
    && (ValidSuperblockLocation(loc) ==> ValidSuperblockBytes(reqWrite.bytes))
    && (ValidJournalLocation(loc) ==> ValidJournalBytes(reqWrite.bytes))
    && (ValidIndirectionTableLocation(loc) ==> ValidIndirectionTableBytes(reqWrite.bytes))
    && (ValidNodeLocation(loc) ==> ValidNodeBytes(reqWrite.bytes))
  }

  // There's only one case where we ever use this.
  // It's for journals.
  predicate ValidReqWrite2(reqWrite1: D.ReqWrite, reqWrite2: D.ReqWrite)
  {
    && ValidReqWrite(reqWrite1)
    && ValidReqWrite(reqWrite2)
    && ValidJournalLocation(LocOfReqWrite(reqWrite1))
    && ValidJournalLocation(LocOfReqWrite(reqWrite2))
    && var int1 := JournalIntervalOfLocation(LocOfReqWrite(reqWrite1));
    && var int2 := JournalIntervalOfLocation(LocOfReqWrite(reqWrite2));
    && int1.start + int1.len == NumJournalBlocks() as int
    && int2.start == 0
    && int2.len > 0
    && int1.len + int2.len <= NumJournalBlocks() as int
  }

  predicate ValidRespRead(respRead: D.RespRead)
  {
    && |respRead.bytes| < 0x1_0000_0000_0000_0000
    && var loc := LocOfRespRead(respRead);
    //&& |respRead.bytes| == loc.len as int
    && ValidLocation(loc)
  }

  predicate ValidRespWrite(respWrite: D.RespWrite)
  {
    && ValidLocation(LocOfRespWrite(respWrite))
  }

  predicate ValidDiskOp(dop: D.DiskOp)
  {
    && (dop.ReqReadOp? ==> ValidReqRead(dop.reqRead))
    && (dop.ReqWriteOp? ==> ValidReqWrite(dop.reqWrite))
    && (dop.ReqWrite2Op? ==> ValidReqWrite2(dop.reqWrite1, dop.reqWrite2))
    && (dop.RespReadOp? ==> ValidRespRead(dop.respRead))
    && (dop.RespWriteOp? ==> ValidRespWrite(dop.respWrite))
  }

  //
  // Interpretation of ReqRead

  function BlockDiskOp_of_ReqRead(id: D.ReqId, reqRead: D.ReqRead) : BlockDisk.DiskOp
  requires ValidReqRead(reqRead)
  {
    if ValidNodeLocation(LocOfReqRead(reqRead)) then
      BlockDisk.ReqReadNodeOp(id, LocOfReqRead(reqRead))
    else if ValidIndirectionTableLocation(LocOfReqRead(reqRead)) then
      BlockDisk.ReqReadIndirectionTableOp(id, LocOfReqRead(reqRead))
    else
      BlockDisk.NoDiskOp
  }

  function JournalDiskOp_of_ReqRead(id: D.ReqId, reqRead: D.ReqRead) : JournalDisk.DiskOp
  requires ValidReqRead(reqRead)
  {
    if ValidSuperblock1Location(LocOfReqRead(reqRead)) then
      JournalDisk.ReqReadSuperblockOp(id, 0)
    else if ValidSuperblock2Location(LocOfReqRead(reqRead)) then
      JournalDisk.ReqReadSuperblockOp(id, 1)
    else if ValidJournalLocation(LocOfReqRead(reqRead)) then
      JournalDisk.ReqReadJournalOp(id, JournalIntervalOfLocation(LocOfReqRead(reqRead)))
    else
      JournalDisk.NoDiskOp
  }

  function DiskOp_of_ReqRead(id: D.ReqId, reqRead: D.ReqRead) : BJD.DiskOp
  requires ValidReqRead(reqRead)
  {
    BJD.DiskOp(
      BlockDiskOp_of_ReqRead(id, reqRead),
      JournalDiskOp_of_ReqRead(id, reqRead)
    )
  }

  //
  // Interpretation of ReqWrite

  function BlockDiskOp_of_ReqWrite(id: D.ReqId, reqWrite: D.ReqWrite) : BlockDisk.DiskOp
  requires ValidReqWrite(reqWrite)
  {
    if ValidNodeLocation(LocOfReqWrite(reqWrite)) then
      BlockDisk.ReqWriteNodeOp(id,
        BlockDisk.ReqWriteNode(LocOfReqWrite(reqWrite),
        NodeOfBytes(reqWrite.bytes)))
    else if ValidIndirectionTableLocation(LocOfReqWrite(reqWrite)) then
      BlockDisk.ReqWriteIndirectionTableOp(id,
        BlockDisk.ReqWriteIndirectionTable(LocOfReqWrite(reqWrite),
        IndirectionTableOfBytes(reqWrite.bytes)))
    else
      BlockDisk.NoDiskOp
  }

  function JournalDiskOp_of_ReqWrite(id: D.ReqId, reqWrite: D.ReqWrite) : JournalDisk.DiskOp
  requires ValidReqWrite(reqWrite)
  {
    if ValidSuperblock1Location(LocOfReqWrite(reqWrite)) then
      JournalDisk.ReqWriteSuperblockOp(id, 0,
        JournalDisk.ReqWriteSuperblock(SuperblockOfBytes(reqWrite.bytes)))
    else if ValidSuperblock2Location(LocOfReqWrite(reqWrite)) then
      JournalDisk.ReqWriteSuperblockOp(id, 1,
        JournalDisk.ReqWriteSuperblock(SuperblockOfBytes(reqWrite.bytes)))
    else if ValidJournalLocation(LocOfReqWrite(reqWrite)) then
      JournalDisk.ReqWriteJournalOp(id, None,
        JournalDisk.ReqWriteJournal(
          JournalIntervalOfLocation(LocOfReqWrite(reqWrite)).start,
          JournalBytes.JournalRangeOfByteSeq(reqWrite.bytes).value
        )
      )
    else
      JournalDisk.NoDiskOp
  }

  function DiskOp_of_ReqWrite(id: D.ReqId, reqWrite: D.ReqWrite) : BJD.DiskOp
  requires ValidReqWrite(reqWrite)
  {
    BJD.DiskOp(
      BlockDiskOp_of_ReqWrite(id, reqWrite),
      JournalDiskOp_of_ReqWrite(id, reqWrite)
    )
  }

  //
  // Interpretation of ReqWrite2

  function JournalDiskOp_of_ReqWrite2(id1: D.ReqId, id2: D.ReqId, reqWrite1: D.ReqWrite, reqWrite2: D.ReqWrite) : JournalDisk.DiskOp
  requires ValidReqWrite2(reqWrite1, reqWrite2)
  {
    var int1 := JournalIntervalOfLocation(LocOfReqWrite(reqWrite1));
    var int2 := JournalIntervalOfLocation(LocOfReqWrite(reqWrite2));
    JournalDisk.ReqWriteJournalOp(id1, Some(id2),
        JournalDisk.ReqWriteJournal(
          int1.start,
          JournalBytes.JournalRangeOfByteSeq(reqWrite1.bytes).value
            + JournalBytes.JournalRangeOfByteSeq(reqWrite2.bytes).value
        )
      )
  }

  function DiskOp_of_ReqWrite2(id1: D.ReqId, id2: D.ReqId, reqWrite1: D.ReqWrite, reqWrite2: D.ReqWrite) : BJD.DiskOp
  requires ValidReqWrite2(reqWrite1, reqWrite2)
  {
    BJD.DiskOp(
      BlockDisk.NoDiskOp,
      JournalDiskOp_of_ReqWrite2(id1, id2, reqWrite1, reqWrite2)
    )
  }


  //
  // Interpretation of RespRead

  function BlockDiskOp_of_RespRead(id: D.ReqId, respRead: D.RespRead) : BlockDisk.DiskOp
  requires ValidRespRead(respRead)
  {
    if ValidNodeLocation(LocOfRespRead(respRead)) then
      BlockDisk.RespReadNodeOp(id,
        NodeOptOfBytes(respRead.bytes))
    else if ValidIndirectionTableLocation(LocOfRespRead(respRead)) then
      BlockDisk.RespReadIndirectionTableOp(id,
        IndirectionTableOptOfBytes(respRead.bytes))
    else
      BlockDisk.NoDiskOp
  }

  function JournalDiskOp_of_RespRead(id: D.ReqId, respRead: D.RespRead) : JournalDisk.DiskOp
  requires ValidRespRead(respRead)
  {
    if ValidSuperblock1Location(LocOfRespRead(respRead)) then
      JournalDisk.RespReadSuperblockOp(id, 0,
        SuperblockOptOfBytes(respRead.bytes))
    else if ValidSuperblock2Location(LocOfRespRead(respRead)) then
      JournalDisk.RespReadSuperblockOp(id, 1,
        SuperblockOptOfBytes(respRead.bytes))
    else if ValidJournalLocation(LocOfRespRead(respRead)) then
      JournalDisk.RespReadJournalOp(id,
        JournalBytes.JournalRangeOfByteSeq(respRead.bytes)
      )
    else
      JournalDisk.NoDiskOp
  }

  function DiskOp_of_RespRead(id: D.ReqId, respRead: D.RespRead) : BJD.DiskOp
  requires ValidRespRead(respRead)
  {
    BJD.DiskOp(
      BlockDiskOp_of_RespRead(id, respRead),
      JournalDiskOp_of_RespRead(id, respRead)
    )
  }

  //
  // Interpretation of RespWrite

  function BlockDiskOp_of_RespWrite(id: D.ReqId, respWrite: D.RespWrite) : BlockDisk.DiskOp
  requires ValidRespWrite(respWrite)
  {
    if ValidNodeLocation(LocOfRespWrite(respWrite)) then
      BlockDisk.RespWriteNodeOp(id)
    else if ValidIndirectionTableLocation(LocOfRespWrite(respWrite)) then
      BlockDisk.RespWriteIndirectionTableOp(id)
    else
      BlockDisk.NoDiskOp
  }

  function JournalDiskOp_of_RespWrite(id: D.ReqId, respWrite: D.RespWrite) : JournalDisk.DiskOp
  requires ValidRespWrite(respWrite)
  {
    if ValidSuperblock1Location(LocOfRespWrite(respWrite)) then
      JournalDisk.RespWriteSuperblockOp(id, 0)
    else if ValidSuperblock2Location(LocOfRespWrite(respWrite)) then
      JournalDisk.RespWriteSuperblockOp(id, 1)
    else if ValidJournalLocation(LocOfRespWrite(respWrite)) then
      JournalDisk.RespWriteJournalOp(id)
    else
      JournalDisk.NoDiskOp
  }

  function DiskOp_of_RespWrite(id: D.ReqId, respWrite: D.RespWrite) : BJD.DiskOp
  requires ValidRespWrite(respWrite)
  {
    BJD.DiskOp(
      BlockDiskOp_of_RespWrite(id, respWrite),
      JournalDiskOp_of_RespWrite(id, respWrite)
    )
  }

  function IDiskOp(diskOp: D.DiskOp) : BJD.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case ReqReadOp(id, reqRead) => DiskOp_of_ReqRead(id, reqRead)
      case ReqWriteOp(id, reqWrite) => DiskOp_of_ReqWrite(id, reqWrite)
      case ReqWrite2Op(id1, id2, reqWrite1, reqWrite2) => DiskOp_of_ReqWrite2(id1, id2, reqWrite1, reqWrite2)
      case RespReadOp(id, respRead) => DiskOp_of_RespRead(id, respRead)
      case RespWriteOp(id, respWrite) => DiskOp_of_RespWrite(id, respWrite)
      case NoDiskOp => BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp)
    }
  }
}
