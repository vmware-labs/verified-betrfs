include "InterpretationDiskOps.i.dfy"
include "InterpretationDiskContents.i.dfy"
include "AsyncDiskModel.s.dfy"

module InterpretationDisk {
  import BlockDisk
  import JournalDisk
  import D = AsyncDisk
  import opened Options
  import opened DiskLayout
  import opened NativeTypes
  import opened Maps
  import G = PivotBetreeGraph
  import opened SectorType
  import opened JournalIntervals
  import opened JournalRanges
  import opened InterpretationDiskOps
  import opened InterpretationDiskContents
  import JournalBytes

  ///// reqWrites are correct

  predicate ReqWriteNodeLocation(reqWrite: D.ReqWrite)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && ValidNodeLocation(LocOfReqWrite(reqWrite))
  }

  predicate ReqWriteIndirectionTableLocation(reqWrite: D.ReqWrite)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && ValidIndirectionTableLocation(LocOfReqWrite(reqWrite))
  }

  predicate ReqWriteJournalLocation(reqWrite: D.ReqWrite)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && ValidJournalLocation(LocOfReqWrite(reqWrite))
  }

  predicate ReqWriteSuperblockLocation(reqWrite: D.ReqWrite)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && ValidSuperblockLocation(LocOfReqWrite(reqWrite))
  }

  predicate reqWritesHaveValidNodes(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites ::
        ReqWriteNodeLocation(reqWrites[id]) ==>
          ValidNodeBytes(reqWrites[id].bytes)
  }

  predicate reqWritesHaveValidIndirectionTables(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites ::
        ReqWriteIndirectionTableLocation(reqWrites[id]) ==>
          ValidIndirectionTableBytes(reqWrites[id].bytes)
  }

  predicate reqWritesHaveValidJournals(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites ::
        ReqWriteJournalLocation(reqWrites[id]) ==>
          ValidJournalBytes(reqWrites[id].bytes)
  }

  predicate reqWritesHaveValidSuperblocks(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites ::
        ReqWriteSuperblockLocation(reqWrites[id]) ==>
          ValidSuperblockBytes(reqWrites[id].bytes)
  }

  predicate reqWritesHaveValidData(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    && reqWritesHaveValidNodes(reqWrites)
    && reqWritesHaveValidIndirectionTables(reqWrites)
    && reqWritesHaveValidJournals(reqWrites)
    && reqWritesHaveValidSuperblocks(reqWrites)
  }


  ///// get operation from Loc

  function ReqReadWithLoc(reqReads: map<D.ReqId, D.ReqRead>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqReads && LocOfReqRead(reqReads[id]) == loc then
      Some(id)
    else
      None
  }

  function ReqWriteWithLoc(reqWrites: map<D.ReqId, D.ReqWrite>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqWrites
        && |reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
        && LocOfReqWrite(reqWrites[id]) == loc then
      Some(id)
    else
      None
  }

  function RespReadWithLoc(respReads: map<D.ReqId, D.RespRead>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in respReads
        && |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && LocOfRespRead(respReads[id]) == loc then
      Some(id)
    else
      None
  }

  function RespWriteWithLoc(respWrites: map<D.ReqId, D.RespWrite>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in respWrites && LocOfRespWrite(respWrites[id]) == loc then
      Some(id)
    else
      None
  }

  //// Superblocks

  predicate HasSuperblockAtLoc(disk: D.Variables, loc: Location)
  {
    && 0 <= loc.addr as int
      <= loc.addr as int + loc.len as int
      <= |disk.contents|
    && ValidSuperblockBytes(
        disk.contents[loc.addr .. loc.addr as int + loc.len as int])
  }

  function SuperblockAtLoc(disk: D.Variables, loc: Location) : Superblock
  requires HasSuperblockAtLoc(disk, loc)
  {
    SuperblockOfBytes(
        disk.contents[loc.addr .. loc.addr as int + loc.len as int])
  }

  function SuperblockAtLocOpt(disk: D.Variables, loc: Location) : Option<Superblock>
  {
    if HasSuperblockAtLoc(disk, loc) then
      Some(SuperblockAtLoc(disk,loc))
    else
      None
  }

  function ReqReadSuperblockAtLoc_of_reqs(disk: D.Variables, loc: Location) : set<D.ReqId>
  {
    set id | id in disk.reqReads &&
        LocOfReqRead(disk.reqReads[id]) == loc
  }

  function ReqReadSuperblockAtLoc_of_resps(disk: D.Variables, loc: Location) : set<D.ReqId>
  {
    set id | id in disk.respReads
        && |disk.respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && LocOfRespRead(disk.respReads[id]) == loc
  }

  function ReqReadSuperblockAtLoc(disk: D.Variables, loc: Location) : set<D.ReqId>
  {
      ReqReadSuperblockAtLoc_of_reqs(disk, loc)
    + ReqReadSuperblockAtLoc_of_resps(disk, loc)
  }

  function ReqWriteSuperblockAtLoc(disk: D.Variables, loc: Location) : Option<JournalDisk.ReqWriteSuperblockId>
  requires ValidSuperblockLocation(loc)
  requires reqWritesHaveValidSuperblocks(disk.reqWrites)
  {
    var id := ReqWriteWithLoc(disk.reqWrites, loc);
    if id.Some? then
      Some(JournalDisk.ReqWriteSuperblockId(
        id.value,
        JournalDisk.ReqWriteSuperblock(SuperblockOfBytes(disk.reqWrites[id.value].bytes))
      ))
    else (
      var id2 := RespWriteWithLoc(disk.respWrites, loc);
      if id2.Some? && HasSuperblockAtLoc(disk, loc) then
        Some(JournalDisk.ReqWriteSuperblockId(
          id2.value,
          JournalDisk.ReqWriteSuperblock(SuperblockAtLoc(disk, loc))
        ))
      else
        None
    )
  }

  function Superblock1(disk: D.Variables) : Option<Superblock>
  {
    SuperblockAtLocOpt(disk, Superblock1Location())
  }

  function Superblock2(disk: D.Variables) : Option<Superblock>
  {
    SuperblockAtLocOpt(disk, Superblock2Location())
  }

  function ReqReadSuperblock1(disk: D.Variables) : set<JournalDisk.ReqId>
  {
    ReqReadSuperblockAtLoc(disk, Superblock1Location())
  }

  function ReqReadSuperblock2(disk: D.Variables) : set<JournalDisk.ReqId>
  {
    ReqReadSuperblockAtLoc(disk, Superblock2Location())
  }

  function ReqWriteSuperblock1(disk: D.Variables) : Option<JournalDisk.ReqWriteSuperblockId>
  requires reqWritesHaveValidSuperblocks(disk.reqWrites)
  {
    ReqWriteSuperblockAtLoc(disk, Superblock1Location())
  }

  function ReqWriteSuperblock2(disk: D.Variables) : Option<JournalDisk.ReqWriteSuperblockId>
  requires reqWritesHaveValidSuperblocks(disk.reqWrites)
  {
    ReqWriteSuperblockAtLoc(disk, Superblock2Location())
  }

  //// Journals

  function ReqReadJournals_of_reqs(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    map id | id in disk.reqReads &&
        ValidJournalLocation(LocOfReqRead(disk.reqReads[id]))
      :: JournalIntervalOfLocation(LocOfReqRead(disk.reqReads[id]))
  }

  function ReqReadJournals_of_resps(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    map id | id in disk.respReads
      && |disk.respReads[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidJournalLocation(LocOfRespRead(disk.respReads[id]))
      :: JournalIntervalOfLocation(LocOfRespRead(disk.respReads[id]))
  }

  function ReqReadJournals(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    MapUnion(
        ReqReadJournals_of_reqs(disk), 
        ReqReadJournals_of_resps(disk))
  }

  function ReqWriteJournals_of_reqs(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    map id | id in disk.reqWrites
      && |disk.reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidJournalLocation(LocOfReqWrite(disk.reqWrites[id]))
      :: JournalIntervalOfLocation(LocOfReqWrite(disk.reqWrites[id]))
  }

  function ReqWriteJournals_of_resps(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    map id | id in disk.respWrites
      && ValidJournalLocation(LocOfRespWrite(disk.respWrites[id]))
      :: JournalIntervalOfLocation(LocOfRespWrite(disk.respWrites[id]))
  }

  function ReqWriteJournals(disk: D.Variables) : map<D.ReqId, JournalInterval>
  {
    MapUnion(
        ReqWriteJournals_of_reqs(disk), 
        ReqWriteJournals_of_resps(disk))
  }

  //// IndirectionTables

  function ReqReadIndirectionTables_of_reqs(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.reqReads &&
        ValidIndirectionTableLocation(LocOfReqRead(disk.reqReads[id]))
      :: LocOfReqRead(disk.reqReads[id])
  }

  function ReqReadIndirectionTables_of_resps(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.respReads
      && |disk.respReads[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidIndirectionTableLocation(LocOfRespRead(disk.respReads[id]))
      :: LocOfRespRead(disk.respReads[id])
  }

  function ReqReadIndirectionTables(disk: D.Variables) : map<D.ReqId, Location>
  {
    MapUnion(
        ReqReadIndirectionTables_of_reqs(disk), 
        ReqReadIndirectionTables_of_resps(disk))
  }

  function ReqWriteIndirectionTables_of_reqs(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.reqWrites
      && |disk.reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidIndirectionTableLocation(LocOfReqWrite(disk.reqWrites[id]))
      :: LocOfReqWrite(disk.reqWrites[id])
  }

  function ReqWriteIndirectionTables_of_resps(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.respWrites
      && ValidIndirectionTableLocation(LocOfRespWrite(disk.respWrites[id]))
      :: LocOfRespWrite(disk.respWrites[id])
  }

  function ReqWriteIndirectionTables(disk: D.Variables) : map<D.ReqId, Location>
  {
    MapUnion(
        ReqWriteIndirectionTables_of_reqs(disk), 
        ReqWriteIndirectionTables_of_resps(disk))
  }

  //// Nodes

  function ReqReadNodes_of_reqs(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.reqReads &&
        ValidNodeLocation(LocOfReqRead(disk.reqReads[id]))
      :: LocOfReqRead(disk.reqReads[id])
  }

  function ReqReadNodes_of_resps(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.respReads
      && |disk.respReads[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidNodeLocation(LocOfRespRead(disk.respReads[id]))
      :: LocOfRespRead(disk.respReads[id])
  }

  function ReqReadNodes(disk: D.Variables) : map<D.ReqId, Location>
  {
    MapUnion(
        ReqReadNodes_of_reqs(disk), 
        ReqReadNodes_of_resps(disk))
  }

  function ReqWriteNodes_of_reqs(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.reqWrites
      && |disk.reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
      && ValidNodeLocation(LocOfReqWrite(disk.reqWrites[id]))
      :: LocOfReqWrite(disk.reqWrites[id])
  }

  function ReqWriteNodes_of_resps(disk: D.Variables) : map<D.ReqId, Location>
  {
    map id | id in disk.respWrites
      && ValidNodeLocation(LocOfRespWrite(disk.respWrites[id]))
      :: LocOfRespWrite(disk.respWrites[id])
  }

  function ReqWriteNodes(disk: D.Variables) : map<D.ReqId, Location>
  {
    MapUnion(
        ReqWriteNodes_of_reqs(disk), 
        ReqWriteNodes_of_resps(disk))
  }

  ///////// Interpretation of the disk

  predicate locInBounds(loc: Location, contents: seq<byte>)
  {
    && loc.addr as int + loc.len as int <= |contents|
  }

  function atLoc(loc: Location, contents: seq<byte>) : seq<byte>
  requires locInBounds(loc, contents)
  {
    contents[loc.addr .. loc.addr as int + loc.len as int]
  }

  function atLocWithWrites(loc: Location, contents: seq<byte>, reqs: map<D.ReqId, D.ReqWrite>) : seq<byte>
  {
    withWrites(contents, reqs, loc.addr as int, loc.len as int)
  }

  function DiskNodes(disk: D.Variables) : imap<Location, G.Node>
  {
    imap loc |
      && ValidNodeLocation(loc)
      && ValidNodeBytes(atLocWithWrites(loc, disk.contents, disk.reqWrites))
    :: NodeOfBytes(atLocWithWrites(loc, disk.contents, disk.reqWrites))
  }

  function DiskIndirectionTables(disk: D.Variables) : imap<Location, IndirectionTable>
  {
    imap loc |
      && ValidIndirectionTableLocation(loc)
      && ValidIndirectionTableBytes(atLocWithWrites(loc, disk.contents, disk.reqWrites))
    :: IndirectionTableOfBytes(atLocWithWrites(loc, disk.contents, disk.reqWrites))

  }

  predicate ValidJournalBlockBytes(bytes: seq<byte>)
  {
    && JournalBytes.JournalBlockOfByteSeq(bytes).Some?
  }

  function JournalBlockOfBytes(bytes: seq<byte>) : JournalBlock
  requires ValidJournalBlockBytes(bytes)
  {
    JournalBytes.JournalBlockOfByteSeq(bytes).value
  }

  function JournalBlockAt(contents: seq<byte>, reqWrites: map<D.ReqId, D.ReqWrite>, i: int) : Option<JournalBlock>
  requires 0 <= i < NumJournalBlocks() as int
  {
    var loc := JournalRangeLocation(i as uint64, 1);
    if ValidJournalBlockBytes(atLocWithWrites(loc, contents, reqWrites))
    then
      Some(JournalBlockOfBytes(
        atLocWithWrites(loc, contents, reqWrites)))
    else
      None
  }

  function {:opaque} DiskJournalOfContentsI(contents: seq<byte>, reqWrites: map<D.ReqId, D.ReqWrite>, i: int) : (res : seq<Option<JournalBlock>>)
  requires 0 <= i <= NumJournalBlocks() as int
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == JournalBlockAt(contents, reqWrites, j)
  {
    if i == 0 then [] else
      DiskJournalOfContentsI(contents, reqWrites, i-1) + [JournalBlockAt(contents, reqWrites, i-1)]
  }

  function DiskJournal(disk: D.Variables) : seq<Option<JournalBlock>>
  {
    DiskJournalOfContentsI(disk.contents, disk.reqWrites,
        NumJournalBlocks() as int)
  }

  function DiskSuperblockAtLoc(contents: seq<byte>, loc: Location) : Option<Superblock>
  requires ValidSuperblockLocation(loc)
  {
    if locInBounds(loc, contents)
      && ValidSuperblockBytes(atLoc(loc, contents))
    then Some(SuperblockOfBytes(atLoc(loc, contents)))
    else None
  }

  function DiskSuperblock1(disk: D.Variables) : Option<Superblock>
  {
    DiskSuperblockAtLoc(disk.contents, Superblock1Location())
  }

  function DiskSuperblock2(disk: D.Variables) : Option<Superblock>
  {
    DiskSuperblockAtLoc(disk.contents, Superblock2Location())
  }

  //// Putting stuff together

  function IBlockDisk(disk: D.Variables) : BlockDisk.Variables
  {
    BlockDisk.Variables(
      ReqReadIndirectionTables(disk),
      ReqReadNodes(disk),
      ReqWriteIndirectionTables(disk),
      ReqWriteNodes(disk),
      DiskIndirectionTables(disk),
      DiskNodes(disk)
    )
  }

  function IJournalDisk(disk: D.Variables) : JournalDisk.Variables
  requires reqWritesHaveValidSuperblocks(disk.reqWrites)
  {
    JournalDisk.Variables(
      ReqReadSuperblock1(disk),
      ReqReadSuperblock2(disk),
      ReqReadJournals(disk),
      ReqWriteSuperblock1(disk),
      ReqWriteSuperblock2(disk),
      ReqWriteJournals(disk),
      DiskSuperblock1(disk),
      DiskSuperblock2(disk),
      DiskJournal(disk)
    )
  }

  //// Invariant stuff

  predicate reqWritesHaveValidLocations(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites ::
        && |reqWrites[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidLocation(LocOfReqWrite(reqWrites[id]))
  }

  predicate reqReadsHaveValidLocations(reqReads: map<D.ReqId, D.ReqRead>)
  {
    forall id | id in reqReads ::
        ValidLocation(LocOfReqRead(reqReads[id]))
  }

  predicate respWritesHaveValidLocations(respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id | id in respWrites ::
        ValidLocation(LocOfRespWrite(respWrites[id]))
  }

  predicate respReadsHaveValidLocations(respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        && |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidLocation(LocOfRespRead(respReads[id]))
  }

  predicate respReadHasCorrectData(contents: seq<byte>, respRead: D.RespRead)
  {
    && |respRead.bytes| < 0x1_0000_0000_0000_0000
    && locInBounds(LocOfRespRead(respRead), contents)
    && atLoc(LocOfRespRead(respRead), contents)
        == respRead.bytes
  }

  predicate respReadsHaveCorrectData(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        respReadHasCorrectData(contents, respReads[id])
  }

  predicate writesOverlap(r1: D.ReqWrite, r2: D.ReqWrite)
  requires |r1.bytes| < 0x1_0000_0000_0000_0000
  requires |r2.bytes| < 0x1_0000_0000_0000_0000
  {
    overlap(LocOfReqWrite(r1), LocOfReqWrite(r2))
  }

  predicate allWritesDontOverlap(reqWrites: map<D.ReqId, D.ReqWrite>)
  requires reqWritesHaveValidLocations(reqWrites)
  {
    forall id1, id2 ::
      id1 in reqWrites && id2 in reqWrites && id1 != id2
      ==> !writesOverlap(reqWrites[id1], reqWrites[id2])
  }

  predicate writeReqReadOverlap(r1: D.ReqWrite, r2: D.ReqRead)
  requires |r1.bytes| < 0x1_0000_0000_0000_0000
  {
    overlap(LocOfReqRead(r2), LocOfReqWrite(r1))
  }

  predicate allWritesReqReadsDontOverlap(reqWrites: map<D.ReqId, D.ReqWrite>, reqReads: map<D.ReqId, D.ReqRead>)
  requires reqWritesHaveValidLocations(reqWrites)
  {
    forall id1, id2 ::
      id1 in reqWrites && id2 in reqReads
      ==> !writeReqReadOverlap(reqWrites[id1], reqReads[id2])
  }

  predicate writeRespReadOverlap(r1: D.ReqWrite, r2: D.RespRead)
  requires |r1.bytes| < 0x1_0000_0000_0000_0000
  requires |r2.bytes| < 0x1_0000_0000_0000_0000
  {
    overlap(LocOfRespRead(r2), LocOfReqWrite(r1))
  }

  predicate allWritesRespReadsDontOverlap(reqWrites: map<D.ReqId, D.ReqWrite>, respReads: map<D.ReqId, D.RespRead>)
  requires reqWritesHaveValidLocations(reqWrites)
  requires respReadsHaveValidLocations(respReads)
  {
    forall id1, id2 ::
      id1 in reqWrites && id2 in respReads
      ==> !writeRespReadOverlap(reqWrites[id1], respReads[id2])
  }

  ///// respWrites are correct

  predicate respWritesHaveValidNodes(contents: seq<byte>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id | id in respWrites ::
        ValidNodeLocation(LocOfRespWrite(respWrites[id])) ==>
          && locInBounds(LocOfRespWrite(respWrites[id]), contents)
          && ValidNodeBytes(atLoc(LocOfRespWrite(respWrites[id]), contents))
  }

  predicate respWritesHaveValidIndirectionTables(contents: seq<byte>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id | id in respWrites ::
        ValidIndirectionTableLocation(LocOfRespWrite(respWrites[id])) ==>
          && locInBounds(LocOfRespWrite(respWrites[id]), contents)
          && ValidIndirectionTableBytes(atLoc(LocOfRespWrite(respWrites[id]), contents))
  }

  predicate respWritesHaveValidJournals(contents: seq<byte>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id | id in respWrites ::
        ValidJournalLocation(LocOfRespWrite(respWrites[id])) ==>
          && locInBounds(LocOfRespWrite(respWrites[id]), contents)
          && ValidJournalBytes(atLoc(LocOfRespWrite(respWrites[id]), contents))
  }

  predicate respWritesHaveValidSuperblocks(contents: seq<byte>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id | id in respWrites ::
        ValidSuperblockLocation(LocOfRespWrite(respWrites[id])) ==>
          && locInBounds(LocOfRespWrite(respWrites[id]), contents)
          && ValidSuperblockBytes(atLoc(LocOfRespWrite(respWrites[id]), contents))
  }

  predicate respWritesHaveValidData(contents: seq<byte>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    && respWritesHaveValidNodes(contents, respWrites)
    && respWritesHaveValidIndirectionTables(contents, respWrites)
    && respWritesHaveValidJournals(contents, respWrites)
    && respWritesHaveValidSuperblocks(contents, respWrites)
  }

  predicate writeIdsDistinct(reqWrites: map<D.ReqId, D.ReqWrite>, respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in respWrites
      :: id1 != id2
  }

  predicate readIdsDistinct(reqReads: map<D.ReqId, D.ReqRead>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id1, id2 | id1 in reqReads && id2 in respReads
      :: id1 != id2
  }

  predicate Inv(disk: D.Variables)
  {
    && reqWritesHaveValidLocations(disk.reqWrites)
    && reqReadsHaveValidLocations(disk.reqReads)
    && respWritesHaveValidLocations(disk.respWrites)
    && respReadsHaveValidLocations(disk.respReads)
    && respReadsHaveCorrectData(disk.contents, disk.respReads)
    && reqWritesHaveValidData(disk.reqWrites)
    && respWritesHaveValidData(disk.contents, disk.respWrites)
    && allWritesDontOverlap(disk.reqWrites)
    && allWritesReqReadsDontOverlap(disk.reqWrites, disk.reqReads)
    && allWritesRespReadsDontOverlap(disk.reqWrites, disk.respReads)
    && writeIdsDistinct(disk.reqWrites, disk.respWrites)
    && readIdsDistinct(disk.reqReads, disk.respReads)
  }

  lemma RefinesReqReadOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.ReqReadOp?
  requires ValidDiskOp(dop)
  requires D.RecvRead(k, disk, disk', dop)
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDiskOp_of_ReqRead(dop.id, dop.reqRead))
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_ReqRead(dop.id, dop.reqRead))
  {
  }

  lemma RefinesReqWriteOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.ReqWriteOp?
  requires ValidDiskOp(dop)
  requires D.RecvWrite(k, disk, disk', dop)

  requires forall id | id in disk.reqWrites
    :: !writesOverlap(dop.reqWrite, disk.reqWrites[id])
  requires forall id | id in disk.reqReads
    :: !writeReqReadOverlap(dop.reqWrite, disk.reqReads[id])
  requires forall id | id in disk.respReads
    :: !writeRespReadOverlap(dop.reqWrite, disk.respReads[id])

  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDiskOp_of_ReqWrite(dop.id, dop.reqWrite))
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_ReqWrite(dop.id, dop.reqWrite))
  {
    var loc := LocOfReqWrite(dop.reqWrite);

    assert disk.contents == disk'.contents;

    getReqWriteSelf(disk.contents, disk'.reqWrites, dop.id);

    forall l | !overlap(l, loc)
    ensures atLocWithWrites(l, disk.contents, disk.reqWrites)
         == atLocWithWrites(l, disk'.contents, disk'.reqWrites)
    {
      newReqWritePreserve(disk.contents, disk.reqWrites,
          dop.id, dop.reqWrite, l.addr as int, l.len as int);
    }

    if ValidNodeLocation(loc) {
      forall l | ValidLocation(l) && !ValidNodeLocation(l)
          && overlap(l, loc)
      ensures false
      {
        overlappingLocsSameType(l, loc);
      }

      assert IBlockDisk(disk').reqWriteNodes[dop.id] == loc;

      assert loc != Superblock1Location();
      assert loc != Superblock2Location();
      assert overlap(Superblock1Location(), Superblock1Location());
      assert overlap(Superblock2Location(), Superblock2Location());
      if ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock1Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock1Location();

        /*assert ReqWriteWithLoc(disk'.reqWrites, Superblock1Location()).Some?;
        var id2 := ReqWriteWithLoc(disk'.reqWrites, Superblock1Location()).value;
        assert id2 in disk'.reqWrites
          && |disk'.reqWrites[id2].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id2]) == Superblock1Location();
        assert id1 != dop.id;
        assert id2 != dop.id;
        assert id2 in disk.reqWrites
          && |disk.reqWrites[id2].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id2]) == Superblock1Location();*/
      } else {
        assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
            == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());
      }

      assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());

      if ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock2Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock2Location();
      }

      assert ReqWriteWithLoc(disk.reqWrites, Superblock2Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location());

      assert IJournalDisk(disk).superblock1
          == IJournalDisk(disk').superblock1;
      assert IJournalDisk(disk).superblock2
          == IJournalDisk(disk').superblock2;
      assert IJournalDisk(disk).journal
          == IJournalDisk(disk').journal;
      assert IJournalDisk(disk).reqWriteSuperblock1
          == IJournalDisk(disk').reqWriteSuperblock1;
      assert IJournalDisk(disk).reqWriteSuperblock2
          == IJournalDisk(disk').reqWriteSuperblock2;
      assert IJournalDisk(disk).reqWriteJournals
          == IJournalDisk(disk').reqWriteJournals;

      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
    }
    else if ValidIndirectionTableLocation(loc) {
      forall l | ValidLocation(l) && !ValidIndirectionTableLocation(l)
          && overlap(l, loc)
      ensures false
      {
        overlappingLocsSameType(l, loc);
      }

      if ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock1Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock1Location();
      } else {
        assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
            == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());
      }
      assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());
      if ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock2Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock2Location();
      }
      assert ReqWriteWithLoc(disk.reqWrites, Superblock2Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location());


      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
    }
    else if ValidJournalLocation(loc) {
      forall l | ValidLocation(l) && !ValidJournalLocation(l)
          && overlap(l, loc)
      ensures false
      {
        overlappingLocsSameType(l, loc);
      }

      if ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock1Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock1Location();
      } else {
        assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
            == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());
      }
      assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());
      if ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).Some? {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).value;
        assert id1 in disk.reqWrites
          && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk.reqWrites[id1]) == Superblock2Location();
        assert id1 != dop.id;
        assert id1 in disk.reqWrites
          && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
          && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock2Location();
      }
      assert ReqWriteWithLoc(disk.reqWrites, Superblock2Location())
          == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location());

      var newEntries := IDiskOp(dop).jdop.reqWriteJournal.journal;
      var interval := JournalInterval(
          IDiskOp(dop).jdop.reqWriteJournal.start,
          |IDiskOp(dop).jdop.reqWriteJournal.journal|);
      var journal := DiskJournal(disk);
      var journal' := DiskJournal(disk');
      assert JournalUpdate(journal, journal', interval, newEntries) by {
        forall i | 0 <= i < |journal|
        ensures journal'[i] == CyclicSpliceValue(
              journal, interval, newEntries, i)
        {
          if interval.start <= i < interval.start + interval.len {
            JournalBytes.JournalBlockOfJournalRange(dop.reqWrite.bytes, i - interval.start);
            getReqWriteSelfSub(disk.contents, disk'.reqWrites, dop.id, (i - interval.start) * 4096, 4096);
            calc {
              journal'[i];
              JournalBlockAt(disk'.contents, disk'.reqWrites, i);
              Some(JournalBlockOfBytes(atLocWithWrites(JournalRangeLocation(i as uint64, 1), disk'.contents, disk'.reqWrites)));
              JournalBytes.JournalBlockOfByteSeq(dop.reqWrite.bytes[(i - interval.start) * 4096 .. (i - interval.start + 1) * 4096]);
              Some(JournalBytes.JournalRangeOfByteSeq(dop.reqWrite.bytes).value[i - interval.start]);
              Some(newEntries[i - interval.start]);
            }
          } else if interval.start <= i + NumJournalBlocks() as int < interval.start + interval.len {
            assert journal'[i] == Some(newEntries[i + NumJournalBlocks() as int - interval.start]);
          } else {
            assert journal'[i] == journal[i];
          }
        }
        reveal_JournalUpdate();
      }

      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
    }
    else if ValidSuperblockLocation(loc) {
      forall l | ValidLocation(l) && !ValidSuperblockLocation(l)
          && overlap(l, loc)
      ensures false
      {
        overlappingLocsSameType(l, loc);
      }

      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_ReqWrite(dop.id, dop.reqWrite));
    }
  }
}

