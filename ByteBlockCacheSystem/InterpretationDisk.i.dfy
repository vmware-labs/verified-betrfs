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
  import opened Sequences

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
    /*&& 0 <= loc.addr as int
      <= loc.addr as int + loc.len as int
      <= |disk.contents|
    && ValidSuperblockBytes(
        disk.contents[loc.addr .. loc.addr as int + loc.len as int])*/
    && locInBounds(loc, disk.contents)
    && ValidSuperblockBytes(atLoc(loc, disk.contents))
  }

  function SuperblockAtLoc(disk: D.Variables, loc: Location) : Superblock
  requires HasSuperblockAtLoc(disk, loc)
  {
    SuperblockOfBytes(atLoc(loc, disk.contents))
    /*SuperblockOfBytes(
        disk.contents[loc.addr .. loc.addr as int + loc.len as int])*/
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
    && D.AllChecksumsCheckOut(
          atLoc(LocOfRespRead(respRead), contents),
          respRead.bytes)
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

  predicate writesReqRespOverlap(r1: D.ReqWrite, r2: D.RespWrite)
  requires |r1.bytes| < 0x1_0000_0000_0000_0000
  {
    overlap(LocOfReqWrite(r1), LocOfRespWrite(r2))
  }

  predicate allWritesReqsRespsDontOverlap(reqWrites: map<D.ReqId, D.ReqWrite>, respWrites: map<D.ReqId, D.RespWrite>)
  requires reqWritesHaveValidLocations(reqWrites)
  {
    forall id1, id2 ::
      id1 in reqWrites && id2 in respWrites
      ==> !writesReqRespOverlap(reqWrites[id1], respWrites[id2])
  }

  predicate writesRespRespOverlap(r1: D.RespWrite, r2: D.RespWrite)
  {
    overlap(LocOfRespWrite(r1), LocOfRespWrite(r2))
  }

  predicate allWriteRespsDontOverlap(respWrites: map<D.ReqId, D.RespWrite>)
  {
    forall id1, id2 ::
      id1 in respWrites && id2 in respWrites && id1 != id2
      ==> !writesRespRespOverlap(respWrites[id1], respWrites[id2])
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

  ///// respReads are reads of valid data

  predicate respReadsHaveValidNodes(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidNodeLocation(LocOfRespRead(respReads[id])) ==>
          && locInBounds(LocOfRespRead(respReads[id]), contents)
          && ValidNodeBytes(atLoc(LocOfRespRead(respReads[id]), contents))
  }

  predicate respReadsHaveValidIndirectionTables(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidIndirectionTableLocation(LocOfRespRead(respReads[id])) ==>
          && locInBounds(LocOfRespRead(respReads[id]), contents)
          && ValidIndirectionTableBytes(atLoc(LocOfRespRead(respReads[id]), contents))
  }

  predicate respReadsHaveValidJournals(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidJournalLocation(LocOfRespRead(respReads[id])) ==>
          && locInBounds(LocOfRespRead(respReads[id]), contents)
          && ValidJournalBytes(atLoc(LocOfRespRead(respReads[id]), contents))
  }

  predicate respReadsHaveValidSuperblocks(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    forall id | id in respReads ::
        |respReads[id].bytes| < 0x1_0000_0000_0000_0000
        && ValidSuperblockLocation(LocOfRespRead(respReads[id])) ==>
          && locInBounds(LocOfRespRead(respReads[id]), contents)
          && ValidSuperblockBytes(atLoc(LocOfRespRead(respReads[id]), contents))
  }

  predicate respReadsHaveValidData(contents: seq<byte>, respReads: map<D.ReqId, D.RespRead>)
  {
    && respReadsHaveValidNodes(contents, respReads)
    && respReadsHaveValidIndirectionTables(contents, respReads)
    && respReadsHaveValidJournals(contents, respReads)
    && respReadsHaveValidSuperblocks(contents, respReads)
  }

  ///// reqReads are of valid data

  predicate reqReadsHaveValidNodes(contents: seq<byte>, reqReads: map<D.ReqId, D.ReqRead>)
  {
    forall id | id in reqReads ::
        ValidNodeLocation(LocOfReqRead(reqReads[id]))
        && locInBounds(LocOfReqRead(reqReads[id]), contents) ==>
          && ValidNodeBytes(atLoc(LocOfReqRead(reqReads[id]), contents))
  }

  predicate reqReadsHaveValidIndirectionTables(contents: seq<byte>, reqReads: map<D.ReqId, D.ReqRead>)
  {
    forall id | id in reqReads ::
        ValidIndirectionTableLocation(LocOfReqRead(reqReads[id]))
        && locInBounds(LocOfReqRead(reqReads[id]), contents) ==>
          && ValidIndirectionTableBytes(atLoc(LocOfReqRead(reqReads[id]), contents))
  }

  predicate reqReadsHaveValidJournals(contents: seq<byte>, reqReads: map<D.ReqId, D.ReqRead>)
  {
    forall id | id in reqReads ::
        ValidJournalLocation(LocOfReqRead(reqReads[id]))
        && locInBounds(LocOfReqRead(reqReads[id]), contents) ==>
          && ValidJournalBytes(atLoc(LocOfReqRead(reqReads[id]), contents))
  }

  predicate reqReadsHaveValidSuperblocks(contents: seq<byte>, reqReads: map<D.ReqId, D.ReqRead>)
  {
    forall id | id in reqReads ::
        ValidSuperblockLocation(LocOfReqRead(reqReads[id]))
          && locInBounds(LocOfReqRead(reqReads[id]), contents) ==>
          && ValidSuperblockBytes(atLoc(LocOfReqRead(reqReads[id]), contents))
  }

  predicate reqReadsHaveValidData(contents: seq<byte>, reqReads: map<D.ReqId, D.ReqRead>)
  {
    && reqReadsHaveValidNodes(contents, reqReads)
    && reqReadsHaveValidIndirectionTables(contents, reqReads)
    && reqReadsHaveValidJournals(contents, reqReads)
    && reqReadsHaveValidSuperblocks(contents, reqReads)
  }


  //// more stuff

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
    && respReadsHaveValidData(disk.contents, disk.respReads)
    && reqReadsHaveValidData(disk.contents, disk.reqReads)
    && allWritesDontOverlap(disk.reqWrites)
    && allWritesReqsRespsDontOverlap(disk.reqWrites, disk.respWrites)
    && allWriteRespsDontOverlap(disk.respWrites)
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

  requires forall id | id in disk.reqWrites
      :: !writeReqReadOverlap(disk.reqWrites[id], dop.reqRead)
  requires ValidNodeLocation(LocOfReqRead(dop.reqRead)) ==>
      LocOfReqRead(dop.reqRead) in IBlockDisk(disk).nodes
  requires ValidIndirectionTableLocation(LocOfReqRead(dop.reqRead)) ==>
      LocOfReqRead(dop.reqRead) in IBlockDisk(disk).indirectionTables
  requires ValidJournalLocation(LocOfReqRead(dop.reqRead)) ==>
      Disk_HasJournalRange(
        IJournalDisk(disk).journal, 
        IDiskOp(dop).jdop.interval)
  requires LocOfReqRead(dop.reqRead) == Superblock1Location() ==>
      IJournalDisk(disk).superblock1.Some?
  requires LocOfReqRead(dop.reqRead) == Superblock2Location() ==>
      IJournalDisk(disk).superblock2.Some?

  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDiskOp_of_ReqRead(dop.id, dop.reqRead))
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_ReqRead(dop.id, dop.reqRead))
  {
    var loc := LocOfReqRead(dop.reqRead);
    if locInBounds(LocOfReqRead(dop.reqRead), disk.contents) {
      atLoc_eq_atLocWithWrites(disk.contents, disk.reqWrites, LocOfReqRead(dop.reqRead));
      assert atLoc(LocOfReqRead(dop.reqRead), disk.contents)
        == atLocWithWrites(LocOfReqRead(dop.reqRead), disk.contents, disk.reqWrites);

      if ValidJournalLocation(loc) {
        var interval := JournalIntervalOfLocation(loc);
        var bytes := atLoc(loc, disk.contents);
        forall i | 0 <= i < interval.len
        ensures JournalBytes.JournalBlockOfByteSeq(bytes[i*4096..(i+1)*4096]).Some?
        {
          block_exists_of_Disk_JournalRange(DiskJournal(disk), interval, i);
          calc {
            bytes[i*4096..(i+1)*4096];
            atLoc(loc, disk.contents)[i*4096..(i+1)*4096];
              { reveal_atLoc(); }
            disk.contents[loc.addr .. loc.addr as int + loc.len as int][i*4096..(i+1)*4096];
            { lemma_seq_slice_slice(disk.contents, loc.addr as int, loc.addr as int + loc.len as int, i*4096, (i+1)*4096); }
            disk.contents[loc.addr as int + i*4096 .. loc.addr as int + (i+1)*4096];
              { reveal_atLoc(); }
            atLoc(
                JournalRangeLocation((interval.start + i) as uint64, 1),
                disk.contents);
              {
                atLoc_eq_atLocWithWrites(disk.contents, disk.reqWrites, JournalRangeLocation((interval.start + i) as uint64, 1));
              }
            atLocWithWrites(
                JournalRangeLocation((interval.start + i) as uint64, 1),
                disk.contents, disk.reqWrites);
          }
          assert DiskJournal(disk)[interval.start + i]
              == JournalBlockAt(disk.contents, disk.reqWrites, interval.start + i);
          assert JournalBytes.JournalBlockOfByteSeq(
            bytes[i*4096..(i+1)*4096]).Some?;
        }
        JournalBytes.JournalRangeOfJournalBlocks(bytes, interval.len);
        assert JournalBytes.JournalRangeOfByteSeq(bytes).Some?;
        assert ValidJournalBytes(bytes);
      }
    }
  }

  predicate reqWriteDisjointFromCurrent(disk: D.Variables, reqWrite: D.ReqWrite)
  requires Inv(disk)
  {
    && |reqWrite.bytes| < 0x1_0000_0000_0000_0000
    && (forall id | id in disk.reqWrites
      :: !writesOverlap(reqWrite, disk.reqWrites[id]))
    && (forall id | id in disk.respWrites
      :: !writesReqRespOverlap(reqWrite, disk.respWrites[id]))
    && (forall id | id in disk.reqReads
      :: !writeReqReadOverlap(reqWrite, disk.reqReads[id]))
    && (forall id | id in disk.respReads
      :: !writeRespReadOverlap(reqWrite, disk.respReads[id]))
  }

  lemma RefinesReqWriteOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.ReqWriteOp?
  requires ValidDiskOp(dop)
  requires D.RecvWrite(k, disk, disk', dop)

  requires reqWriteDisjointFromCurrent(disk, dop.reqWrite)

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

    if loc != Superblock1Location() {
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
    }
    if loc != Superblock2Location() { 
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

  lemma RefinesReqWrite2Op(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.ReqWrite2Op?
  requires ValidDiskOp(dop)
  requires D.RecvWrite2(k, disk, disk', dop)

  requires reqWriteDisjointFromCurrent(disk, dop.reqWrite1)
  requires reqWriteDisjointFromCurrent(disk, dop.reqWrite2)

  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDisk.NoDiskOp)
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_ReqWrite2(dop.id1, dop.id2, dop.reqWrite1, dop.reqWrite2))
  {
    var loc1 := LocOfReqWrite(dop.reqWrite1);
    var loc2 := LocOfReqWrite(dop.reqWrite2);
    assert ValidJournalLocation(loc1);
    assert ValidJournalLocation(loc2);

    var r1 := disk.reqWrites[dop.id1 := dop.reqWrite1];
    forall l | !overlap(l, loc1) && !overlap(l, loc2)
    ensures atLocWithWrites(l, disk.contents, disk.reqWrites)
         == atLocWithWrites(l, disk'.contents, disk'.reqWrites)
    {
      newReqWritePreserve(disk.contents, disk.reqWrites,
          dop.id1, dop.reqWrite1, l.addr as int, l.len as int);
      newReqWritePreserve(disk.contents, r1,
          dop.id2, dop.reqWrite2, l.addr as int, l.len as int);
    }

    assert overlap(Superblock1Location(), Superblock1Location());
    assert overlap(Superblock2Location(), Superblock2Location());
    if ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).Some? {
      var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location()).value;
      assert id1 in disk.reqWrites
        && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
        && LocOfReqWrite(disk.reqWrites[id1]) == Superblock1Location();
      assert id1 in disk.reqWrites
        && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
        && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock1Location();
    }

    assert ReqWriteWithLoc(disk.reqWrites, Superblock1Location())
        == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location());

    if ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).Some? {
      var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location()).value;
      assert id1 in disk.reqWrites
        && |disk.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
        && LocOfReqWrite(disk.reqWrites[id1]) == Superblock2Location();
      assert id1 in disk.reqWrites
        && |disk'.reqWrites[id1].bytes| < 0x1_0000_0000_0000_0000
        && LocOfReqWrite(disk'.reqWrites[id1]) == Superblock2Location();
    }

    assert ReqWriteWithLoc(disk.reqWrites, Superblock2Location())
        == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location());

    forall l | ValidLocation(l) && !ValidJournalLocation(l)
        && overlap(l, loc1)
    ensures false
    {
      overlappingLocsSameType(l, loc1);
    }

    forall l | ValidLocation(l) && !ValidJournalLocation(l)
        && overlap(l, loc2)
    ensures false
    {
      overlappingLocsSameType(l, loc2);
    }

    var newEntries := IDiskOp(dop).jdop.reqWriteJournal.journal;
    var interval := JournalInterval(
          IDiskOp(dop).jdop.reqWriteJournal.start,
          |IDiskOp(dop).jdop.reqWriteJournal.journal|);
    assert interval.start + interval.len > NumJournalBlocks() as int;
    var journal := DiskJournal(disk);
    var journal' := DiskJournal(disk');

    var interval1 := JournalInterval(interval.start, NumJournalBlocks() as int - interval.start);
    var interval2 := JournalInterval(0, interval.len - (NumJournalBlocks() as int - interval.start));

    assert JournalUpdate(journal, journal', interval, newEntries) by {
      forall i | 0 <= i < |journal|
      ensures journal'[i] == CyclicSpliceValue(
            journal, interval, newEntries, i)
      {
        if interval1.start <= i < interval1.start + interval1.len {
          JournalBytes.JournalBlockOfJournalRange(dop.reqWrite1.bytes, i - interval1.start);
          getReqWriteSelfSub(disk.contents, r1, dop.id1, (i - interval1.start) * 4096, 4096);
          newReqWritePreserve(disk.contents, r1, dop.id2, dop.reqWrite2, loc1.addr as int + (i - interval1.start) * 4096, 4096);
          calc {
            journal'[i];
            JournalBlockAt(disk'.contents, disk'.reqWrites, i);
            Some(JournalBlockOfBytes(atLocWithWrites(JournalRangeLocation(i as uint64, 1), disk'.contents, disk'.reqWrites)));
            JournalBytes.JournalBlockOfByteSeq(dop.reqWrite1.bytes[(i - interval1.start) * 4096 .. (i - interval1.start + 1) * 4096]);
            Some(JournalBytes.JournalRangeOfByteSeq(dop.reqWrite1.bytes).value[i - interval1.start]);
            Some(newEntries[i - interval1.start]);
          }
        } else if interval2.start <= i < interval2.start + interval2.len {
          JournalBytes.JournalBlockOfJournalRange(dop.reqWrite2.bytes, i - interval2.start);
          getReqWriteSelfSub(disk.contents, disk'.reqWrites, dop.id2, (i - interval2.start) * 4096, 4096);
          calc {
            journal'[i];
            JournalBlockAt(disk'.contents, disk'.reqWrites, i);
            Some(JournalBlockOfBytes(atLocWithWrites(JournalRangeLocation(i as uint64, 1), disk'.contents, disk'.reqWrites)));
            JournalBytes.JournalBlockOfByteSeq(dop.reqWrite2.bytes[(i - interval2.start) * 4096 .. (i - interval2.start + 1) * 4096]);
            Some(JournalBytes.JournalRangeOfByteSeq(dop.reqWrite2.bytes).value[i - interval2.start]);
            Some(newEntries[i - interval2.start + NumJournalBlocks() as int - interval1.start]);
          }
        //} else if interval.start <= i + NumJournalBlocks() as int < interval.start + interval.len {
        //  assert journal'[i] == Some(newEntries[i + NumJournalBlocks() as int - interval.start]);
        } else {
          assert journal'[i] == journal[i];
        }
      }
      reveal_JournalUpdate();
    }

    assert BlockDisk.Next(BlockDisk.Constants(),
        IBlockDisk(disk), IBlockDisk(disk'),
        BlockDisk.NoDiskOp);
    assert JournalDisk.Next(JournalDisk.Constants(),
        IJournalDisk(disk), IJournalDisk(disk'),
        JournalDiskOp_of_ReqWrite2(dop.id1, dop.id2, dop.reqWrite1, dop.reqWrite2));
  }

  lemma RefinesRespReadOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.RespReadOp?
  requires ValidDiskOp(dop)
  requires D.AckRead(k, disk, disk', dop)
  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDiskOp_of_RespRead(dop.id, dop.respRead))
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_RespRead(dop.id, dop.respRead))
  {
    var loc := LocOfRespRead(dop.respRead);
    atLoc_eq_atLocWithWrites(disk.contents, disk.reqWrites, loc);
    if ValidJournalLocation(loc) {
      var journal := DiskJournal(disk);
      var interval := JournalIntervalOfLocation(loc);
      var jr := JournalBytes.JournalRangeOfByteSeq(dop.respRead.bytes);
      if jr.Some? {
        forall i | 0 <= i < interval.len
        ensures journal[interval.start + i] == Some(jr.value[i])
        {
          var loc1 := JournalRangeLocation((interval.start + i) as uint64, 1);
          var bytes := atLoc(loc, disk.contents);

          calc {
            bytes[i*4096..(i+1)*4096];
            atLoc(loc, disk.contents)[i*4096..(i+1)*4096];
              { reveal_atLoc(); }
            disk.contents[loc.addr .. loc.addr as int + loc.len as int][i*4096..(i+1)*4096];
            { lemma_seq_slice_slice(disk.contents, loc.addr as int, loc.addr as int + loc.len as int, i*4096, (i+1)*4096); }
            disk.contents[loc.addr as int + i*4096 .. loc.addr as int + (i+1)*4096];
              { reveal_atLoc(); }
            atLoc(
                JournalRangeLocation((interval.start + i) as uint64, 1),
                disk.contents);
              {
                atLoc_eq_atLocWithWrites(disk.contents, disk.reqWrites, JournalRangeLocation((interval.start + i) as uint64, 1));
              }
            atLocWithWrites(
                JournalRangeLocation((interval.start + i) as uint64, 1),
                disk.contents, disk.reqWrites);
          }
          JournalBytes.JournalBlockOfJournalRange(bytes, i);

          assert ValidJournalBlockBytes(atLocWithWrites(loc1, disk.contents, disk.reqWrites));
          calc {
            journal[interval.start + i];
            JournalBlockAt(disk.contents, disk.reqWrites, interval.start + i);
            Some(JournalBlockOfBytes(
                atLocWithWrites(loc1, disk.contents, disk.reqWrites)));
            JournalBytes.JournalBlockOfByteSeq(atLocWithWrites(loc1, disk.contents, disk.reqWrites));
            {
              calc {
                atLocWithWrites(loc1, disk.contents, disk.reqWrites);
                bytes[4096*i .. 4096*(i+1)];
                {
                  var realContents := bytes;
                  var fakeContents := dop.respRead.bytes;
                  assert fakeContents[4096*i..4096*(i+1)] == realContents[4096*i..4096*(i+1)] by {
                    assert D.ChecksumsCheckOutForSlice(realContents, fakeContents, 4096*i, 4096*(i+1));
                    assert D.ChecksumChecksOut(realContents[4096*i..4096*(i+1)])
                      by {
                        JournalBytes.reveal_JournalBlockOfByteSeq();
                      }
                    assert D.ChecksumChecksOut(fakeContents[4096*i..4096*(i+1)])
                      by {
                        JournalBytes.JournalBlockOfJournalRange(dop.respRead.bytes, i);
                        JournalBytes.reveal_JournalBlockOfByteSeq();
                      }
                  }
                }
                dop.respRead.bytes[4096*i .. 4096*(i+1)];
              }
            }
            JournalBytes.JournalBlockOfByteSeq(dop.respRead.bytes[4096*i .. 4096*(i+1)]);
            {
              JournalBytes.JournalBlockOfJournalRange(dop.respRead.bytes, i);
            }
            Some(JournalBytes.JournalRangeOfByteSeq(dop.respRead.bytes).value[i]);
            Some(jr.value[i]);
          }
        }

        get_Disk_JournalRange(
          DiskJournal(disk),
          interval,
          jr.value);
      }

      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_RespRead(dop.id, dop.respRead));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_RespRead(dop.id, dop.respRead));

    } else {
      var realContents := atLoc(LocOfRespRead(dop.respRead), disk.contents);
      var fakeContents := dop.respRead.bytes;
      if ValidCheckedBytes(fakeContents) {
        assert fakeContents == realContents by {
          assert D.ChecksumsCheckOutForSlice(realContents, fakeContents, 0, |realContents|);
          assert D.ChecksumChecksOut(realContents[0..|realContents|])
            by {
              assert realContents[0..|realContents|] == realContents;
              reveal_ValidCheckedBytes();
            }
          assert D.ChecksumChecksOut(fakeContents[0..|realContents|])
            by {
              assert fakeContents[0..|realContents|] == fakeContents;
              reveal_ValidCheckedBytes();
            }
        }
      }

      assert BlockDisk.Next(BlockDisk.Constants(),
          IBlockDisk(disk), IBlockDisk(disk'),
          BlockDiskOp_of_RespRead(dop.id, dop.respRead));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_RespRead(dop.id, dop.respRead));
    }
  }

  lemma RefinesRespWriteOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.RespWriteOp?
  requires ValidDiskOp(dop)
  requires D.AckWrite(k, disk, disk', dop)
  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDiskOp_of_RespWrite(dop.id, dop.respWrite))
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDiskOp_of_RespWrite(dop.id, dop.respWrite))
  {
    var loc := LocOfRespWrite(dop.respWrite);
    if ValidSuperblockLocation(loc) {
      //assert ValidSuperblockBytes(atLoc(LocOfRespWrite(respWrites[id]), contents));
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_RespWrite(dop.id, dop.respWrite));
    } else if ValidJournalLocation(loc) {
      assert JournalDisk.Next(JournalDisk.Constants(),
          IJournalDisk(disk), IJournalDisk(disk'),
          JournalDiskOp_of_RespWrite(dop.id, dop.respWrite));
    }
  }

  lemma RefinesStutterOp(k: D.Constants, disk: D.Variables, disk': D.Variables, dop: D.DiskOp)
  requires Inv(disk)
  requires dop.NoDiskOp?
  requires ValidDiskOp(dop)
  requires D.Stutter(k, disk, disk', dop)
  ensures Inv(disk')
  ensures BlockDisk.Next(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'),
      BlockDisk.NoDiskOp)
  ensures JournalDisk.Next(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'),
      JournalDisk.NoDiskOp)
  {
  }

  lemma RefinesProcessRead(k: D.Constants, disk: D.Variables, disk': D.Variables, id: D.ReqId, fakeContents: seq<byte>)
  requires Inv(disk)
  requires D.ProcessReadFailure(k, disk, disk', id, fakeContents)
  ensures Inv(disk')
  ensures IBlockDisk(disk) == IBlockDisk(disk')
  ensures IJournalDisk(disk) == IJournalDisk(disk')
  {
    reveal_atLoc();
  }

  lemma RefinesProcessWrite(k: D.Constants, disk: D.Variables, disk': D.Variables, id: D.ReqId)
  requires Inv(disk)
  requires D.ProcessWrite(k, disk, disk', id)
  ensures Inv(disk')
  ensures IBlockDisk(disk) == IBlockDisk(disk')
  ensures IJournalDisk(disk) == IJournalDisk(disk')
    || JournalDisk.ProcessWriteSuperblock(JournalDisk.Constants(),   
          IJournalDisk(disk), IJournalDisk(disk'), 0)
    || JournalDisk.ProcessWriteSuperblock(JournalDisk.Constants(),   
          IJournalDisk(disk), IJournalDisk(disk'), 1)
  {
    forall l
    ensures atLocWithWrites(l, disk.contents, disk.reqWrites)
         == atLocWithWrites(l, disk'.contents, disk'.reqWrites)
    {
      onApplyWrite(disk.contents, disk.reqWrites, l.addr as int, l.len as int, id);
    }

    var loc := LocOfReqWrite(disk.reqWrites[id]);

    assert |disk.contents| == |disk'.contents| by { D.reveal_splice(); }

    forall l | !overlap(loc, l) && locInBounds(l, disk.contents)
    ensures atLoc(l, disk.contents)
        == atLoc(l, disk'.contents)
    {
      var a := atLoc(l, disk.contents);
      var b := atLoc(l, disk'.contents);
      forall i | 0 <= i < |a| ensures a[i] == b[i]
      {
        D.reveal_splice();
        reveal_atLoc();
        assert a[i] == b[i]; // Fixes verification failure somehow. -- robj
      }
    }

    assert locInBounds(loc, disk'.contents);
    assert atLoc(loc, disk'.contents) == disk.reqWrites[id].bytes by {
      D.reveal_splice();
      reveal_atLoc();
    }

    /*forall id | id in disk'.respReads
    ensures respReadHasCorrectData(disk'.contents, disk'.respReads[id])
    {
    }*/

    if loc == Superblock1Location() {
      /*assert IJournalDisk(disk').superblock1 ==
          Some(SuperblockOfBytes(disk.reqWrites[id].bytes));
      assert SuperblockOfBytes(disk.reqWrites[id].bytes)
          == IJournalDisk(disk).reqWriteSuperblock1.value.req.superblock;

      assert IJournalDisk(disk').superblock2 ==
          IJournalDisk(disk).superblock2;
      assert IJournalDisk(disk').journal ==
          IJournalDisk(disk).journal;

      assert IJournalDisk(disk').reqReadSuperblock1 ==
          IJournalDisk(disk).reqReadSuperblock1;
      assert IJournalDisk(disk').reqReadSuperblock2 ==
          IJournalDisk(disk).reqReadSuperblock2;
      assert IJournalDisk(disk').reqReadJournals ==
          IJournalDisk(disk).reqReadJournals;*/

      assert IJournalDisk(disk').reqWriteSuperblock1 ==
          IJournalDisk(disk).reqWriteSuperblock1 by {
        assert id in disk'.respWrites;
        assert LocOfRespWrite(disk'.respWrites[id]) == loc;
        assert id == RespWriteWithLoc(disk'.respWrites, loc).value;
      }

      assert IJournalDisk(disk').reqWriteSuperblock2 ==
          IJournalDisk(disk).reqWriteSuperblock2 by {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location());
        if id1.Some? {
          assert id1.value in disk'.reqWrites;
          assert LocOfReqWrite(disk'.reqWrites[id1.value]) == Superblock2Location();
          assert id1.value == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location()).value;
        }
        var id2 := RespWriteWithLoc(disk.respWrites, Superblock2Location());
        if id2.Some? {
          assert id2.value in disk'.respWrites;
          assert LocOfRespWrite(disk'.respWrites[id2.value]) == Superblock2Location();
          assert id2.value == RespWriteWithLoc(disk'.respWrites, Superblock2Location()).value;
        }
      }

      //assert IJournalDisk(disk').reqWriteJournals ==
      //    IJournalDisk(disk).reqWriteJournals;

      assert JournalDisk.ProcessWriteSuperblock(
          JournalDisk.Constants(),   
          IJournalDisk(disk), IJournalDisk(disk'), 0);
    } else if loc == Superblock2Location() {
      assert IJournalDisk(disk').reqWriteSuperblock2 ==
          IJournalDisk(disk).reqWriteSuperblock2 by {
        assert id in disk'.respWrites;
        assert LocOfRespWrite(disk'.respWrites[id]) == loc;
        assert id == RespWriteWithLoc(disk'.respWrites, loc).value;
      }

      assert IJournalDisk(disk').reqWriteSuperblock1 ==
          IJournalDisk(disk).reqWriteSuperblock1 by {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location());
        if id1.Some? {
          assert id1.value in disk'.reqWrites;
          assert LocOfReqWrite(disk'.reqWrites[id1.value]) == Superblock1Location();
          assert id1.value == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location()).value;
        }
        var id2 := RespWriteWithLoc(disk.respWrites, Superblock1Location());
        if id2.Some? {
          assert id2.value in disk'.respWrites;
          assert LocOfRespWrite(disk'.respWrites[id2.value]) == Superblock1Location();
          assert id2.value == RespWriteWithLoc(disk'.respWrites, Superblock1Location()).value;
        }
      }

      //assert IJournalDisk(disk').superblock2 ==
      //    Some(SuperblockOfBytes(disk.reqWrites[id].bytes));

      assert JournalDisk.ProcessWriteSuperblock(
          JournalDisk.Constants(),   
          IJournalDisk(disk), IJournalDisk(disk'), 1);
    } else {
      assert IJournalDisk(disk').reqWriteSuperblock1 ==
          IJournalDisk(disk).reqWriteSuperblock1 by {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock1Location());
        if id1.Some? {
          assert id1.value in disk'.reqWrites;
          assert LocOfReqWrite(disk'.reqWrites[id1.value]) == Superblock1Location();
          assert id1.value == ReqWriteWithLoc(disk'.reqWrites, Superblock1Location()).value;
        }
        var id2 := RespWriteWithLoc(disk.respWrites, Superblock1Location());
        if id2.Some? {
          assert id2.value in disk'.respWrites;
          assert LocOfRespWrite(disk'.respWrites[id2.value]) == Superblock1Location();
          assert id2.value == RespWriteWithLoc(disk'.respWrites, Superblock1Location()).value;
        }
      }

      assert IJournalDisk(disk').reqWriteSuperblock2 ==
          IJournalDisk(disk).reqWriteSuperblock2 by {
        var id1 := ReqWriteWithLoc(disk.reqWrites, Superblock2Location());
        if id1.Some? {
          assert id1.value in disk'.reqWrites;
          assert LocOfReqWrite(disk'.reqWrites[id1.value]) == Superblock2Location();
          assert id1.value == ReqWriteWithLoc(disk'.reqWrites, Superblock2Location()).value;
        }
        var id2 := RespWriteWithLoc(disk.respWrites, Superblock2Location());
        if id2.Some? {
          assert id2.value in disk'.respWrites;
          assert LocOfRespWrite(disk'.respWrites[id2.value]) == Superblock2Location();
          assert id2.value == RespWriteWithLoc(disk'.respWrites, Superblock2Location()).value;
        }
      }

      if overlap(Superblock1Location(), loc) {
        overlappingLocsSameType(Superblock1Location(), loc);
        assert false;
      }
      if overlap(Superblock2Location(), loc) {
        overlappingLocsSameType(Superblock2Location(), loc);
        assert false;
      }

      assert IJournalDisk(disk').superblock2 ==
          IJournalDisk(disk).superblock2;
      assert IJournalDisk(disk').journal ==
          IJournalDisk(disk).journal;

      assert IJournalDisk(disk').reqReadSuperblock1 ==
          IJournalDisk(disk).reqReadSuperblock1;
      assert IJournalDisk(disk').reqReadSuperblock2 ==
          IJournalDisk(disk).reqReadSuperblock2;
      assert IJournalDisk(disk').reqReadJournals ==
          IJournalDisk(disk).reqReadJournals;

      assert IJournalDisk(disk) == IJournalDisk(disk');
    }
  }

  lemma RefinesHavocConflictingWrites(k: D.Constants, disk: D.Variables, disk': D.Variables, id: D.ReqId, id': D.ReqId)
  requires Inv(disk)
  requires D.HavocConflictingWrites(k, disk, disk', id, id')
  ensures false
  {
  }

  lemma RefinesHavocConflictingWriteRead(k: D.Constants, disk: D.Variables, disk': D.Variables, id: D.ReqId, id': D.ReqId)
  requires Inv(disk)
  requires D.HavocConflictingWriteRead(k, disk, disk', id, id')
  ensures false
  {
  }

  lemma RefinesCrash(k: D.Constants, disk: D.Variables, disk': D.Variables)
  requires Inv(disk)
  requires D.Crash(k, disk, disk')
  ensures Inv(disk')
  ensures BlockDisk.Crash(BlockDisk.Constants(),
      IBlockDisk(disk), IBlockDisk(disk'))
  ensures JournalDisk.Crash(JournalDisk.Constants(),
      IJournalDisk(disk), IJournalDisk(disk'))
  {
    var bd := IBlockDisk(disk);
    var bd' := IBlockDisk(disk');

    forall loc | loc in bd.nodes &&
        BlockDisk.UntouchedLoc(loc, bd.reqWriteNodes)
    ensures loc in bd'.nodes && bd'.nodes[loc] == bd.nodes[loc]
    {
      forall id | id in disk.reqWrites
        && overlap(loc, LocOfReqWrite(disk.reqWrites[id]))
      ensures false
      {
        overlappingLocsSameType(loc, LocOfReqWrite(disk.reqWrites[id]));
        assert id in bd.reqWriteNodes;
      }
      onCrash(disk.contents, disk.reqWrites, loc.addr as int, loc.len as int);
    }

    forall loc | loc in bd.indirectionTables &&
        BlockDisk.UntouchedLoc(loc, bd.reqWriteIndirectionTables)
    ensures loc in bd'.indirectionTables && bd'.indirectionTables[loc] == bd.indirectionTables[loc]
    {
      forall id | id in disk.reqWrites
        && overlap(loc, LocOfReqWrite(disk.reqWrites[id]))
      ensures false
      {
        overlappingLocsSameType(loc, LocOfReqWrite(disk.reqWrites[id]));
        assert id in bd.reqWriteIndirectionTables;
      }
      onCrash(disk.contents, disk.reqWrites, loc.addr as int, loc.len as int);
    }

    var jd := IJournalDisk(disk);
    var jd' := IJournalDisk(disk');

    var journal := DiskJournal(disk);
    var journal' := DiskJournal(disk');

    forall i | 0 <= i < |journal|
        && JournalDisk.JournalUntouched(i, jd.reqWriteJournals)
    ensures journal[i] == journal'[i]
    {
      var loc := JournalRangeLocation(i as uint64, 1);
      forall id | id in disk.reqWrites
        && overlap(loc, LocOfReqWrite(disk.reqWrites[id]))
      ensures false
      {
        overlappingLocsSameType(loc, LocOfReqWrite(disk.reqWrites[id]));
        assert id in jd.reqWriteJournals;
      }
      onCrash(disk.contents, disk.reqWrites, loc.addr as int, loc.len as int);

      /*calc {
        journal[i];
        JournalBlockAt(disk.contents, disk.reqWrites, i);
        JournalBlockAt(disk.contents, map[], i);
        journal'[i];
      }*/
    }
  }

}

