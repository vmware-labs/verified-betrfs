include "AsyncDiskModel.s.dfy"
include "ByteCache.i.dfy"
module ByteSystem refines AsyncDiskModel {
  import M = ByteCache

  import opened AsyncSectorDiskModelTypes
  import opened Maps
  import BC = BlockCache
  import BJC = BlockJournalCache
  import BJD = BlockJournalDisk
  import opened DiskLayout
  import opened JournalIntervals
  import opened InterpretationDiskOps
  import opened Options

  function ReqReadWithLoc(reqReads: map<D.ReqId, D.ReqRead>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqReads && LocOfReqRead(reqReads[id]) == loc then
      Some(id)
    else
      None
  }

  function ReqWriteWithLoc(reqWrites: map<D.ReqId, D.ReqWrite>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqWrites && LocOfReqWrite(reqWrites[id]) == loc then
      Some(id)
    else
      None
  }

  function RespReadWithLoc(reqReads: map<D.ReqId, D.RespRead>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqReads && LocOfRespRead(reqReads[id]) == loc then
      Some(id)
    else
      None
  }

  function RespWriteWithLoc(reqWrites: map<D.ReqId, D.RespWrite>, loc: Location) : Option<D.ReqId>
  {
    if id :| id in reqWrites && LocOfRespWrite(reqWrites[id]) == loc then
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
    && SuperblockOfBytes(
        disk.contents[loc.addr .. loc.addr as int + loc.len as int])
  }

  function SuperblockAtLocOpt(disk: D.Variables, loc: Location) : Option<Superblock>
  {
    if HasSuperblockAtLoc(disk, loc) then
      Some(SuperblockAtLoc(disk,loc))
    else
      None
  }

  function ReqReadSuperblockAtLoc(disk: D.Variables, loc: Location) : Option<D.ReqId>
  {
    var id1 := ReqReadWithLoc(disk.reqReads, loc);
    var id2 := RespReadWithLoc(disk.respReads, loc);
    if id1.None? then id2 else id1
  }

  function ReqWriteSuperblockAtLoc(disk: D.Variables, loc: Location) : Option<JournalDisk.ReqWriteSuperblockId>
  {
    var id := ReqWriteWithLoc(disk.reqWrites, loc);
    if id.Some? then
      JournalDisk.ReqWriteSuperblockId(
        id.value,
        JournalDisk.ReqWriteSuperblock(SuperblockOfBytes(disk.reqWrites[id.value].bytes))
      )
    else (
      var id2 := RespWriteWithLoc(disk.respWrites, loc);
      if id2.Some? && HasSuperblockAtLoc(disk, loc) then
        JournalDisk.ReqWriteSuperblockId(
          id2.value,
          JournalDisk.ReqWriteSuperblock(SuperblockAtLoc(disk, loc))
        )
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

  function ReqReadSuperblock1(disk: D.Variables) : Option<JournalDisk.ReqReadSuperblockId>
  {
    ReqReadSuperblock(disk, Superblock1Location())
  }

  function ReqReadSuperblock2(disk: D.Variables) : Option<JournalDisk.ReqReadSuperblockId>
  {
    ReqReadSuperblock(disk, Superblock2Location())
  }

  function ReqWriteSuperblock1(disk: D.Variables) : Option<JournalDisk.ReqWriteSuperblockId>
  {
    ReqWriteSuperblock(disk, Superblock1Location())
  }

  function ReqWriteSuperblock2(disk: D.Variables) : Option<JournalDisk.ReqWriteSuperblockId>
  {
    ReqWriteSuperblock(disk, Superblock2Location())
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
}
