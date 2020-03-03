include "DiskLayout.i.dfy"
include "AsyncSectorDiskModel.i.dfy"

module JournalDiskUtils {
  import opened DiskLayout
  import opened NativeTypes
  import opened JournalRanges
  import opened SectorType
  import opened AsyncSectorDisk
  import opened Journal
  import opened Options

  type DiskConstants = AsyncSectorDisk.Constants
  type DiskState = AsyncSectorDisk.Variables

  predicate WFRange(start: int, len: int)
  {
    && 0 <= start < NumJournalBlocks() as int
    && 0 <= len <= NumJournalBlocks() as int
  }

  predicate Disk_HasJournalRange(
      blocks: imap<Location, Sector>, start: int, len: int)
  requires WFRange(start, len)
  {
    && (JournalFrontLocation(start as uint64, len as uint64).Some? ==>
      && JournalFrontLocation(start as uint64, len as uint64).value in blocks
      && blocks[JournalFrontLocation(start as uint64, len as uint64).value].SectorJournal?
    )
    && (JournalBackLocation(start as uint64, len as uint64).Some? ==>
      && JournalBackLocation(start as uint64, len as uint64).value in blocks
      && blocks[JournalBackLocation(start as uint64, len as uint64).value].SectorJournal?
    )
  }

  function Disk_JournalRange(blocks: imap<Location, Sector>, start: int, len: int) : JournalRange
  requires WFRange(start, len)
  requires Disk_HasJournalRange(blocks, start, len)
  {
    if JournalBackLocation(start as uint64, len as uint64).Some? then
      JournalRangeConcat(
          blocks[JournalFrontLocation(start as uint64, len as uint64).value].journal,
          blocks[JournalBackLocation(start as uint64, len as uint64).value].journal)
    else if JournalFrontLocation(start as uint64, len as uint64).Some? then
      blocks[JournalFrontLocation(start as uint64, len as uint64).value].journal
    else
      JournalRangeEmpty()
  }

  protected predicate Disk_HasJournal(
      blocks: imap<Location, Sector>, start: int, len: int)
  requires WFRange(start, len)
  {
    && Disk_HasJournalRange(blocks, start, len)
    && parseJournalRange(Disk_JournalRange(blocks, start, len)).Some?
  }

  protected function Disk_Journal(
      blocks: imap<Location, Sector>, start: int, len: int) : seq<JournalEntry>
  requires WFRange(start, len)
  requires Disk_HasJournal(blocks, start, len)
  {
    parseJournalRange(Disk_JournalRange(blocks, start, len)).value
  }

  predicate NoOverlaps(reqWrites: map<ReqId, ReqWrite>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites ::
        !overlap(reqWrites[id1.loc], reqWrites[id2.loc])
  }

  function Disk_JournalBlockAtLoc(blocks: imap<Location, Sector>, loc: Location)
    : Option<JournalRange>
  {
    if loc in blocks && blocks[loc].SectorJournal? then
      Some(blocks[loc].journal)
    else
      None
  }

  function Disk_JournalBlockAt(blocks: imap<Location, Sector>, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks()
  {
    Disk_JournalBlockAtLoc(blocks, JournalRangeLocation(i, 1))
  }

  function Queue_JournalBlockAt(reqWrites: map<ReqId, ReqWrite>, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks()
  {
    var loc := JournalRangeLocation(i, 1);
    if id :| id in reqWrites && LocationSub(loc, reqWrites[id].loc) then (
      if reqWrites[loc].sector.SectorJournal?
         && 0 <= i - JournalBlockIdx(reqWrites[id].loc) < 
            JournalRangeLen(reqWrites[loc].sector.journal) then (
        Some(JournalBlockGet(reqWrites[loc].sector.journal,
            i - JournalBlockIdx(reqWrites[id].loc)))
      ) else (
        None
      )
    ) else (
      None
    )
  }

  function DiskQueue_JournalBlockAt(disk: DiskState, i: int)
    : Option<JournalRange>
  requires 0 <= i < NumJournalBlocks()
  {
    if Queue_JournalBlockAt(disk.reqWrites, i).Some? then
      Queue_JournalBlockAt(disk.reqWrites, i)
    else
      Disk_JournalBlockAt(disk.blocks, i)
  }

  function DiskQueue_JournalBlockSeq_i(disk: DiskState, i: int)
    : (res : seq<Option<JournalRange>>)
  requires 0 <= i <= NumJournalBlocks()
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == DiskQueue_JournalBlockAt(disk, j)
  {
    if i == 0 then [] else
      Disk_JournalBlockSeq_i(disk, i-1) + [DiskQueue_JournalBlockAt(disk, i-1)]
  }

  function DiskQueue_JournalBlockSeq(disk: DiskState)
  ensures forall j | 0 <= j < NumJournalBlocks() :: res[j] == DiskQueue_JournalBlockAt(disk, j)
  {
    Disk_JournalBlockSeq_i(disk, NumJournalBlocks())
  }

  predicate DiskQueue_HasJournalRange(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  {
    NoOverlapsInRange(disk.reqWrites, 
  }

  function DiskQueue_JournalRange(
      disk: DiskState, start: int, len: int) : JournalRange
  requires WFRange(start, len)
  requires DiskQueue_HasJournal(disk, start, len)




  protected predicate DiskQueue_HasJournal(
      disk: DiskState, start: int, len: int)
  requires WFRange(start, len)

  protected function DiskQueue_Journal(
      disk: DiskState, start: int, len: int) : seq<JournalEntry>
  requires WFRange(start, len)
  requires DiskQueue_HasJournal(disk, start, len)

  lemma Disk_eq_DiskQueue(disk: DiskState, start: int, len: int)
  requires WFRange(start, len)
  requires Disk_HasJournal(disk.blocks, start, len)
  requires forall id | id in disk.reqWrites ::
      locDisjointFromCircularJournalRange(
          disk.reqWrites[id].loc, start as uint64, len as uint64)
  ensures DiskQueue_HasJournal(disk, start, len)
  ensures Disk_Journal(disk.blocks, start, len)
      == DiskQueue_Journal(disk, start, len)

  lemma Disk_Journal_empty(disk: DiskState, start: int)
  requires WFRange(start, 0)
  ensures Disk_HasJournal(disk.blocks, start, 0)
  ensures Disk_Journal(disk.blocks, start, 0) == []

  lemma DiskQueue_Journal_empty(disk: DiskState, start: int)
  requires WFRange(start, 0)
  ensures DiskQueue_HasJournal(disk, start, 0)
  ensures DiskQueue_Journal(disk, start, 0) == []

  lemma DiskQueue_Journal_append(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int, jr: JournalRange,
      dop: DiskOp)
  requires WFRange(start, len)
  requires AsyncSectorDisk.RecvWrite(k, disk, disk', dop)
  requires DiskQueue_HasJournal(disk, start, len)
  requires parseJournalRange(jr).Some?
  requires len + JournalRangeLen(jr) <= NumJournalBlocks() as int
  requires JournalPosAdd(start, len) + JournalRangeLen(jr) <= NumJournalBlocks() as int
  ensures DiskQueue_HasJournal(disk', start, len + JournalRangeLen(jr))
  ensures DiskQueue_Journal(disk', start, len + JournalRangeLen(jr))
      == DiskQueue_Journal(disk, start, len) + parseJournalRange(jr).value

  lemma DiskQueue_Journal_ProcessWrite(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int,
      id: ReqId)
  requires WFRange(start, len)
  requires AsyncSectorDisk.ProcessWrite(k, disk, disk', id)
  requires DiskQueue_HasJournal(disk, start, len)
  ensures DiskQueue_HasJournal(disk', start, len)
  ensures DiskQueue_Journal(disk', start, len)
       == DiskQueue_Journal(disk, start, len)

  lemma Disk_Journal_ProcessWrite(
      k: DiskConstants, disk: DiskState, disk': DiskState,
      start: int, len: int,
      id: ReqId)
  requires WFRange(start, len)
  requires AsyncSectorDisk.ProcessWrite(k, disk, disk', id)
  requires Disk_HasJournal(disk.blocks, start, len)
  requires locDisjointFromCircularJournalRange(
          disk.reqWrites[id].loc, start as uint64, len as uint64)
  ensures Disk_HasJournal(disk'.blocks, start, len)
  ensures Disk_Journal(disk'.blocks, start, len)
       == Disk_Journal(disk.blocks, start, len)
}
