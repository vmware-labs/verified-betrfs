include "../Betree/Betree.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../Betree/Graph.i.dfy"
include "../BlockCacheSystem/AsyncSectorDiskModel.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "JournalRange.i.dfy"

//
// A BlockCache implements the BlockInterface by caching over an
// AsyncSectorDisk. At this layer, the disk provides high-level sectors
// (containing either this module's indirection tables or the Node
// type of the application, a not-yet-bound parameter).
//
// The BlockCache provides Persistent, Frozen, and Ephemeral views of the
// application data, facilitating the crash-safety and crash recovery behavior.
//

module BlockCache refines Transactable {
  import G = PivotBetreeGraph
  import opened Maps
  import opened Options
  import opened NativeTypes
  import opened DiskLayout
  import opened Journal
  import opened JournalRanges
  import opened SectorType

  import Disk = AsyncSectorDisk

  type ReqId = Disk.ReqId
  datatype Constants = Constants()

  type DiskOp = Disk.DiskOp

  // BlockCache stuff

  datatype OutstandingWrite = OutstandingWrite(ref: Reference, loc: Location)
  datatype OutstandingRead = OutstandingRead(ref: Reference)
  //datatype OutstandingJournalWrite = OutstandingJournalWrite(index: int)

  datatype SyncReqStatus = State1 | State2 | State3

  datatype SuperblockReadResult =
      | SuperblockSuccess(value: Superblock)
      | SuperblockUnfinished
      | SuperblockCorruption

  //
  //  persistent graph
  //                  |
  //                  | journalLen  <- persistent state
  //                  |
  //                  |
  //  frozen graph    | frozenJournalPosition
  //                  |
  //                  | 
  //                  | writtenLen  <- frozen state
  //                  v \
  //                  v   inMemoryJournal
  //  ephemeral graph v /
  //                  o \
  //                  o   replayLog
  //                  o /
  //                  o             <- ephemeral state
  //
  // OR
  //
  //  persistent graph
  //                  |
  //                  | journalLen  <- persistent state
  //                  |
  //                  |
  //                  |
  //                  |
  //                  | 
  //                  | writtenLen  = frozenJournalPosition
  //                  X \
  //                  X   inMemoryJournalFrozen
  //  frozen graph    X /           <- frozen state
  //                  v \
  //                  v   inMemoryJournal
  //  ephemeral graph v /
  //                  o \
  //                  o   replayLog
  //                  o /
  //                  o             <- ephemeral state
  //
  // Note that a "state" is obtained by playing journal
  // entries on top of some map interpretation of some
  // "graph" (given by indirection table)


  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable,
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,

        outstandingIndirectionTableWrite: Option<ReqId>,
        frozenIndirectionTableLoc: Option<Location>,
        frozenJournalPosition: int,

        superblockWrite: Option<ReqId>,

        outstandingBlockWrites: map<ReqId, OutstandingWrite>,
        outstandingBlockReads: map<ReqId, OutstandingRead>,

        inMemoryJournalFrozen: seq<JournalEntry>,
        inMemoryJournal: seq<JournalEntry>,
        outstandingJournalWrites: set<ReqId>,
        writtenJournalLen: int,

        replayJournal: seq<JournalEntry>,

        superblock: Superblock,
        whichSuperblock: int,
        newSuperblock: Option<Superblock>,

        cache: map<Reference, Node>,

        syncReqs: map<uint64, SyncReqStatus>
      )

    | LoadingOther(
        superblock: Superblock,
        whichSuperblock: int,

        indirectionTableRead: Option<ReqId>,
        journalFrontRead: Option<ReqId>,
        journalBackRead: Option<ReqId>,

        indirectionTable: Option<IndirectionTable>,
        journalFront: Option<JournalRange>,
        journalBack: Option<JournalRange>,

        syncReqs: map<uint64, SyncReqStatus>
      )

    | LoadingSuperblock(
        outstandingSuperblock1Read: Option<ReqId>,
        outstandingSuperblock2Read: Option<ReqId>,
        superblock1: SuperblockReadResult,
        superblock2: SuperblockReadResult,

        syncReqs: map<uint64, SyncReqStatus>
      )

  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralIndirectionTable.graph
  }

  predicate GraphClosed(graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in graph ::
      forall succ | succ in graph[ref] ::
        succ in graph
  }

  // WF IndirectionTable which must have all LBAs filled in
  predicate WFCompleteIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall loc | loc in indirectionTable.locs.Values :: ValidNodeLocation(loc))
    && indirectionTable.graph.Keys == indirectionTable.locs.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  // WF IndirectionTable which might not have all LBAs filled in
  predicate WFIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall loc | loc in indirectionTable.locs.Values :: ValidNodeLocation(loc))
    && indirectionTable.locs.Keys <= indirectionTable.graph.Keys
    // TODO this may be necessary for an assume in Marshalling, but may be solved by the weights branch
    // && IndirectionTableGraphHasUniqueRefsInAdjList(indirectionTable.graph)
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  predicate ValidAllocation(s: Variables, loc: Location)
  requires s.Ready?
  {
    && (forall ref | ref in s.persistentIndirectionTable.locs ::
        s.persistentIndirectionTable.locs[ref].addr != loc.addr)
    && (forall ref | ref in s.ephemeralIndirectionTable.locs ::
        s.ephemeralIndirectionTable.locs[ref].addr != loc.addr)
    && (s.frozenIndirectionTable.Some? ==>
        forall ref | ref in s.frozenIndirectionTable.value.locs ::
        s.frozenIndirectionTable.value.locs[ref].addr != loc.addr)
    && (forall id | id in s.outstandingBlockWrites ::
        s.outstandingBlockWrites[id].loc.addr != loc.addr)
  }

  function IncrementSuperblockCounter(i: uint64) : uint64
  {
    if i == 0xffff_ffff_ffff_ffff then
      0
    else
      i + 1
  }

  predicate increments1(i: uint64, j: uint64) {
    j == IncrementSuperblockCounter(i)
  }

  function SelectSuperblockIndex(
      superblock1: Superblock, 
      superblock2: Superblock) : int
  {
    if increments1(superblock1.counter, superblock2.counter) then
      1
    else
      0
  }

  function SelectSuperblock(
      superblock1: Superblock, 
      superblock2: Superblock) : Superblock
  {
    if SelectSuperblockIndex(superblock1, superblock2) == 1 then
      superblock2
    else
      superblock1
  }

  function syncReqs3to2(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State3 then State2 else syncReqs[id])
  }

  function syncReqs2to1(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State2 then State1 else syncReqs[id])
  }

  // Journal is written in a circular array, so to load the log
  // we may have to read back two chunks.

  function JournalFrontLocationOfSuperblock(superblock: Superblock) : Option<Location>
  requires superblock.journalStart < NumJournalBlocks()
  {
    JournalFrontLocation(superblock.journalStart, superblock.journalLen)
  }

  function JournalBackLocationOfSuperblock(superblock: Superblock) : Option<Location>
  requires superblock.journalStart < NumJournalBlocks()
  requires superblock.journalLen <= NumJournalBlocks()
  {
    JournalBackLocation(superblock.journalStart, superblock.journalLen)
  }

  predicate WFSuperblock(superblock: Superblock)
  {
    && superblock.journalStart < NumJournalBlocks()
    && superblock.journalLen <= NumJournalBlocks()
    && ValidIndirectionTableLocation(superblock.indirectionTableLoc)
  }

  datatype Step =
    | WriteBackReqStep(ref: Reference)
    | WriteBackRespStep
    | WriteBackIndirectionTableReqStep
    | WriteBackIndirectionTableRespStep
    | WriteBackJournalReqStep(jr: JournalRange)
    | WriteBackJournalReqWraparoundStep(jr: JournalRange)
    | WriteBackJournalRespStep
    | WriteBackSuperblockReq_Basic_Step
    | WriteBackSuperblockReq_UpdateIndirectionTable_Step
    | WriteBackSuperblockRespStep
    | UnallocStep(ref: Reference)
    | PageInReqStep(ref: Reference)
    | PageInRespStep
    | PageInIndirectionTableReqStep
    | PageInIndirectionTableRespStep
    | PageInJournalReqStep(which: int)
    | PageInJournalRespStep(which: int)
    | PageInSuperblockReqStep(which: int)
    | PageInSuperblockRespStep(which: int)
    | FinishLoadingSuperblockPhaseStep
    | FinishLoadingOtherPhaseStep
    | EvictStep(ref: Reference)
    | FreezeStep
    | PushSyncReqStep(id: uint64)
    | PopSyncReqStep(id: uint64)
    | NoOpStep
    | TransactionStep(ops: seq<Op>)

  function assignRefToLocation(indirectionTable: IndirectionTable, ref: Reference, loc: Location) : IndirectionTable
  {
    IndirectionTable(
      if ref in indirectionTable.graph && ref !in indirectionTable.locs then indirectionTable.locs[ref := loc] else indirectionTable.locs,
      indirectionTable.graph
    )
  }

  predicate OutstandingBlockReadsDoesNotHaveRef(outstandingBlockReads: map<ReqId, OutstandingRead>, ref: Reference)
  {
    forall reqId | reqId in outstandingBlockReads :: outstandingBlockReads[reqId].ref != ref
  }

  predicate WriteBackReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.ReqWriteOp?
    && s.Ready?
    && ref in s.cache
    && ValidNodeLocation(dop.reqWrite.loc)
    && dop.reqWrite.sector == SectorNode(s.cache[ref])
    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    // TODO I don't think we really need this.
    && s.outstandingIndirectionTableWrite.None?

    && ValidAllocation(s, dop.reqWrite.loc)

    && s'.ephemeralIndirectionTable == assignRefToLocation(s.ephemeralIndirectionTable, ref, dop.reqWrite.loc)

    && (s.frozenIndirectionTable.Some? ==> (
      s'.frozenIndirectionTable == Some(assignRefToLocation(s.frozenIndirectionTable.value, ref, dop.reqWrite.loc)))
    )
    && (s.frozenIndirectionTable.None? ==> s'.frozenIndirectionTable.None?)

    && s'.cache == s.cache
    && s'.outstandingBlockWrites == s.outstandingBlockWrites[dop.id := OutstandingWrite(ref, dop.reqWrite.loc)]
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.syncReqs == s.syncReqs
    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.frozenJournalPosition == s.frozenJournalPosition
    && s'.superblockWrite == s.superblockWrite
    && s'.inMemoryJournal == s.inMemoryJournal
    && s'.inMemoryJournalFrozen == s.inMemoryJournalFrozen
    && s'.outstandingJournalWrites == s.outstandingJournalWrites
    && s'.writtenJournalLen == s.writtenJournalLen
    && s'.replayJournal == s.replayJournal
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == s.newSuperblock
  }

  predicate WriteBackResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteOp?
    && s.Ready?
    && dop.id in s.outstandingBlockWrites
    && s' == s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, dop.id))
  }

  predicate WriteBackIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteOp?
    && s.Ready?
    && s.frozenIndirectionTable.Some?
    && ValidIndirectionTableLocation(dop.reqWrite.loc)
    && s.newSuperblock.None?
    && !overlap(
          dop.reqWrite.loc,
          s.superblock.indirectionTableLoc)
    && dop.reqWrite.sector == SectorIndirectionTable(s.frozenIndirectionTable.value)
    && s.frozenIndirectionTable.value.graph.Keys <= s.frozenIndirectionTable.value.locs.Keys
    && s.outstandingIndirectionTableWrite.None?
    //&& s.outstandingBlockWrites == map[]
    && s' == s
      .(outstandingIndirectionTableWrite := Some(dop.id))
      .(frozenIndirectionTableLoc := Some(dop.reqWrite.loc))
  }

  predicate WriteBackIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteOp?
    && s.Ready?
    && s.outstandingIndirectionTableWrite == Some(dop.id)
    && s' == s.(outstandingIndirectionTableWrite := None)
  }

  predicate WriteBackJournalReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, jr: JournalRange)
  {
    && s.Ready?

    && var j :=
        if s.inMemoryJournalFrozen == [] then
          s.inMemoryJournal
        else
          s.inMemoryJournalFrozen;

    && JournalRangeParses(jr, j)
    && JournalRangeLen(jr) + s.writtenJournalLen <= NumJournalBlocks() as int
    && JournalRangeLen(jr) > 0
    && s.newSuperblock.None?
    && s.superblock.journalStart < NumJournalBlocks()
    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && var startPos := JournalPosAdd(
        s.superblock.journalStart as int,
        s.writtenJournalLen);

    && var writtenJournalLen' :=
        s.writtenJournalLen + JournalRangeLen(jr);

    && var frozenJournalPosition' := 
        if s.inMemoryJournalFrozen == [] then
          s.frozenJournalPosition
        else
          writtenJournalLen';

    && var inMemoryJournal' :=
        if s.inMemoryJournalFrozen == [] then
          []
        else
          s.inMemoryJournal;

    && var inMemoryJournalFrozen' := [];

    && JournalRangeLen(jr) + startPos <= NumJournalBlocks() as int
    && dop.ReqWriteOp?
    && dop.reqWrite.sector == SectorJournal(jr)
    && dop.reqWrite.loc == JournalRangeLocation(startPos as uint64, JournalRangeLen(jr) as uint64)
    && s' == s
        .(outstandingJournalWrites := s.outstandingJournalWrites + {dop.id})
        .(writtenJournalLen := writtenJournalLen')
        .(frozenJournalPosition := frozenJournalPosition')
        .(inMemoryJournal := inMemoryJournal')
        .(inMemoryJournalFrozen := inMemoryJournalFrozen')
  }

  predicate WriteBackJournalReqWraparound(k: Constants, s: Variables, s': Variables, dop: DiskOp, jr: JournalRange)
  {
    && s.Ready?

    && var j :=
        if s.inMemoryJournalFrozen == [] then
          s.inMemoryJournal
        else
          s.inMemoryJournalFrozen;

    && JournalRangeParses(jr, j)
    && JournalRangeLen(jr) + s.writtenJournalLen <= NumJournalBlocks() as int
    && JournalRangeLen(jr) > 0
    && s.newSuperblock.None?
    && s.superblock.journalStart < NumJournalBlocks()
    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && var startPos := JournalPosAdd(
        s.superblock.journalStart as int,
        s.writtenJournalLen);

    && var writtenJournalLen' :=
        s.writtenJournalLen + JournalRangeLen(jr);

    && var frozenJournalPosition' := 
        if s.inMemoryJournalFrozen == [] then
          s.frozenJournalPosition
        else
          writtenJournalLen';

    && var inMemoryJournal' :=
        if s.inMemoryJournalFrozen == [] then
          []
        else
          s.inMemoryJournal;

    && var inMemoryJournalFrozen' := [];

    && JournalRangeLen(jr) + startPos > NumJournalBlocks() as int
    && dop.ReqWrite2Op?
    && dop.reqWrite1.sector == SectorJournal(JournalRangePrefix(jr, NumJournalBlocks() as int - startPos))
    && dop.reqWrite1.loc == JournalRangeLocation(startPos as uint64, NumJournalBlocks() - startPos as uint64)
    && dop.reqWrite2.sector == SectorJournal(JournalRangeSuffix(jr, NumJournalBlocks() as int - startPos))
    && dop.reqWrite2.loc == JournalRangeLocation(0, JournalRangeLen(jr) as uint64 - (NumJournalBlocks() - startPos as uint64))
    && s' == s
        .(outstandingJournalWrites := s.outstandingJournalWrites + {dop.id1, dop.id2})
        .(writtenJournalLen := writtenJournalLen')
        .(frozenJournalPosition := frozenJournalPosition')
        .(inMemoryJournal := inMemoryJournal')
        .(inMemoryJournalFrozen := inMemoryJournalFrozen')
  }

  predicate WriteBackJournalResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.RespWriteOp?
    && dop.id in s.outstandingJournalWrites
    && s' == s
       .(outstandingJournalWrites := s.outstandingJournalWrites - {dop.id})
  }

  predicate WriteBackSuperblockReq_Basic(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.ReqWriteOp?
    && s.superblockWrite.None?
    && s.outstandingJournalWrites == {}
    && dop.reqWrite.loc == (if s.whichSuperblock == 0 then
        Superblock2Location() else Superblock1Location())
    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && var newSuperblock := Superblock(
      IncrementSuperblockCounter(s.superblock.counter),
      s.superblock.journalStart,
      s.writtenJournalLen as uint64,
      s.superblock.indirectionTableLoc
    );
    && dop.reqWrite.sector == SectorSuperblock(newSuperblock)
    && s' == s
        .(newSuperblock := Some(newSuperblock))
        .(superblockWrite := Some(dop.id))
        .(syncReqs := syncReqs3to2(s.syncReqs))
  }

  predicate WriteBackSuperblockReq_UpdateIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.ReqWriteOp?
    && s.frozenIndirectionTableLoc.Some?
    && s.outstandingIndirectionTableWrite.None?
    && s.superblockWrite.None?
    && s.outstandingBlockWrites == map[]
    && s.outstandingJournalWrites == {}
    && dop.reqWrite.loc == (if s.whichSuperblock == 0 then
        Superblock2Location() else Superblock1Location())
    && 0 <= s.superblock.journalStart < NumJournalBlocks()
    && 0 <= s.frozenJournalPosition
         <= s.writtenJournalLen
         <= NumJournalBlocks() as int
    && s.inMemoryJournalFrozen == []
    && var newSuperblock := Superblock(
      IncrementSuperblockCounter(s.superblock.counter),
      JournalPosAdd(
          s.superblock.journalStart as int,
          s.frozenJournalPosition) as uint64,
      (s.writtenJournalLen - s.frozenJournalPosition) as uint64,
      s.frozenIndirectionTableLoc.value
    );
    && dop.reqWrite.sector == SectorSuperblock(newSuperblock)
    && s' == s
        .(newSuperblock := Some(newSuperblock))
        .(superblockWrite := Some(dop.id))
        .(syncReqs := syncReqs3to2(s.syncReqs))
  }

  predicate WriteBackSuperblockResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.RespWriteOp?
    && Some(dop.id) == s.superblockWrite
    && s.newSuperblock.Some?
    && s'.Ready?
    && var isUpdatingTable :=
        (s.newSuperblock.value.indirectionTableLoc != s.superblock.indirectionTableLoc);
    && (isUpdatingTable ==> s.frozenIndirectionTable.Some?)
    && s' == s.(superblockWrite := None)
        .(superblock := s.newSuperblock.value)
        .(newSuperblock := None)
        .(whichSuperblock := if s.whichSuperblock == 0 then 1 else 0)
        .(syncReqs := syncReqs2to1(s.syncReqs))
        .(writtenJournalLen :=
            if !isUpdatingTable then s.writtenJournalLen else
                s.writtenJournalLen - s.frozenJournalPosition)
        .(frozenJournalPosition :=
            if !isUpdatingTable then s.frozenJournalPosition else 0)
        .(frozenIndirectionTableLoc :=
            if !isUpdatingTable then s.frozenIndirectionTableLoc else None)
        .(frozenIndirectionTable :=
            if !isUpdatingTable then s.frozenIndirectionTable else None)
        .(persistentIndirectionTable :=
            if !isUpdatingTable
              then s.persistentIndirectionTable else s.frozenIndirectionTable.value)
  }

  predicate NoPredecessors(graph: map<Reference, seq<Reference>>, ref: Reference)
  {
    forall r | r in graph :: ref !in graph[r]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.NoDiskOp?
    && s.Ready?

    && IsAllocated(s, ref)

    // We can only dealloc this if nothing is pointing to it.
    && ref != G.Root()
    && NoPredecessors(s.ephemeralIndirectionTable.graph, ref)

    && (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs)

    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.locs == MapRemove(s.ephemeralIndirectionTable.locs, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && s'.ephemeralIndirectionTable.graph == MapRemove(s.ephemeralIndirectionTable.graph, {ref})

    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.outstandingBlockWrites == s.outstandingBlockWrites
    && OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref)
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.frozenIndirectionTable == s.frozenIndirectionTable
    && s'.syncReqs == s.syncReqs

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.frozenJournalPosition == s.frozenJournalPosition
    && s'.superblockWrite == s.superblockWrite
    && s'.inMemoryJournalFrozen == s.inMemoryJournalFrozen
    && s'.outstandingJournalWrites == s.outstandingJournalWrites
    && s'.writtenJournalLen == s.writtenJournalLen
    && s'.replayJournal == s.replayJournal
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == s.newSuperblock
  }

  predicate PageInReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.ReqReadOp?
    && s.Ready?
    && IsAllocated(s, ref)
    && ref in s.ephemeralIndirectionTable.locs
    && ref !in s.cache
    && s.ephemeralIndirectionTable.locs[ref] == dop.reqRead.loc
    && OutstandingRead(ref) !in s.outstandingBlockReads.Values
    && s' == s.(outstandingBlockReads := s.outstandingBlockReads[dop.id := OutstandingRead(ref)])
  }

  predicate PageInResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadOp?
    && s.Ready?
    && dop.id in s.outstandingBlockReads
    && var ref := s.outstandingBlockReads[dop.id].ref;
    && ref !in s.cache
    && dop.respRead.sector.Some?
    && dop.respRead.sector.value.SectorNode?
    && var block := dop.respRead.sector.value.block;
    && ref in s.ephemeralIndirectionTable.graph
    && (iset r | r in s.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)
    && s' == s.(cache := s.cache[ref := block])
              .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, dop.id))
  }

  predicate PageInIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadOp?
    && s.LoadingOther?

    && s.indirectionTableRead.None?
    && s.indirectionTable.None?
    && dop.reqRead.loc == s.superblock.indirectionTableLoc
    && s' == s.(indirectionTableRead := Some(dop.id))
  }

  predicate PageInIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadOp?
    && s.LoadingOther?
    && dop.respRead.sector.Some?
    && dop.respRead.sector.value.SectorIndirectionTable?
    && WFCompleteIndirectionTable(dop.respRead.sector.value.indirectionTable)
    && AllLocationsForDifferentRefsDontOverlap(dop.respRead.sector.value.indirectionTable)

    && s.indirectionTableRead == Some(dop.id)
    && s' == s
        .(indirectionTableRead := None)
        .(indirectionTable := Some(dop.respRead.sector.value.indirectionTable))
  }

  predicate PageInJournalReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
  {
    && dop.ReqReadOp?
    && s.LoadingOther?
    && (which == 0 || which == 1)
    && s.superblock.journalStart < NumJournalBlocks()
    && s.superblock.journalLen <= NumJournalBlocks()
    && (which == 0 ==>
      && JournalFrontLocationOfSuperblock(s.superblock).Some?
      && dop.reqRead.loc == JournalFrontLocationOfSuperblock(s.superblock).value
      && s.journalFrontRead.None?
      && s.journalFront.None?
      && s' == s.(journalFrontRead := Some(dop.id))
    )
    && (which == 1 ==>
      && JournalBackLocationOfSuperblock(s.superblock).Some?
      && dop.reqRead.loc == JournalBackLocationOfSuperblock(s.superblock).value
      && s.journalBackRead.None?
      && s.journalBack.None?
      && s' == s.(journalBackRead := Some(dop.id))
    )
  }

  predicate PageInJournalResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
  {
    && dop.RespReadOp?
    && s.LoadingOther?
    && dop.respRead.sector.Some?
    && dop.respRead.sector.value.SectorJournal?
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.journalFrontRead == Some(dop.id)
      && s' == s
          .(journalFrontRead := None)
          .(journalFront := Some(dop.respRead.sector.value.journal))
    )
    && (which == 1 ==>
      && s.journalBackRead == Some(dop.id)
      && s' == s
          .(journalBackRead := None)
          .(journalBack := Some(dop.respRead.sector.value.journal))
    )
  }

  predicate PageInSuperblockReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
  {
    && dop.ReqReadOp?
    && s.LoadingSuperblock?
    && (which == 0 || which == 1)
    && (which == 0 ==> 
      && dop.reqRead.loc == Superblock1Location()
      && s.outstandingSuperblock1Read.None?
      && s.superblock1.SuperblockUnfinished?
      && s' == s.(outstandingSuperblock1Read := Some(dop.id))
    )
    && (which == 1 ==> 
      && dop.reqRead.loc == Superblock2Location()
      && s.outstandingSuperblock2Read.None?
      && s.superblock2.SuperblockUnfinished?
      && s' == s.(outstandingSuperblock2Read := Some(dop.id))
    )
  }

  predicate PageInSuperblockResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
  {
    && dop.RespReadOp?
    && s.LoadingSuperblock?
    && var sup := (
        if dop.respRead.sector.Some? &&
            dop.respRead.sector.value.SectorSuperblock? &&
            WFSuperblock(dop.respRead.sector.value.superblock) then
          SuperblockSuccess(dop.respRead.sector.value.superblock)
        else
          SuperblockCorruption
    );
    && (which == 0 || which == 1)
    && (which == 0 ==> 
      && s.outstandingSuperblock1Read == Some(dop.id)
      && s' == s
          .(outstandingSuperblock1Read := None)
          .(superblock1 := sup)
    )
    && (which == 1 ==> 
      && s.outstandingSuperblock2Read == Some(dop.id)
      && s' == s
          .(outstandingSuperblock2Read := None)
          .(superblock2 := sup)
    )
  }

  predicate FinishLoadingSuperblockPhase(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s.LoadingSuperblock?
    // TODO account for case where one superblock or the other is corrupt
    && s.superblock1.SuperblockSuccess?
    && s.superblock2.SuperblockSuccess?
    && (s.superblock1.SuperblockSuccess?
        || s.superblock2.SuperblockSuccess?)
    && (s.superblock1.SuperblockSuccess? && s.superblock2.SuperblockSuccess? ==>
      s' == LoadingOther(
        SelectSuperblock(s.superblock1.value, s.superblock2.value),
        SelectSuperblockIndex(s.superblock1.value, s.superblock2.value),
        None, None, None,
        None, None, None,
        s.syncReqs)
    )
    && (s.superblock1.SuperblockCorruption? ==>
      s' == LoadingOther(
        s.superblock2.value,
        1,
        None, None, None,
        None, None, None,
        s.syncReqs)
    )
    && (s.superblock2.SuperblockCorruption? ==>
      s' == LoadingOther(
        s.superblock1.value,
        0,
        None, None, None,
        None, None, None,
        s.syncReqs)
    )
  }

  predicate FinishLoadingOtherPhase(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s.LoadingOther?
    && s.indirectionTable.Some?
    && s.superblock.journalStart < NumJournalBlocks()
    && s.superblock.journalLen <= NumJournalBlocks()
    && (JournalFrontLocationOfSuperblock(s.superblock).Some? ==> s.journalFront.Some?)
    && (JournalBackLocationOfSuperblock(s.superblock).Some? ==> s.journalBack.Some?)

    && var fullRange := (
        if JournalBackLocationOfSuperblock(s.superblock).Some? then
          JournalRangeConcat(s.journalFront.value, s.journalBack.value)
        else if JournalFrontLocationOfSuperblock(s.superblock).Some? then
          s.journalFront.value
        else
          JournalRangeEmpty()
    );

    && s'.Ready?
    && s'.persistentIndirectionTable == s.indirectionTable.value
    && s'.frozenIndirectionTable == None
    && s'.ephemeralIndirectionTable == s.indirectionTable.value
    && s'.outstandingIndirectionTableWrite == None
    && s'.frozenIndirectionTableLoc == None
    && s'.superblockWrite == None
    && s'.outstandingBlockWrites == map[]
    && s'.outstandingBlockReads == map[]
    && s'.inMemoryJournalFrozen == []
    && s'.inMemoryJournal == []
    && s'.outstandingJournalWrites == {}
    && s'.writtenJournalLen == s.superblock.journalLen as int
    && JournalRangeParses(fullRange, s'.replayJournal)
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == None
    && s'.cache == map[]
    && s'.syncReqs == s.syncReqs
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?
    && ref in s.cache
    && (ref in s.ephemeralIndirectionTable.graph ==>
      && ref in s.ephemeralIndirectionTable.locs
      && OutstandingWrite(ref, s.ephemeralIndirectionTable.locs[ref]) !in s.outstandingBlockWrites.Values
    )
    && (s.frozenIndirectionTable.Some? ==>
        ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs)
    && s' == s.(cache := MapRemove(s.cache, {ref}))
  }

  predicate Freeze(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.NoDiskOp?
    && s.outstandingIndirectionTableWrite.None?
    && s.superblockWrite.None?
    && s' ==
        s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
         .(frozenIndirectionTableLoc := None)
         .(inMemoryJournalFrozen := s.inMemoryJournalFrozen + s.inMemoryJournal)
         .(inMemoryJournal := [])
         .(frozenJournalPosition := s.writtenJournalLen)
  }

  predicate PushSyncReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
  {
    && dop.NoDiskOp?
    && id !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[id := State3])
  }

  predicate PopSyncReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
  {
    && dop.NoDiskOp?
    && id in s.syncReqs
    && s.syncReqs[id] == State1
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, id))
  }

  predicate NoOp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && (dop.RespReadOp? || dop.NoDiskOp? || (
      && dop.RespWriteOp?
      && !(
        || (s.Ready? && s.outstandingIndirectionTableWrite == Some(dop.id))
        || (s.Ready? && dop.id in s.outstandingBlockWrites)
        || (s.Ready? && dop.id in s.outstandingJournalWrites)
        || (s.Ready? && s.superblockWrite == Some(dop.id))
      )
    ))
    && s' == s
  }

  ////// Write/Alloc Ops

  predicate BlockPointsToValidReferences(block: Node, graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in G.Successors(block) :: ref in graph
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && ref in s.cache // probably not necessary?
    && ref in s.ephemeralIndirectionTable.graph
    && s'.Ready?
    && s'.cache == s.cache[ref := block]
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    && s'.ephemeralIndirectionTable.locs == MapRemove(s.ephemeralIndirectionTable.locs, {ref})

    && BlockPointsToValidReferences(block, s.ephemeralIndirectionTable.graph)

    && (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs)
    && ref in s'.ephemeralIndirectionTable.graph
    && s'.ephemeralIndirectionTable.graph == s.ephemeralIndirectionTable.graph[ref := s'.ephemeralIndirectionTable.graph[ref]]
    && (iset r | r in s'.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)

    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.outstandingBlockWrites == s.outstandingBlockWrites
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.frozenIndirectionTable == s.frozenIndirectionTable
    && s'.syncReqs == s.syncReqs

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.frozenJournalPosition == s.frozenJournalPosition
    && s'.superblockWrite == s.superblockWrite
    && s'.inMemoryJournal == s.inMemoryJournal
    && s'.inMemoryJournalFrozen == s.inMemoryJournalFrozen
    && s'.outstandingJournalWrites == s.outstandingJournalWrites
    && s'.writtenJournalLen == s.writtenJournalLen
    && s'.replayJournal == s.replayJournal
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == s.newSuperblock
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && ref !in s.cache
    && !IsAllocated(s, ref)
    && s'.Ready?
    && s'.cache == s.cache[ref := block]
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    && s'.ephemeralIndirectionTable.locs == s.ephemeralIndirectionTable.locs

    && BlockPointsToValidReferences(block, s.ephemeralIndirectionTable.graph)

    && ref in s'.ephemeralIndirectionTable.graph
    && s'.ephemeralIndirectionTable.graph == s.ephemeralIndirectionTable.graph[ref := s'.ephemeralIndirectionTable.graph[ref]]
    && (iset r | r in s'.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)

    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.outstandingBlockWrites == s.outstandingBlockWrites
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.frozenIndirectionTable == s.frozenIndirectionTable
    && s'.syncReqs == s.syncReqs

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.frozenJournalPosition == s.frozenJournalPosition
    && s'.superblockWrite == s.superblockWrite
    && s'.inMemoryJournal == s.inMemoryJournal
    && s'.inMemoryJournalFrozen == s.inMemoryJournalFrozen
    && s'.outstandingJournalWrites == s.outstandingJournalWrites
    && s'.writtenJournalLen == s.writtenJournalLen
    && s'.replayJournal == s.replayJournal
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == s.newSuperblock
  }

  predicate ReadStep(k: Constants, s: Variables, op: ReadOp)
  {
    s.Ready? && op.ref in s.ephemeralIndirectionTable.graph && MapsTo(s.cache, op.ref, op.node)
  }

  predicate OpStep(k: Constants, s: Variables, s': Variables, op: Op)
  {
    match op {
      case WriteOp(ref, block) => Dirty(k, s, s', ref, block)
      case AllocOp(ref, block) => Alloc(k, s, s', ref, block)
    }
  }

  predicate Transaction(k: Constants, s: Variables, s': Variables, dop: DiskOp, ops: seq<Op>)
  {
    && dop.NoDiskOp?
    && OpTransaction(k, s, s', ops)
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == LoadingSuperblock(None, None, SuperblockUnfinished, SuperblockUnfinished, map[])
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteBackReqStep(ref) => WriteBackReq(k, s, s', dop, ref)
      case WriteBackRespStep => WriteBackResp(k, s, s', dop)
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReq(k, s, s', dop)
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableResp(k, s, s', dop)
      case WriteBackJournalReqStep(jr: JournalRange) => WriteBackJournalReq(k, s, s', dop, jr)
      case WriteBackJournalReqWraparoundStep(jr: JournalRange) => WriteBackJournalReqWraparound(k, s, s', dop, jr)
      case WriteBackJournalRespStep => WriteBackJournalResp(k, s, s', dop)
      case WriteBackSuperblockReq_Basic_Step => WriteBackSuperblockReq_Basic(k, s, s', dop)
      case WriteBackSuperblockReq_UpdateIndirectionTable_Step => WriteBackSuperblockReq_UpdateIndirectionTable(k, s, s', dop)
      case WriteBackSuperblockRespStep => WriteBackSuperblockResp(k, s, s', dop)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, ref)
      case PageInReqStep(ref) => PageInReq(k, s, s', dop, ref)
      case PageInRespStep => PageInResp(k, s, s', dop)
      case PageInIndirectionTableReqStep => PageInIndirectionTableReq(k, s, s', dop)
      case PageInIndirectionTableRespStep => PageInIndirectionTableResp(k, s, s', dop)
      case PageInJournalReqStep(which: int) => PageInJournalReq(k, s, s', dop, which)
      case PageInJournalRespStep(which: int) => PageInJournalResp(k, s, s', dop, which)
      case PageInSuperblockReqStep(which: int) => PageInSuperblockReq(k, s, s', dop, which)
      case PageInSuperblockRespStep(which: int) => PageInSuperblockResp(k, s, s', dop, which)
      case FinishLoadingSuperblockPhaseStep => FinishLoadingSuperblockPhase(k, s, s', dop)
      case FinishLoadingOtherPhaseStep => FinishLoadingOtherPhase(k, s, s', dop)
      case EvictStep(ref) => Evict(k, s, s', dop, ref)
      case FreezeStep => Freeze(k, s, s', dop)
      case PushSyncReqStep(id: uint64) => PushSyncReq(k, s, s', dop, id)
      case PopSyncReqStep(id: uint64) => PopSyncReq(k, s, s', dop, id)
      case NoOpStep => NoOp(k, s, s', dop)
      case TransactionStep(ops) => Transaction(k, s, s', dop, ops)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step: Step :: NextStep(k, s, s', dop, step)
  }

  predicate CacheConsistentWithSuccessors(cache: map<Reference, Node>, graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in cache && ref in graph :: (iset r | r in graph[ref]) == G.Successors(cache[ref])
  }

  predicate IndirectionTableCacheConsistent(indirectionTable: IndirectionTable, cache: map<Reference, Node>)
  {
    && indirectionTable.graph.Keys <= cache.Keys + indirectionTable.locs.Keys
  }

  predicate EphemeralTableEntriesInCacheOrNotBeingWritten(k: Constants, s: Variables)
  requires s.Ready?
  requires IndirectionTableCacheConsistent(s.ephemeralIndirectionTable, s.cache)
  {
    forall ref | ref in s.ephemeralIndirectionTable.graph ::
      ref !in s.cache ==> forall id | id in s.outstandingBlockWrites ::
        s.outstandingBlockWrites[id].ref != ref || s.outstandingBlockWrites[id].loc.addr != s.ephemeralIndirectionTable.locs[ref].addr
  }

  predicate OutstandingReadRefsUnique(outstandingBlockReads: map<ReqId, OutstandingRead>)
  {
    forall id1, id2 | id1 in outstandingBlockReads && id2 in outstandingBlockReads && outstandingBlockReads[id1] == outstandingBlockReads[id2] ::
      id1 == id2
  }

  predicate OverlappingImpliesEq(loc1: Location, loc2: Location) {
    loc1.addr == loc2.addr ==> loc1 == loc2
  }

  predicate OverlappingWritesEqForIndirectionTable(k: Constants, s: Variables, indirectionTable: IndirectionTable)
  requires s.Ready?
  {
    forall ref | ref in indirectionTable.locs ::
      forall id | id in s.outstandingBlockWrites ::
        OverlappingImpliesEq(indirectionTable.locs[ref], s.outstandingBlockWrites[id].loc)
  }

  predicate LocationsForDifferentRefsDontOverlap(indirectionTable: IndirectionTable,
      r1: Reference, r2: Reference)
  requires r1 in indirectionTable.locs
  requires r2 in indirectionTable.locs
  {
    indirectionTable.locs[r1].addr == indirectionTable.locs[r2].addr ==> r1 == r2
  }

  predicate AllLocationsForDifferentRefsDontOverlap(indirectionTable: IndirectionTable)
  {
    forall r1, r2 | r1 in indirectionTable.locs && r2 in indirectionTable.locs ::
        LocationsForDifferentRefsDontOverlap(indirectionTable, r1, r2)
  }

  predicate OutstandingWriteValidNodeLocation(outstandingBlockWrites: map<ReqId, OutstandingWrite>)
  {
    forall id | id in outstandingBlockWrites ::
      ValidNodeLocation(outstandingBlockWrites[id].loc)
  }

  predicate OutstandingBlockWritesDontOverlap(outstandingBlockWrites: map<ReqId, OutstandingWrite>, id1: ReqId, id2: ReqId)
  requires id1 in outstandingBlockWrites
  requires id2 in outstandingBlockWrites
  {
    outstandingBlockWrites[id1].loc.addr == outstandingBlockWrites[id2].loc.addr ==> id1 == id2
  }

  predicate AllOutstandingBlockWritesDontOverlap(outstandingBlockWrites: map<ReqId, OutstandingWrite>)
  {
    forall id1, id2 | id1 in outstandingBlockWrites && id2 in outstandingBlockWrites ::
        OutstandingBlockWritesDontOverlap(outstandingBlockWrites, id1, id2)
  }

  predicate InvLoadingSuperblock(k: Constants, s: Variables)
  requires s.LoadingSuperblock?
  {
    && (s.superblock1.SuperblockSuccess? ==>
        && s.outstandingSuperblock1Read.None?
        && WFSuperblock(s.superblock1.value)
       )
    && (s.superblock2.SuperblockSuccess? ==>
        && s.outstandingSuperblock2Read.None?
        && WFSuperblock(s.superblock2.value)
       )
    && (s.superblock1.SuperblockCorruption? ==>
        && s.outstandingSuperblock1Read.None?
        )
    && (s.superblock2.SuperblockCorruption? ==>
        && s.outstandingSuperblock2Read.None?
        )
  }

  predicate InvLoadingOther(k: Constants, s: Variables)
  requires s.LoadingOther?
  {
    && WFSuperblock(s.superblock)
    && (s.indirectionTable.Some? ==>
      && s.indirectionTableRead.None?
      && WFCompleteIndirectionTable(s.indirectionTable.value)
      && AllLocationsForDifferentRefsDontOverlap(s.indirectionTable.value)
    )
    && (s.whichSuperblock == 0 || s.whichSuperblock == 1)
  }

  predicate InvReady(k: Constants, s: Variables)
  requires s.Ready?
  {
    && WFCompleteIndirectionTable(s.persistentIndirectionTable)

    && WFIndirectionTable(s.ephemeralIndirectionTable)
    && IndirectionTableCacheConsistent(s.ephemeralIndirectionTable, s.cache)
    && CacheConsistentWithSuccessors(s.cache, s.ephemeralIndirectionTable.graph)
    && EphemeralTableEntriesInCacheOrNotBeingWritten(k, s)
    && OutstandingReadRefsUnique(s.outstandingBlockReads)
    && OverlappingWritesEqForIndirectionTable(k, s, s.ephemeralIndirectionTable)
    && OverlappingWritesEqForIndirectionTable(k, s, s.persistentIndirectionTable)
    && OutstandingWriteValidNodeLocation(s.outstandingBlockWrites)
    && AllOutstandingBlockWritesDontOverlap(s.outstandingBlockWrites)
    && (s.superblockWrite.Some? <==> s.newSuperblock.Some?)
    && (s.frozenIndirectionTableLoc.Some? ==> s.frozenIndirectionTable.Some?)

    && (s.whichSuperblock == 0 || s.whichSuperblock == 1)

    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && 0 <= s.superblock.journalLen as int <= s.writtenJournalLen

    && (s.frozenIndirectionTable.Some? ==> (
      && 0 <= s.frozenJournalPosition <= NumJournalBlocks() as int
      && s.superblock.journalLen as int <= s.writtenJournalLen
      && s.frozenJournalPosition <= s.writtenJournalLen
    ))

    // This isn't necessary for the other invariants in this file,
    // but it is useful for the implementation.
    && AllLocationsForDifferentRefsDontOverlap(s.ephemeralIndirectionTable)

    && (s.frozenIndirectionTable.Some? ==> (
      && WFIndirectionTable(s.frozenIndirectionTable.value)
      && IndirectionTableCacheConsistent(s.frozenIndirectionTable.value, s.cache)
      && OverlappingWritesEqForIndirectionTable(k, s, s.frozenIndirectionTable.value)
    ))

    && (s.outstandingIndirectionTableWrite.Some? ==> (
      && s.frozenIndirectionTableLoc.Some?
    ))
    && (s.frozenIndirectionTableLoc.Some? ==> (
      && s.frozenIndirectionTable.Some?
      && WFCompleteIndirectionTable(s.frozenIndirectionTable.value)
    ))

    && WFSuperblock(s.superblock)
    && (s.newSuperblock.Some? ==>
        && s.outstandingJournalWrites == {}

        && (
          || s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc
          || (
            && s.frozenIndirectionTableLoc.Some?
            && s.newSuperblock.value.indirectionTableLoc == s.frozenIndirectionTableLoc.value
          )
        )

        && WFSuperblock(s.newSuperblock.value)
        && s.newSuperblock.value.counter ==
            IncrementSuperblockCounter(s.superblock.counter)
        && (s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc ==>
            && s.newSuperblock.value.journalStart == s.superblock.journalStart
            && s.newSuperblock.value.journalLen as int <= s.writtenJournalLen
        )
        && (s.newSuperblock.value.indirectionTableLoc != s.superblock.indirectionTableLoc ==>
            && s.inMemoryJournalFrozen == []
            && s.outstandingIndirectionTableWrite.None?
            && s.newSuperblock.value.journalStart as int == JournalPosAdd(s.superblock.journalStart as int, s.frozenJournalPosition)
            && s.frozenJournalPosition as int + s.newSuperblock.value.journalLen as int
                <= s.writtenJournalLen
        )
    )
    && (s.frozenIndirectionTableLoc.Some? ==> (
      && ValidIndirectionTableLocation(s.frozenIndirectionTableLoc.value)
      && !overlap(
          s.frozenIndirectionTableLoc.value,
          s.superblock.indirectionTableLoc)
    ))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && (s.LoadingSuperblock? ==> InvLoadingSuperblock(k, s))
    && (s.LoadingOther? ==> InvLoadingOther(k, s))
    && (s.Ready? ==> InvReady(k, s))
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma WriteBackReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires WriteBackReq(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackIndirectionTableReq(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackIndirectionTableResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackJournalReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, jr: JournalRange)
    requires Inv(k, s)
    requires WriteBackJournalReq(k, s, s', dop, jr)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackJournalReqWraparoundStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, jr: JournalRange)
    requires Inv(k, s)
    requires WriteBackJournalReqWraparound(k, s, s', dop, jr)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }


  lemma WriteBackJournalRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackJournalResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackSuperblockReq_Basic_StepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackSuperblockReq_Basic(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackSuperblockReq_UpdateIndirectionTable_StepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackSuperblockReq_UpdateIndirectionTable(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackSuperblockRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackSuperblockResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      /*if s'.frozenIndirectionTable.Some? {
        if s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc {
          assert s'.superblock.journalLen as int <= s'.frozenJournalPosition;
        } else {
          assert s'.superblock.journalLen as int <= s'.frozenJournalPosition;
        }
      }*/

      assert InvReady(k, s');
    }
  }

  lemma DirtyStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Dirty(k, s, s', ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma AllocStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Alloc(k, s, s', ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma OpPreservesInv(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires OpStep(k, s, s', op)
    ensures Inv(k, s')
  {
    match op {
      case WriteOp(ref, block) => DirtyStepPreservesInv(k, s, s', ref, block);
      case AllocOp(ref, block) => AllocStepPreservesInv(k, s, s', ref, block);
    }
  }

  lemma TransactionStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ops: seq<Op>)
    requires Inv(k, s)
    requires Transaction(k, s, s', dop, ops)
    ensures Inv(k, s')
    decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      OpPreservesInv(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := SplitTransaction(k, s, s', ops);
      TransactionStepPreservesInv(k, s, smid, dop, ops1);
      TransactionStepPreservesInv(k, smid, s', dop, ops2);
    }
  }

  lemma UnallocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires Unalloc(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires PageInReq(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires PageInResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires PageInIndirectionTableReq(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires PageInIndirectionTableResp(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInJournalReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
    requires Inv(k, s)
    requires PageInJournalReq(k, s, s', dop, which)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInJournalRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
    requires Inv(k, s)
    requires PageInJournalResp(k, s, s', dop, which)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInSuperblockReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
    requires Inv(k, s)
    requires PageInSuperblockReq(k, s, s', dop, which)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInSuperblockRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, which: int)
    requires Inv(k, s)
    requires PageInSuperblockResp(k, s, s', dop, which)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma FinishLoadingSuperblockPhaseStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires FinishLoadingSuperblockPhase(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma FinishLoadingOtherPhaseStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires FinishLoadingOtherPhase(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma EvictStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires Evict(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma FreezeStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Freeze(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PushSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires PushSyncReq(k, s, s', dop, id)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PopSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires PopSyncReq(k, s, s', dop, id)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', dop, step)
    ensures Inv(k, s')
  {
    match step {
      case WriteBackReqStep(ref) => WriteBackReqStepPreservesInv(k, s, s', dop, ref);
      case WriteBackRespStep => WriteBackRespStepPreservesInv(k, s, s', dop);
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReqStepPreservesInv(k, s, s', dop);
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableRespStepPreservesInv(k, s, s', dop);
      case WriteBackJournalReqStep(jr: JournalRange) => WriteBackJournalReqStepPreservesInv(k, s, s', dop, jr);
      case WriteBackJournalReqWraparoundStep(jr: JournalRange) => WriteBackJournalReqWraparoundStepPreservesInv(k, s, s', dop, jr);
      case WriteBackJournalRespStep => WriteBackJournalRespStepPreservesInv(k, s, s', dop);
      case WriteBackSuperblockReq_Basic_Step => WriteBackSuperblockReq_Basic_StepPreservesInv(k, s, s', dop);
      case WriteBackSuperblockReq_UpdateIndirectionTable_Step => WriteBackSuperblockReq_UpdateIndirectionTable_StepPreservesInv(k, s, s', dop);
      case WriteBackSuperblockRespStep => WriteBackSuperblockRespStepPreservesInv(k, s, s', dop);
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, ref);
      case PageInReqStep(ref) => PageInReqStepPreservesInv(k, s, s', dop, ref);
      case PageInRespStep => PageInRespStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableReqStep => PageInIndirectionTableReqStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableRespStep => PageInIndirectionTableRespStepPreservesInv(k, s, s', dop);
      case PageInJournalReqStep(which) => PageInJournalReqStepPreservesInv(k, s, s', dop, which);
      case PageInJournalRespStep(which) => PageInJournalRespStepPreservesInv(k, s, s', dop, which);
      case PageInSuperblockReqStep(which) => PageInSuperblockReqStepPreservesInv(k, s, s', dop, which);
      case PageInSuperblockRespStep(which) => PageInSuperblockRespStepPreservesInv(k, s, s', dop, which);
      case FinishLoadingSuperblockPhaseStep => FinishLoadingSuperblockPhaseStepPreservesInv(k, s, s', dop);
      case FinishLoadingOtherPhaseStep => FinishLoadingOtherPhaseStepPreservesInv(k, s, s', dop);
      case EvictStep(ref) => EvictStepPreservesInv(k, s, s', dop, ref);
      case FreezeStep => FreezeStepPreservesInv(k, s, s', dop);
      case PushSyncReqStep(id) => PushSyncReqStepPreservesInv(k, s, s', dop, id);
      case PopSyncReqStep(id) => PopSyncReqStepPreservesInv(k, s, s', dop, id);
      case NoOpStep => { }
      case TransactionStep(ops) => TransactionStepPreservesInv(k, s, s', dop, ops);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Next(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', dop, step);
    NextStepPreservesInv(k, s, s', dop, step);
  }
}
