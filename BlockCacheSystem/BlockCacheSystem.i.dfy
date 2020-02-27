include "../BlockCacheSystem/BlockCache.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
//
// Attach a BlockCache to a Disk
//

module BlockCacheSystem {
  import M = BlockCache
  import D = AsyncSectorDisk

  import opened Maps
  import opened Sequences
  import opened Options
  import opened AsyncSectorDiskModelTypes
  import opened NativeTypes
  import opened DiskLayout
  import opened SectorType

  type DiskOp = M.DiskOp

  type Constants = AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelVariables<M.Variables, D.Variables>

  type Reference = M.G.Reference
  type Node = M.G.Node
  type Op = M.Op

  predicate DiskHasSuperblock1(blocks: imap<Location, Sector>)
  {
    && Superblock1Location() in blocks
    && blocks[Superblock1Location()].SectorSuperblock?
    && M.WFSuperblock(blocks[Superblock1Location()].superblock)
  }

  function Superblock1OfDisk(blocks: imap<Location, Sector>) : (su: Superblock)
  requires DiskHasSuperblock1(blocks)
  {
    blocks[Superblock1Location()].superblock
  }

  predicate DiskHasSuperblock2(blocks: imap<Location, Sector>)
  {
    && Superblock2Location() in blocks
    && blocks[Superblock2Location()].SectorSuperblock?
    && M.WFSuperblock(blocks[Superblock2Location()].superblock)
  }

  function Superblock2OfDisk(blocks: imap<Location, Sector>) : (su: Superblock)
  requires DiskHasSuperblock2(blocks)
  {
    blocks[Superblock2Location()].superblock
  }

  predicate DiskHasSuperblock(blocks: imap<Location, Sector>)
  {
    DiskHasSuperblock1(blocks) || DiskHasSuperblock2(blocks)
  }

  function SuperblockOfDisk(blocks: imap<Location, Sector>) : (su : Superblock)
  requires DiskHasSuperblock(blocks)
  ensures M.WFSuperblock(su)
  {
    if DiskHasSuperblock1(blocks) && DiskHasSuperblock2(blocks) then
      M.SelectSuperblock(Superblock1OfDisk(blocks), Superblock2OfDisk(blocks))
    else if DiskHasSuperblock1(blocks) then
      Superblock1OfDisk(blocks)
    else
      Superblock2OfDisk(blocks)
  }

  predicate DiskHasIndirectionTable(blocks: imap<Location, Sector>)
  {
    && DiskHasSuperblock(blocks)
    && ValidIndirectionTableLocation(SuperblockOfDisk(blocks).indirectionTableLoc)
    && SuperblockOfDisk(blocks).indirectionTableLoc in blocks
    && blocks[SuperblockOfDisk(blocks).indirectionTableLoc].SectorIndirectionTable?
  }

  function IndirectionTableOfDisk(blocks: imap<Location, Sector>) : IndirectionTable
  requires DiskHasIndirectionTable(blocks)
  {
    blocks[SuperblockOfDisk(blocks).indirectionTableLoc].indirectionTable
  }

  predicate WFDisk(blocks: imap<Location, Sector>)
  {
    && DiskHasSuperblock(blocks)
    && DiskHasIndirectionTable(blocks)
    && M.WFCompleteIndirectionTable(IndirectionTableOfDisk(blocks))
  }

  predicate WFDiskWithSuperblock(blocks: imap<Location, Sector>, superblock: Superblock)
  {
    && superblock.indirectionTableLoc in blocks
    && blocks[superblock.indirectionTableLoc].SectorIndirectionTable?
    && M.WFCompleteIndirectionTable(blocks[superblock.indirectionTableLoc].indirectionTable)
  }

  predicate WFIndirectionTableRefWrtDisk(indirectionTable: IndirectionTable, blocks: imap<Location,Sector>,
      ref: Reference)
  requires ref in indirectionTable.locs
  {
    && indirectionTable.locs[ref] in blocks
    && blocks[indirectionTable.locs[ref]].SectorNode?
  }

  predicate WFIndirectionTableWrtDisk(indirectionTable: IndirectionTable, blocks: imap<Location, Sector>)
  {
    && (forall ref | ref in indirectionTable.locs :: WFIndirectionTableRefWrtDisk(indirectionTable, blocks, ref))
  }

  predicate disjointWritesFromIndirectionTable(
      outstandingBlockWrites: map<D.ReqId, M.OutstandingWrite>,
      indirectionTable: IndirectionTable)
  {
    forall req, ref |
        && req in outstandingBlockWrites
        && ref in indirectionTable.locs ::
          outstandingBlockWrites[req].loc != indirectionTable.locs[ref]
  }

  function RefMapOfDisk(
      indirectionTable: IndirectionTable,
      blocks: imap<Location, Sector>) : map<Reference, Node>
  requires WFDisk(blocks)
  requires WFIndirectionTableWrtDisk(indirectionTable, blocks)
  {
    map ref | ref in indirectionTable.locs :: blocks[indirectionTable.locs[ref]].block
  }

  function Graph(refs: set<Reference>, refmap: map<Reference, Node>) : map<Reference, Node>
  requires refs <= refmap.Keys
  {
    map ref | ref in refs :: refmap[ref]
  }

  function DiskGraph(indirectionTable: IndirectionTable, blocks: imap<Location, Sector>) : map<Reference, Node>
  requires WFDisk(blocks)
  requires M.WFCompleteIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, blocks)
  {
    Graph(indirectionTable.graph.Keys, RefMapOfDisk(indirectionTable, blocks))
  }

  function PersistentGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(s.disk.blocks)
  requires WFIndirectionTableWrtDisk(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks)
  {
    DiskGraph(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks)
  }

  function {:opaque} QueueLookupIdByLocation(reqWrites: map<D.ReqId, D.ReqWrite>, loc: Location) : (res : Option<D.ReqId>)
  ensures res.None? ==> forall id | id in reqWrites :: reqWrites[id].loc != loc
  ensures res.Some? ==> res.value in reqWrites && reqWrites[res.value].loc == loc
  {
    if id :| id in reqWrites && reqWrites[id].loc == loc then Some(id) else None
  }

  predicate WFIndirectionTableRefWrtDiskQueue(indirectionTable: IndirectionTable, disk: D.Variables, ref: Reference)
  requires ref in indirectionTable.locs
  {
    && (QueueLookupIdByLocation(disk.reqWrites, indirectionTable.locs[ref]).None? ==>
      && indirectionTable.locs[ref] in disk.blocks
      && disk.blocks[indirectionTable.locs[ref]].SectorNode?
    )
  }

  predicate WFIndirectionTableWrtDiskQueue(indirectionTable: IndirectionTable, disk: D.Variables)
  {
    && (forall ref | ref in indirectionTable.locs :: WFIndirectionTableRefWrtDiskQueue(indirectionTable, disk, ref))
  }

  predicate WFReqWriteBlocks(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id | id in reqWrites && ValidNodeLocation(reqWrites[id].loc) ::
        reqWrites[id].sector.SectorNode?
  }

  function DiskQueueLookup(disk: D.Variables, loc: Location) : Node
  requires WFDisk(disk.blocks)
  requires WFReqWriteBlocks(disk.reqWrites)
  requires ValidNodeLocation(loc)
  requires !QueueLookupIdByLocation(disk.reqWrites, loc).Some? ==> loc in disk.blocks
  requires !QueueLookupIdByLocation(disk.reqWrites, loc).Some? ==> disk.blocks[loc].SectorNode?
  {
    if QueueLookupIdByLocation(disk.reqWrites, loc).Some? then
      disk.reqWrites[QueueLookupIdByLocation(disk.reqWrites, loc).value].sector.block
    else
      disk.blocks[loc].block
  }

  function DiskQueueCacheLookup(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>, ref: Reference) : Node
  requires WFDisk(disk.blocks)
  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDiskQueue(indirectionTable, disk)
  requires M.IndirectionTableCacheConsistent(indirectionTable, cache)
  requires WFReqWriteBlocks(disk.reqWrites)
  requires ref in indirectionTable.graph
  {
    if ref in indirectionTable.locs then (
      DiskQueueLookup(disk, indirectionTable.locs[ref])
    ) else (
      cache[ref]
    )
  }

  function DiskCacheGraph(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>) : map<Reference, Node>
  requires WFDisk(disk.blocks)
  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDiskQueue(indirectionTable, disk)
  requires M.IndirectionTableCacheConsistent(indirectionTable, cache)
  requires WFReqWriteBlocks(disk.reqWrites)
  {
    map ref | ref in indirectionTable.graph :: DiskQueueCacheLookup(indirectionTable, disk, cache, ref)
  }

  function FrozenGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(s.disk.blocks)
  requires s.machine.Ready?
  requires s.machine.frozenIndirectionTable.Some?
  requires M.WFIndirectionTable(s.machine.frozenIndirectionTable.value)
  requires WFIndirectionTableWrtDiskQueue(s.machine.frozenIndirectionTable.value, s.disk)
  requires M.IndirectionTableCacheConsistent(s.machine.frozenIndirectionTable.value, s.machine.cache)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
  }

  function FrozenGraphOpt(k: Constants, s: Variables) : Option<map<Reference, Node>>
  requires WFDisk(s.disk.blocks)
  requires s.machine.Ready? && s.machine.frozenIndirectionTable.Some? ==> M.WFIndirectionTable(s.machine.frozenIndirectionTable.value)
  requires s.machine.Ready? && s.machine.frozenIndirectionTable.Some? ==> WFIndirectionTableWrtDiskQueue(s.machine.frozenIndirectionTable.value, s.disk)
  requires s.machine.Ready? && s.machine.frozenIndirectionTable.Some? ==> M.IndirectionTableCacheConsistent(s.machine.frozenIndirectionTable.value, s.machine.cache)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    if s.machine.Ready? && s.machine.frozenIndirectionTable.Some? then Some(FrozenGraph(k, s)) else None
  }

  function EphemeralGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires M.Inv(k.machine, s.machine)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  requires WFIndirectionTableWrtDiskQueue(s.machine.ephemeralIndirectionTable, s.disk)
  requires M.IndirectionTableCacheConsistent(s.machine.ephemeralIndirectionTable, s.machine.cache)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
  }

  function EphemeralGraphOpt(k: Constants, s: Variables) : Option<map<Reference, Node>>
  requires M.Inv(k.machine, s.machine)
  requires WFDisk(s.disk.blocks)
  requires s.machine.Ready? ==> WFIndirectionTableWrtDiskQueue(s.machine.ephemeralIndirectionTable, s.disk)
  requires s.machine.Ready? ==> M.IndirectionTableCacheConsistent(s.machine.ephemeralIndirectionTable, s.machine.cache)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    if s.machine.Ready? then Some(EphemeralGraph(k, s)) else None
  }

  predicate NoDanglingPointers(graph: map<Reference, Node>)
  {
    forall r1, r2 {:trigger r2 in M.G.Successors(graph[r1])}
      | r1 in graph && r2 in M.G.Successors(graph[r1])
      :: r2 in graph
  }

  predicate SuccessorsAgree(succGraph: map<Reference, seq<Reference>>, graph: map<Reference, Node>)
  {
    && succGraph.Keys == graph.Keys
    && forall ref | ref in succGraph :: (iset r | r in succGraph[ref]) == M.G.Successors(graph[ref])
  }

  ///// Init

  predicate Init(k: Constants, s: Variables)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
    && WFDisk(s.disk.blocks)
    && WFIndirectionTableWrtDisk(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(IndirectionTableOfDisk(s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && PersistentGraph(k, s).Keys == {M.G.Root()}
    && M.G.Successors(PersistentGraph(k, s)[M.G.Root()]) == iset{}
  }

  ////// Next

  datatype Step =
    | MachineStep(dop: DiskOp, machineStep: M.Step)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, dop: DiskOp, machineStep: M.Step)
  {
    && M.NextStep(k.machine, s.machine, s'.machine, dop, machineStep)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate DiskInternal(k: Constants, s: Variables, s': Variables, step: D.InternalStep)
  {
    && s.machine == s'.machine
    && D.NextInternalStep(k.disk, s.disk, s'.disk, step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case MachineStep(dop, machineStep) => Machine(k, s, s', dop, machineStep)
      case DiskInternalStep(step) => DiskInternal(k, s, s', step)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  ////// Invariants

  predicate CleanCacheEntriesAreCorrect(k: Constants, s: Variables)
  requires WFDisk(s.disk.blocks)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  requires s.machine.Ready?
  requires M.WFIndirectionTable(s.machine.ephemeralIndirectionTable)
  requires WFIndirectionTableWrtDiskQueue(s.machine.ephemeralIndirectionTable, s.disk)
  {
    forall ref | ref in s.machine.cache ::
      ref in s.machine.ephemeralIndirectionTable.locs ==>
        s.machine.cache[ref] == DiskQueueLookup(s.disk, s.machine.ephemeralIndirectionTable.locs[ref])
  }

  // Any outstanding read we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockRead(k: Constants, s: Variables, id: D.ReqId, ref: Reference)
  requires s.machine.Ready?
  {
    && ref !in s.machine.cache
    && ref in s.machine.ephemeralIndirectionTable.locs
    && var loc := s.machine.ephemeralIndirectionTable.locs[ref];
    && loc in s.disk.blocks
    && var sector := s.disk.blocks[loc];
    && !(id in s.disk.reqReads && id in s.disk.respReads)
    && (id in s.disk.reqReads ==> s.disk.reqReads[id] == D.ReqRead(loc))
    && (id in s.disk.respReads && s.disk.respReads[id].sector.Some? ==> s.disk.respReads[id] == D.RespRead(Some(sector)))
  }

  predicate CorrectInflightBlockReads(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall id | id in s.machine.outstandingBlockReads ::
      CorrectInflightBlockRead(k, s, id, s.machine.outstandingBlockReads[id].ref)
  }

  predicate CorrectInflightIndirectionTableReads(k: Constants, s: Variables)
  requires s.machine.LoadingOther?
  requires WFDisk(s.disk.blocks)
  {
    s.machine.indirectionTableRead.Some? ==> (
      && var reqId := s.machine.indirectionTableRead.value;
      && !(reqId in s.disk.reqReads && reqId in s.disk.respReads)
      && (reqId in s.disk.reqReads ==>
        s.disk.reqReads[reqId] == D.ReqRead(s.machine.superblock.indirectionTableLoc)
      )
      && (reqId in s.disk.respReads && s.disk.respReads[reqId].sector.Some? ==>
        s.disk.respReads[reqId] == D.RespRead(Some(SectorIndirectionTable(IndirectionTableOfDisk(s.disk.blocks))))
      )
    )
  }

  predicate CorrectInflightSuperblockReads(k: Constants, s: Variables)
  requires s.machine.LoadingSuperblock?
  requires WFDisk(s.disk.blocks)
  {
    && (s.machine.outstandingSuperblock1Read.Some? ==> (
      && var reqId := s.machine.outstandingSuperblock1Read.value;
      && !(reqId in s.disk.reqReads && reqId in s.disk.respReads)
      && (reqId in s.disk.reqReads ==>
        s.disk.reqReads[reqId] == D.ReqRead(Superblock1Location())
      )
      && (reqId in s.disk.respReads && s.disk.respReads[reqId].sector.Some? ==>
        && Superblock1Location() in s.disk.blocks
        && s.disk.respReads[reqId] == D.RespRead(Some(s.disk.blocks[Superblock1Location()]))
      )
    ))
    && (s.machine.outstandingSuperblock2Read.Some? ==> (
      && var reqId := s.machine.outstandingSuperblock2Read.value;
      && !(reqId in s.disk.reqReads && reqId in s.disk.respReads)
      && (reqId in s.disk.reqReads ==>
        s.disk.reqReads[reqId] == D.ReqRead(Superblock2Location())
      )
      && (reqId in s.disk.respReads && s.disk.respReads[reqId].sector.Some? ==>
        && Superblock2Location() in s.disk.blocks
        && s.disk.respReads[reqId] == D.RespRead(Some(s.disk.blocks[Superblock2Location()]))
      )
    ))
  }

  // Any outstanding write we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockWrite(k: Constants, s: Variables, id: D.ReqId, ref: Reference, loc: Location)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    && ValidNodeLocation(loc)
    && (forall r | r in s.machine.ephemeralIndirectionTable.locs ::
        s.machine.ephemeralIndirectionTable.locs[r].addr == loc.addr ==> r == ref)

    && (s.machine.frozenIndirectionTable.Some? ==>
        forall r | r in s.machine.frozenIndirectionTable.value.locs ::
        s.machine.frozenIndirectionTable.value.locs[r].addr == loc.addr ==> r == ref)

    && (forall r | r in IndirectionTableOfDisk(s.disk.blocks).locs ::
        IndirectionTableOfDisk(s.disk.blocks).locs[r].addr != loc.addr)

    && (id in s.disk.reqWrites ==>
      && s.disk.reqWrites[id].loc == loc
      && s.disk.reqWrites[id].sector.SectorNode?
    )

    && !(id in s.disk.reqWrites && id in s.disk.respWrites)
    && (id in s.disk.reqWrites || id in s.disk.respWrites)
  }

  predicate CorrectInflightBlockWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    forall id | id in s.machine.outstandingBlockWrites ::
      CorrectInflightBlockWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, s.machine.outstandingBlockWrites[id].loc)
  }

  predicate CorrectInflightJournalWrite(k: Constants, s: Variables, id: D.ReqId)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    && (id in s.disk.reqWrites ==>
      && ValidJournalLocation(s.disk.reqWrites[id].loc)
      && s.disk.reqWrites[id].sector.SectorJournal?
    )

    && !(id in s.disk.reqWrites && id in s.disk.respWrites)
    && (id in s.disk.reqWrites || id in s.disk.respWrites)
  }

  predicate CorrectInflightJournalWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    forall id | id in s.machine.outstandingJournalWrites ::
      CorrectInflightJournalWrite(k, s, id)
  }

  predicate CorrectInflightIndirectionTableWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    s.machine.outstandingIndirectionTableWrite.Some? ==> (
      && s.machine.frozenIndirectionTable.Some?
      && var reqId := s.machine.outstandingIndirectionTableWrite.value;
      && !(reqId in s.disk.reqWrites && reqId in s.disk.respWrites)
      && (reqId in s.disk.reqWrites || reqId in s.disk.respWrites)
      && s.machine.frozenIndirectionTableLoc.Some?
      && (reqId in s.disk.reqWrites ==>
          s.disk.reqWrites[reqId] ==
          D.ReqWrite(
            s.machine.frozenIndirectionTableLoc.value,
            SectorIndirectionTable(
              s.machine.frozenIndirectionTable.value
            )
          )
      )
      && (reqId in s.disk.respWrites ==>
        && s.machine.frozenIndirectionTableLoc.value in s.disk.blocks
        && s.disk.blocks[s.machine.frozenIndirectionTableLoc.value].SectorIndirectionTable?
        && s.machine.frozenIndirectionTable == Some(s.disk.blocks[s.machine.frozenIndirectionTableLoc.value].indirectionTable)
      )
    )
  }

  predicate CorrectInflightSuperblockWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    s.machine.superblockWrite.Some? ==> (
      && s.machine.newSuperblock.Some?
      && var reqId := s.machine.superblockWrite.value;
      && !(reqId in s.disk.reqWrites && reqId in s.disk.respWrites)
      && (reqId in s.disk.reqWrites || reqId in s.disk.respWrites)
      && (s.machine.whichSuperblock == 0 || s.machine.whichSuperblock == 1)
      && var loc := if s.machine.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
      && var otherloc := if s.machine.whichSuperblock == 0 then Superblock1Location() else Superblock2Location();

      && (reqId in s.disk.reqWrites ==>
        && s.disk.reqWrites[reqId] ==
          D.ReqWrite(loc, SectorSuperblock(s.machine.newSuperblock.value))
        && otherloc in s.disk.blocks
        && s.disk.blocks[otherloc] == SectorSuperblock(s.machine.superblock)
        && SuperblockOfDisk(s.disk.blocks) == s.machine.superblock
      )
      && (reqId in s.disk.respWrites ==>
        && loc in s.disk.blocks
        && s.disk.blocks[loc].SectorSuperblock?
        && s.machine.newSuperblock == Some(s.disk.blocks[loc].superblock)
      )
    )
  }

  predicate WriteReqIdsDistinct(s: M.Variables)
  requires s.Ready?
  {
    && (s.superblockWrite.Some? ==> (
      && s.superblockWrite != s.outstandingIndirectionTableWrite
    ))

    && (forall id | id in s.outstandingJournalWrites ::
      s.superblockWrite != Some(id))
    && (forall id | id in s.outstandingJournalWrites ::
      s.outstandingIndirectionTableWrite != Some(id))

    && (forall id | id in s.outstandingBlockWrites ::
      s.superblockWrite != Some(id))
    && (forall id | id in s.outstandingBlockWrites ::
      s.outstandingIndirectionTableWrite != Some(id))

    && (forall id1, id2 |
      id1 in s.outstandingJournalWrites
        && id2 in s.outstandingBlockWrites ::
      id1 != id2)
  }

  // If there's a write in progress, then the in-memory state must know about it.

  predicate RecordedWriteRequest(k: Constants, s: Variables, id: D.ReqId, loc: Location, sector: Sector)
  {
    && s.machine.Ready?
    && (sector.SectorIndirectionTable? ==>
      && s.machine.outstandingIndirectionTableWrite == Some(id)
      && s.machine.frozenIndirectionTable == Some(sector.indirectionTable)
    )
    && (sector.SectorNode? ==>
      && id in s.machine.outstandingBlockWrites
    )
    && (sector.SectorSuperblock? ==>
      s.machine.superblockWrite == Some(id)
    )
    && (sector.SectorJournal? ==>
      id in s.machine.outstandingJournalWrites
    )
  }

  predicate RecordedReadRequest(k: Constants, s: Variables, id: D.ReqId)
  {
    && (s.machine.Ready? ==> id in s.machine.outstandingBlockReads)
    && (s.machine.LoadingOther? ==>
      || Some(id) == s.machine.indirectionTableRead
      || Some(id) == s.machine.journalFrontRead
      || Some(id) == s.machine.journalBackRead
    )
    && (s.machine.LoadingSuperblock? ==>
      || Some(id) == s.machine.outstandingSuperblock1Read
      || Some(id) == s.machine.outstandingSuperblock2Read
    )
  }

  predicate RecordedWriteRequests(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqWrites :: RecordedWriteRequest(k, s, id, s.disk.reqWrites[id].loc, s.disk.reqWrites[id].sector)
  }

  predicate RecordedReadRequests(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqReads :: RecordedReadRequest(k, s, id)
  }

  predicate WriteRequestsUniqueLBAs(reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && reqWrites[id1].loc.addr == reqWrites[id2].loc.addr :: id1 == id2
  }

  predicate NoReadWriteConflicts(
      reqReads: map<D.ReqId, D.ReqRead>,
      reqWrites: map<D.ReqId, D.ReqWrite>)
  {
    forall id1, id2 | id1 in reqReads && id2 in reqWrites :: reqReads[id1].loc.addr != reqWrites[id2].loc.addr
  }

  predicate Inv(k: Constants, s: Variables) {
    && M.Inv(k.machine, s.machine)
    && WFDisk(s.disk.blocks)
    && WFReqWriteBlocks(s.disk.reqWrites)
    && WFIndirectionTableWrtDisk(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(IndirectionTableOfDisk(s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && (s.machine.frozenIndirectionTable.Some? ==>
        && WFIndirectionTableWrtDiskQueue(s.machine.frozenIndirectionTable.value, s.disk)
        && SuccessorsAgree(s.machine.frozenIndirectionTable.value.graph, FrozenGraph(k, s))
      )
      && (s.machine.frozenIndirectionTableLoc.Some? ==>
        && s.machine.frozenIndirectionTable.Some?
        && M.WFCompleteIndirectionTable(s.machine.frozenIndirectionTable.value)
        && (s.machine.outstandingIndirectionTableWrite.None? ==> (
          && s.machine.frozenIndirectionTableLoc.value in s.disk.blocks
          && s.disk.blocks[s.machine.frozenIndirectionTableLoc.value].SectorIndirectionTable?
          && s.machine.frozenIndirectionTable == Some(s.disk.blocks[s.machine.frozenIndirectionTableLoc.value].indirectionTable)
        ))
      )
      //&& (s.machine.outstandingIndirectionTableWrite.Some? ==>
      //  && WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.blocks)
      //  && s.machine.outstandingBlockWrites == map[]
      //)
      //&& (
      //  || s.machine.persistentIndirectionTable == IndirectionTableOfDisk(s.disk.blocks)
      //  || s.machine.frozenIndirectionTable == Some(IndirectionTableOfDisk(s.disk.blocks))
      //)
      && (
        || s.machine.superblock == SuperblockOfDisk(s.disk.blocks)
        || s.machine.newSuperblock == Some(SuperblockOfDisk(s.disk.blocks))
      )
      && s.machine.superblock.indirectionTableLoc in s.disk.blocks
      && s.disk.blocks[s.machine.superblock.indirectionTableLoc]
        == SectorIndirectionTable(s.machine.persistentIndirectionTable)
      && (s.machine.superblockWrite.None? ==>
        || s.machine.persistentIndirectionTable == IndirectionTableOfDisk(s.disk.blocks)
      )
      && (s.machine.newSuperblock.Some? ==>
        && WFDiskWithSuperblock(
            s.disk.blocks,
            s.machine.newSuperblock.value)
        && (s.machine.newSuperblock.value.indirectionTableLoc !=
            s.machine.superblock.indirectionTableLoc ==> (
          && s.machine.frozenIndirectionTableLoc.Some?
          && s.machine.outstandingIndirectionTableWrite.None?
          && s.machine.newSuperblock.value.indirectionTableLoc ==
                s.machine.frozenIndirectionTableLoc.value
          && WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.blocks)
          && disjointWritesFromIndirectionTable(s.machine.outstandingBlockWrites, s.machine.frozenIndirectionTable.value)
        ))

        /*&& s.machine.frozenIndirectionTable.Some?
        && s.disk.blocks[s.machine.newSuperblock.value.indirectionTableLoc].indirectionTable
            == s.machine.frozenIndirectionTable.value*/
      )
      && WFIndirectionTableWrtDiskQueue(s.machine.ephemeralIndirectionTable, s.disk)
      && SuccessorsAgree(s.machine.ephemeralIndirectionTable.graph, EphemeralGraph(k, s))
      && NoDanglingPointers(EphemeralGraph(k, s))
      && CleanCacheEntriesAreCorrect(k, s)
      && CorrectInflightBlockReads(k, s)
      && CorrectInflightBlockWrites(k, s)
      && CorrectInflightIndirectionTableWrites(k, s)
      && CorrectInflightJournalWrites(k, s)
      && CorrectInflightSuperblockWrites(k, s)
      && WriteReqIdsDistinct(s.machine)
    )
    && (s.machine.LoadingSuperblock? ==>
      && CorrectInflightSuperblockReads(k, s)
      && (s.machine.superblock1.SuperblockSuccess? ==>
        && DiskHasSuperblock1(s.disk.blocks)
        && s.machine.superblock1.value == Superblock1OfDisk(s.disk.blocks)
        && s.machine.outstandingSuperblock1Read.None?
      )
      && (s.machine.superblock2.SuperblockSuccess? ==>
        && DiskHasSuperblock2(s.disk.blocks)
        && s.machine.superblock2.value == Superblock2OfDisk(s.disk.blocks)
        && s.machine.outstandingSuperblock2Read.None?
      )
      && (s.machine.superblock1.SuperblockCorruption? ==>
        && !DiskHasSuperblock1(s.disk.blocks)
        && s.machine.outstandingSuperblock1Read.None?
      )
      && (s.machine.superblock2.SuperblockCorruption? ==>
        && !DiskHasSuperblock2(s.disk.blocks)
        && s.machine.outstandingSuperblock2Read.None?
      )
    )
    && (s.machine.LoadingOther? ==>
      && s.machine.superblock == SuperblockOfDisk(s.disk.blocks)
      && CorrectInflightIndirectionTableReads(k, s)
      && (s.machine.indirectionTable.Some? ==> (
        && s.machine.indirectionTableRead.None?
        && s.machine.indirectionTable.value
            == IndirectionTableOfDisk(s.disk.blocks)
      ))
      && (s.machine.journalFront.Some? ==> (
        && s.machine.journalFrontRead.None?
      ))
      && (s.machine.journalBack.Some? ==> (
        && s.machine.journalBackRead.None?
      ))
      && (M.JournalFrontLocation(s.machine.superblock).None? ==> (
        && s.machine.journalFrontRead.None?
        && s.machine.journalFront.None?
      ))
      && (M.JournalBackLocation(s.machine.superblock).None? ==> (
        && s.machine.journalBackRead.None?
        && s.machine.journalBack.None?
      ))
    )
    && WriteRequestsUniqueLBAs(s.disk.reqWrites)
    && NoReadWriteConflicts(s.disk.reqReads, s.disk.reqWrites)
    && RecordedWriteRequests(k, s)
    && RecordedReadRequests(k, s)
  }

  ////// Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma QueueLookupIdByLocationInsert(
      reqWrites: map<D.ReqId, D.ReqWrite>,
      reqWrites': map<D.ReqId, D.ReqWrite>,
      id: D.ReqId,
      req: D.ReqWrite,
      loc: Location)
  requires id !in reqWrites
  requires reqWrites' == reqWrites[id := req]
  requires WriteRequestsUniqueLBAs(reqWrites')
  ensures QueueLookupIdByLocation(reqWrites', req.loc) == Some(id)
  ensures loc != req.loc ==>
      QueueLookupIdByLocation(reqWrites', loc) == QueueLookupIdByLocation(reqWrites, loc)
  {
    assert reqWrites'[id].loc == req.loc;
    //if (QueueLookupIdByLocation(reqWrites', req.loc).None?) {
    //  assert forall id | id in reqWrites' :: reqWrites'[id].loc != req.loc;
    //  assert false;
    //}
    //assert QueueLookupIdByLocation(reqWrites', req.loc).Some?;
    //assert QueueLookupIdByLocation(reqWrites', req.loc).value == id;

    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && reqWrites[id1].loc.addr == reqWrites[id2].loc.addr
    ensures id1 == id2
    {
      assert reqWrites'[id1] == reqWrites[id1];
      assert reqWrites'[id2] == reqWrites[id2];
    }
    assert WriteRequestsUniqueLBAs(reqWrites);

    if (loc != req.loc) {
      if id' :| id' in reqWrites && reqWrites[id'].loc == loc {
        assert reqWrites'[id'].loc == loc;
        //assert QueueLookupIdByLocation(reqWrites', loc)
        //    == Some(id')
        //    == QueueLookupIdByLocation(reqWrites, loc);
      } else {
        //assert QueueLookupIdByLocation(reqWrites', loc) == QueueLookupIdByLocation(reqWrites, loc);
      }
    }
  }

  lemma WriteBackReqStepUniqueLBAs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures WriteRequestsUniqueLBAs(s'.disk.reqWrites)
  {
    forall id1, id2 | id1 in s'.disk.reqWrites && id2 in s'.disk.reqWrites && s'.disk.reqWrites[id1].loc.addr == s'.disk.reqWrites[id2].loc.addr
    ensures id1 == id2
    {
      overlappingLocsSameType(
          s'.disk.reqWrites[id1].loc,
          s'.disk.reqWrites[id2].loc);

      /*if (s'.disk.reqWrites[id1].loc == dop.reqWrite.loc) {
        assert overlap(s'.disk.reqWrites[id1].loc, s'.disk.reqWrites[id2].loc);
        assert ValidNodeLocation(s'.disk.reqWrites[id1].loc);

        if (ValidNodeLocation(s'.disk.reqWrites[id2].loc)) {
          assert s'.disk.reqWrites[id1].loc == s'.disk.reqWrites[id2].loc;
        } else {
          assert ValidLocation(s'.disk.reqWrites[id2].loc);
          assert false;
        }

        assert s'.disk.reqWrites[id1].loc == s'.disk.reqWrites[id2].loc;

        if (id1 in s.disk.reqWrites) {
          assert RecordedWriteRequest(k, s, id1, s.disk.reqWrites[id1].loc, s.disk.reqWrites[id1].sector);
          assert id1 in s.machine.outstandingBlockWrites;
          assert CorrectInflightBlockWrite(k, s, id1, s.machine.outstandingBlockWrites[id1].ref, s.machine.outstandingBlockWrites[id1].loc);
          assert s.machine.outstandingBlockWrites[id1].loc == dop.reqWrite.loc;
          assert false;
        }
        if (id2 in s.disk.reqWrites) {
          assert RecordedWriteRequest(k, s, id2, s.disk.reqWrites[id2].loc, s.disk.reqWrites[id2].sector);
          assert id2 in s.machine.outstandingBlockWrites;
          assert CorrectInflightBlockWrite(k, s, id2, s.machine.outstandingBlockWrites[id2].ref, s.machine.outstandingBlockWrites[id2].loc);
          assert s.machine.outstandingBlockWrites[id2].loc == dop.reqWrite.loc;
          assert false;
        }
        assert id1 == dop.id;
        assert id2 == dop.id;
        assert id1 == id2;
      } else if (s'.disk.reqWrites[id2].loc == dop.reqWrite.loc) {
        assert id1 == id2;
      } else {
        assert id1 in s.disk.reqWrites;
        assert id2 in s.disk.reqWrites;
        assert s.disk.reqWrites[id1].loc.addr == s.disk.reqWrites[id2].loc.addr;
        assert id1 == id2;
      }*/
    }
  }

  lemma WriteBackReqStepPreservesDiskCacheGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, indirectionTable: IndirectionTable, indirectionTable': IndirectionTable)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);

    requires M.WFIndirectionTable(indirectionTable)
    requires WFIndirectionTableWrtDiskQueue(indirectionTable, s.disk)
    requires indirectionTable' == M.assignRefToLocation(indirectionTable, ref, dop.reqWrite.loc)
    requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
    requires dop.reqWrite.loc !in indirectionTable.locs.Values

    ensures M.WFIndirectionTable(indirectionTable')
    ensures WFIndirectionTableWrtDiskQueue(indirectionTable', s'.disk)
    ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
         == DiskCacheGraph(indirectionTable', s'.disk, s'.machine.cache)
  {
    assert dop.id !in s.disk.reqWrites;

    WriteBackReqStepUniqueLBAs(k, s, s', dop, ref);

    forall r | r in indirectionTable'.locs
    ensures WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r)
    {
      if (r == ref && ref !in indirectionTable.locs) {
        assert s'.disk.reqWrites[dop.id].loc == dop.reqWrite.loc;
        //assert indirectionTable'.locs[ref] == dop.reqWrite.loc;
        //assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable'.locs[ref]).Some?;
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r);
      } else {
        //assert r in indirectionTable.locs;
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable, s.disk, r);
        //assert indirectionTable.locs[r] == indirectionTable'.locs[r];
        //assert s.disk.blocks == s'.disk.blocks;
        if QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[r]).Some? {
          var oid := QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[r]).value;
          //assert oid in s.disk.reqWrites;
          //assert s.disk.reqWrites[oid].loc == indirectionTable.locs[r];
          assert s'.disk.reqWrites[oid].loc == indirectionTable.locs[r];
          //assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable.locs[r]).Some?;
        }
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r);
      }
    }

    forall r | r in indirectionTable.graph
    ensures DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
         == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r)
    {
      if (r == ref) {
        QueueLookupIdByLocationInsert(s.disk.reqWrites, s'.disk.reqWrites, dop.id, dop.reqWrite, indirectionTable'.locs[ref]);

        //assert s'.disk.reqWrites[dop.id].loc == dop.reqWrite.loc;
        /*
        assert indirectionTable'.locs[ref] == dop.reqWrite.loc;
        assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable'.locs[ref]).Some?;
        assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable'.locs[ref]) == Some(dop.id);
        assert s'.disk.reqWrites[dop.id].sector.SectorNode?;
        assert r !in indirectionTable.locs;

        assert DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
            == s.machine.cache[r]
            == s'.disk.reqWrites[dop.id].sector.block
            == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
        */
      } else if (r in indirectionTable.locs) {
        //assert indirectionTable.locs[r] != dop.reqWrite.loc;
        QueueLookupIdByLocationInsert(s.disk.reqWrites, s'.disk.reqWrites, dop.id, dop.reqWrite, indirectionTable.locs[r]);

        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable, s.disk, r);
        //assert indirectionTable.locs[r] == indirectionTable'.locs[r];
        //assert s.disk.blocks == s'.disk.blocks;

        /*
        if QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[r]).Some? {
          var oid := QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[r]).value;
          assert oid in s.disk.reqWrites;
          assert s.disk.reqWrites[oid].loc == indirectionTable.locs[r];
          assert s'.disk.reqWrites[oid].loc == indirectionTable.locs[r];
          assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable.locs[r]).Some?;
          assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable'.locs[r])
              == QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[r]);
        } else {
          assert QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable.locs[r]).None?;
          assert s.disk.blocks[indirectionTable.locs[r]].block
              == s'.disk.blocks[indirectionTable.locs[r]].block
              == s'.disk.blocks[indirectionTable'.locs[r]].block;
        }
        */

        //assert DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
        //    == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
      } else {
        //assert DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
        //    == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
      }
    }
  }

  lemma WriteBackReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);

    ensures s.machine.frozenIndirectionTable.Some? ==> (
      && s'.machine.frozenIndirectionTable.Some?
      && WFIndirectionTableWrtDiskQueue(s'.machine.frozenIndirectionTable.value, s'.disk)
    )

    ensures WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk)

    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
    WriteBackReqStepPreservesDiskCacheGraph(k, s, s', dop, ref, s.machine.ephemeralIndirectionTable, s'.machine.ephemeralIndirectionTable);
    if s.machine.frozenIndirectionTable.Some? {
      WriteBackReqStepPreservesDiskCacheGraph(k, s, s', dop, ref, s.machine.frozenIndirectionTable.value, s'.machine.frozenIndirectionTable.value);
    }
  }

  lemma WriteBackReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackReqStepUniqueLBAs(k, s, s', dop, ref);
    WriteBackReqStepPreservesGraphs(k, s, s', dop, ref);

    /*assert ValidNodeLocation(dop.reqWrite.loc);
    forall id | id in s'.machine.outstandingJournalWrites
    ensures CorrectInflightJournalWrite(k, s', id)
    {
      assert CorrectInflightJournalWrite(k, s, id);
      if (id in s'.disk.reqWrites) {
        assert id != dop.id;
        assert id in s.disk.reqWrites;
        assert id in s.machine.outstandingJournalWrites;
      }
      assert CorrectInflightJournalWrite(k, s', id);
    }
    assert CorrectInflightJournalWrites(k, s');*/

    assert IndirectionTableOfDisk(s.disk.blocks)
        == IndirectionTableOfDisk(s'.disk.blocks);

    /*if (s.machine.newSuperblock.Some?) {
      assert s.machine.superblockWrite.Some?;
      var reqId := s.machine.superblockWrite.value;
      if reqId in s.disk.reqWrites {
        assert IndirectionTableOfDisk(s.disk.blocks)
            == s.machine.persistentIndirectionTable;
      } else {
        assert reqId in s.disk.respWrites;

        assert IndirectionTableOfDisk(s.disk.blocks)
            == s.machine.persistentIndirectionTable
          || Some(IndirectionTableOfDisk(s.disk.blocks))
            == s.machine.frozenIndirectionTable;
      }
    } else {
      assert IndirectionTableOfDisk(s.disk.blocks)
          == s.machine.persistentIndirectionTable;
    }

    assert IndirectionTableOfDisk(s.disk.blocks)
        == s.machine.persistentIndirectionTable
      || Some(IndirectionTableOfDisk(s.disk.blocks))
        == s.machine.frozenIndirectionTable;*/

    /*var loc := s'.machine.outstandingBlockWrites[dop.id].loc;
    forall r | r in IndirectionTableOfDisk(s'.disk.blocks).locs
    ensures IndirectionTableOfDisk(s'.disk.blocks).locs[r].addr != loc.addr
    {
      forall t | t in s.machine.persistentIndirectionTable.locs
      ensures s.machine.persistentIndirectionTable.locs[t].addr
          != loc.addr
      {
      }

      //assert forall t |
      //  t in s.machine.persistentIndirectionTable.locs ::
      //      s.machine.persistentIndirectionTable.locs[t].addr != loc.t;
    }*/

    //assert CorrectInflightBlockWrite(k, s', dop.id,
    //    s'.machine.outstandingBlockWrites[dop.id].ref,
    //    s'.machine.outstandingBlockWrites[dop.id].loc);
  }

  lemma WriteBackRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma WriteBackRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackRespStepPreservesGraphs(k, s, s', dop);
    /*forall id | id in s'.machine.outstandingJournalWrites
    ensures CorrectInflightJournalWrite(k, s', id)
    {
      assert id in s.machine.outstandingJournalWrites;
      assert dop.id in s.machine.outstandingBlockWrites;
      assert id != dop.id;
      assert CorrectInflightJournalWrite(k, s, id);
    }*/
  }

  lemma WriteBackIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);

    ensures s'.machine.Ready? && s'.machine.frozenIndirectionTable.Some? ==> WFIndirectionTableWrtDiskQueue(s'.machine.frozenIndirectionTable.value, s'.disk)
    ensures WFReqWriteBlocks(s'.disk.reqWrites)
    ensures WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk);

    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
    assert forall id | id in s.disk.reqWrites :: id in s'.disk.reqWrites;

    //assert forall loc ::
    //    ValidIndirectionTableLocation(loc) ==>
    //      !ValidNodeLocation(loc);
    //assert ValidIndirectionTableLocation(dop.reqWrite.loc);

    /*forall ref | ref in s'.machine.ephemeralIndirectionTable.locs
    ensures WFIndirectionTableRefWrtDiskQueue(
        s'.machine.ephemeralIndirectionTable, s'.disk, ref)
    {
      //assert WFIndirectionTableRefWrtDiskQueue(
      //  s.machine.ephemeralIndirectionTable, s.disk, ref);
      //var disk := s'.disk;
      var indirectionTable := s'.machine.ephemeralIndirectionTable;
      if (QueueLookupIdByLocation(s'.disk.reqWrites, indirectionTable.locs[ref]).None?) {
        //assert ValidNodeLocation(indirectionTable.locs[ref]);
        //assert dop.reqWrite.loc != indirectionTable.locs[ref];
        //assert dop.id !in s.disk.reqWrites;
        forall id | id in s.disk.reqWrites
        ensures s.disk.reqWrites[id].loc != indirectionTable.locs[ref]
        {
          //assert id in s'.disk.reqWrites;
          //assert s'.disk.reqWrites[id].loc != indirectionTable.locs[ref];
        }
        //assert QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[ref]).None?;
        //assert QueueLookupIdByLocation(s.disk.reqWrites, s.machine.ephemeralIndirectionTable.locs[ref]).None?;
        //assert indirectionTable.locs[ref] in s'.disk.blocks;
        //assert s'.disk.blocks[indirectionTable.locs[ref]].SectorNode?;
      }
    }*/
    assert WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk);

    assert s'.machine.Ready? && s'.machine.frozenIndirectionTable.Some? ==> WFIndirectionTableWrtDiskQueue(s'.machine.frozenIndirectionTable.value, s'.disk);
    assert WFReqWriteBlocks(s'.disk.reqWrites);

    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma WriteBackIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop);

    forall id1, id2 | id1 in s'.disk.reqReads && id2 in s'.disk.reqWrites
    ensures s'.disk.reqReads[id1].loc.addr != s'.disk.reqWrites[id2].loc.addr
    {
      assert ValidNodeLocation(s'.disk.reqReads[id1].loc);
    }

    forall id1, id2 | id1 in s'.disk.reqWrites && id2 in s'.disk.reqWrites && s'.disk.reqWrites[id1].loc.addr == s'.disk.reqWrites[id2].loc.addr
    ensures id1 == id2
    {
      overlappingLocsSameType(
          s'.disk.reqWrites[id1].loc,
          s'.disk.reqWrites[id2].loc);
    }
  }

  lemma WriteBackIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckWrite(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine)
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
    M.WriteBackIndirectionTableRespStepPreservesInv(k.machine, s.machine, s'.machine, dop);
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma WriteBackIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    M.WriteBackIndirectionTableRespStepPreservesInv(k.machine, s.machine, s'.machine, dop);
    WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
  }

  lemma DirtyStepUpdatesGraph(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s)
    ensures ref in EphemeralGraph(k, s)
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s)[ref := block]
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma DirtyStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  lemma AllocStepUpdatesGraph(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s)
    ensures ref !in EphemeralGraph(k, s)
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s)[ref := block]
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma AllocStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  lemma OpPreservesInv(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires M.OpStep(k.machine, s.machine, s'.machine, op)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
    match op {
      case WriteOp(ref, block) => DirtyStepPreservesInv(k, s, s', ref, block);
      case AllocOp(ref, block) => AllocStepPreservesInv(k, s, s', ref, block);
    }
  }

  lemma TransactionStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ops: seq<Op>)
    requires Inv(k, s)
    requires M.Transaction(k.machine, s.machine, s'.machine, dop, ops)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
    decreases |ops|
  {
    if |ops| == 0 {
    } else if |ops| == 1 {
      OpPreservesInv(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := M.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      TransactionStepPreservesInv(k, s, AsyncSectorDiskModelVariables(smid, s.disk), dop, ops1);
      TransactionStepPreservesInv(k, AsyncSectorDiskModelVariables(smid, s.disk), s', dop, ops2);
    }
  }

  lemma UnallocStepUpdatesGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraph(k, s') == MapRemove1(EphemeralGraph(k, s), ref)
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma UnallocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    /*
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;
    */
  }

  lemma PageInReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageInReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvRead(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageInReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInReqStepPreservesGraphs(k, s, s', dop, ref);

    forall id | id in s'.machine.outstandingBlockReads
    ensures CorrectInflightBlockRead(k, s', id, s'.machine.outstandingBlockReads[id].ref)
    {
    }

    forall id1, id2 | id1 in s'.disk.reqReads && id2 in s'.disk.reqWrites
    ensures s'.disk.reqReads[id1].loc.addr != s'.disk.reqWrites[id2].loc.addr
    {
      if (id1 == dop.id && s'.disk.reqReads[id1].loc.addr == s'.disk.reqWrites[id2].loc.addr) {
        //var loc := dop.reqRead.loc;
        //assert s.machine.ephemeralIndirectionTable.locs[ref] == loc;
        //assert id2 in s.disk.reqWrites;
        //assert RecordedWriteRequest(k, s, id2, s'.disk.reqWrites[id2].loc, s'.disk.reqWrites[id2].sector);
        //assert overlap(dop.reqRead.loc, s'.disk.reqWrites[id2].loc);
        //assert ValidNodeLocation(dop.reqRead.loc);
        overlappingLocsSameType(dop.reqRead.loc, s'.disk.reqWrites[id2].loc);
        //assert ValidNodeLocation(s'.disk.reqWrites[id2].loc);
        //assert s'.disk.reqWrites[id2].sector.SectorNode?;
        //assert id2 in s.machine.outstandingBlockWrites;
        //assert s.machine.outstandingBlockWrites[id2].ref != ref ||
        //    s.machine.outstandingBlockWrites[id2].loc.addr != s.machine.ephemeralIndirectionTable.locs[ref].addr;
        //assert false;
      }
    }
  }

  lemma PageInRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckRead(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInRespStepPreservesGraphs(k, s, s', dop);
  }

  lemma PageInIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvRead(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == None
    ensures EphemeralGraphOpt(k, s) == None
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
  }

  lemma PageInIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckRead(k.disk, s.disk, s'.disk, dop);

    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraphOpt(k, s') == None
  {
    //assert IndirectionTableOfDisk(s.disk.blocks) == s'.machine.persistentIndirectionTable;
    /*
    forall ref | ref in s'.machine.ephemeralIndirectionTable.locs
    ensures WFIndirectionTableRefWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk, ref)
    {
      assert ref in IndirectionTableOfDisk(s.disk.blocks).locs;
      assert WFIndirectionTableRefWrtDisk(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks, ref);
    }
    */
  }

  lemma PageInIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
  }

  lemma FinishLoadingSuperblockPhaseStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.FinishLoadingSuperblockPhase(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraphOpt(k, s') == None
  {
  }

  lemma FinishLoadingSuperblockPhaseStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.FinishLoadingSuperblockPhase(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    FinishLoadingSuperblockPhaseStepPreservesGraphs(k, s, s', dop);
  }

  lemma FinishLoadingOtherPhaseStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.FinishLoadingOtherPhase(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);

    ensures EphemeralGraph.requires(k, s')

    ensures PersistentGraph(k, s') == PersistentGraph(k, s)
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraph(k, s') == PersistentGraph(k, s)
  {
    assert WFIndirectionTableWrtDiskQueue(s.machine.indirectionTable.value, s.disk);

    assert s.disk.reqWrites == map[];
    forall ref | ref in s'.machine.ephemeralIndirectionTable.locs
    ensures WFIndirectionTableRefWrtDiskQueue(
        s'.machine.ephemeralIndirectionTable, s'.disk, ref)
    {
    }
    assert WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk);
  }

  lemma FinishLoadingOtherPhaseStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.FinishLoadingOtherPhase(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    FinishLoadingOtherPhaseStepPreservesGraphs(k, s, s', dop);
  }

  lemma EvictStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma EvictStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    EvictStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma FreezeStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.Freeze(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == Some(EphemeralGraph(k, s));
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
    M.FreezeStepPreservesInv(k.machine, s.machine, s'.machine, dop);
  }

  lemma FreezeStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.Freeze(k.machine, s.machine, s'.machine, dop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    M.FreezeStepPreservesInv(k.machine, s.machine, s'.machine, dop);
    FreezeStepPreservesGraphs(k, s, s', dop);
  }

  lemma PushSyncReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires M.PushSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
  {
  }

  lemma PushSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires M.PushSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PushSyncReqStepPreservesGraphs(k, s, s', dop, id);
  }

  lemma PopSyncReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires M.PopSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
  {
  }

  lemma PopSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: uint64)
    requires Inv(k, s)
    requires M.PopSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PopSyncReqStepPreservesGraphs(k, s, s', dop, id);
  }

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, machineStep: M.Step)
    requires Inv(k, s)
    requires Machine(k, s, s', dop, machineStep)
    ensures Inv(k, s')
  {
    match machineStep {
      case WriteBackReqStep(ref) => WriteBackReqStepPreservesInv(k, s, s', dop, ref);
      case WriteBackRespStep => WriteBackRespStepPreservesInv(k, s, s', dop);
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReqStepPreservesInv(k, s, s', dop);
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableRespStepPreservesInv(k, s, s', dop);
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, ref);
      case PageInReqStep(ref) => PageInReqStepPreservesInv(k, s, s', dop, ref);
      case PageInRespStep => PageInRespStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableReqStep => PageInIndirectionTableReqStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableRespStep => PageInIndirectionTableRespStepPreservesInv(k, s, s', dop);
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

  lemma ProcessReadPreservesGraphs(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessRead(k.disk, s.disk, s'.disk, id)
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraphOpt(k, s) == EphemeralGraphOpt(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
    if (EphemeralGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
  }

  lemma ProcessReadPreservesInv(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessRead(k.disk, s.disk, s'.disk, id)
    ensures Inv(k, s')
  {
  }

  lemma ProcessReadFailurePreservesGraphs(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessReadFailure(k.disk, s.disk, s'.disk, id)
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraphOpt(k, s) == EphemeralGraphOpt(k, s');
  {
    if (FrozenGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
    if (EphemeralGraphOpt(k, s).Some?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
  }

  lemma ProcessReadFailurePreservesInv(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessReadFailure(k.disk, s.disk, s'.disk, id)
    ensures Inv(k, s')
  {
  }

  lemma ProcessWrite_PreservesOtherTypes(k: Constants, s: Variables, s': Variables, id: D.ReqId)
  requires Inv(k, s)
  requires s.machine == s'.machine
  requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)
  ensures !ValidSuperblock1Location(s.disk.reqWrites[id].loc) ==> Superblock1Location() in s.disk.blocks ==> Superblock1Location() in s'.disk.blocks && s'.disk.blocks[Superblock1Location()] == s.disk.blocks[Superblock1Location()]
  ensures !ValidSuperblock1Location(s.disk.reqWrites[id].loc) ==> Superblock1Location() in s'.disk.blocks ==> Superblock1Location() in s.disk.blocks
  ensures !ValidSuperblock2Location(s.disk.reqWrites[id].loc) ==> Superblock2Location() in s.disk.blocks ==> Superblock2Location() in s'.disk.blocks && s'.disk.blocks[Superblock2Location()] == s.disk.blocks[Superblock2Location()]
  ensures !ValidSuperblock2Location(s.disk.reqWrites[id].loc) ==> Superblock2Location() in s'.disk.blocks ==> Superblock2Location() in s.disk.blocks
  ensures !ValidJournalLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidJournalLocation(loc) :: loc in s.disk.blocks ==> loc in s'.disk.blocks && s'.disk.blocks[loc] == s.disk.blocks[loc]
  ensures !ValidJournalLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidJournalLocation(loc) :: loc in s'.disk.blocks ==> loc in s.disk.blocks
  ensures !ValidIndirectionTableLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidIndirectionTableLocation(loc) :: loc in s.disk.blocks ==> loc in s'.disk.blocks && s'.disk.blocks[loc] == s.disk.blocks[loc]
  ensures !ValidIndirectionTableLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidIndirectionTableLocation(loc) :: loc in s'.disk.blocks ==> loc in s.disk.blocks
  ensures !ValidNodeLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidNodeLocation(loc) :: loc in s.disk.blocks ==> loc in s'.disk.blocks && s'.disk.blocks[loc] == s.disk.blocks[loc]
  ensures !ValidNodeLocation(s.disk.reqWrites[id].loc) ==> forall loc | ValidNodeLocation(loc) :: loc in s'.disk.blocks ==> loc in s.disk.blocks
  {
    forall loc | ValidLocation(loc) && overlap(s.disk.reqWrites[id].loc, loc)
    ensures ValidSuperblock1Location(s.disk.reqWrites[id].loc) <==> ValidSuperblock1Location(loc)
    ensures ValidSuperblock2Location(s.disk.reqWrites[id].loc) <==> ValidSuperblock2Location(loc)
    ensures ValidJournalLocation(s.disk.reqWrites[id].loc) <==> ValidJournalLocation(loc)
    ensures ValidIndirectionTableLocation(s.disk.reqWrites[id].loc) <==> ValidIndirectionTableLocation(loc)
    ensures ValidNodeLocation(s.disk.reqWrites[id].loc) <==> ValidNodeLocation(loc)
    {
      overlappingLocsSameType(s.disk.reqWrites[id].loc, loc);
    }
    assert ValidSuperblock1Location(Superblock1Location());
    assert ValidSuperblock2Location(Superblock2Location());

    if !ValidJournalLocation(s.disk.reqWrites[id].loc) {
      forall loc | ValidJournalLocation(loc)
      ensures loc in s.disk.blocks ==> loc in s'.disk.blocks && s'.disk.blocks[loc] == s.disk.blocks[loc]
      ensures loc in s'.disk.blocks ==> loc in s.disk.blocks
      {
        if overlap(s.disk.reqWrites[id].loc, loc) {
          assert ValidJournalLocation(s.disk.reqWrites[id].loc);
          assert false;
        }
      }
    }
  }

  lemma ProcessWritePreservesDiskCacheGraph(k: Constants, s: Variables, s': Variables, id: D.ReqId, indirectionTable: IndirectionTable)
  requires Inv(k, s)
  requires s.machine == s'.machine
  requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)

  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDiskQueue(indirectionTable, s.disk)
  requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
  requires M.OverlappingWritesEqForIndirectionTable(k.machine, s.machine, indirectionTable)

  ensures WFDisk(s'.disk.blocks)
  ensures WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk)
  ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
       == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache)
  {
    ProcessWrite_PreservesOtherTypes(k, s, s', id);

    var req := s.disk.reqWrites[id];
    if (ValidIndirectionTableLocation(req.loc)) {
      assert WFDisk(s'.disk.blocks);

      forall ref | ref in indirectionTable.locs
      ensures WFIndirectionTableRefWrtDiskQueue(indirectionTable, s'.disk, ref)
      ensures ValidNodeLocation(indirectionTable.locs[ref])
      {
        assert ValidNodeLocation(indirectionTable.locs[ref]);
        assert WFIndirectionTableRefWrtDiskQueue(indirectionTable, s.disk, ref);
      }

      assert WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    } else if (ValidNodeLocation(req.loc)) {
      /*if overlap(req.loc, Superblock1Location()) {
        overlappingLocsSameType(req.loc, Superblock1Location());
        assert false;
      }
      if overlap(req.loc, Superblock2Location()) {
        overlappingLocsSameType(req.loc, Superblock2Location());
        assert false;
      }

      if DiskHasSuperblock1(s.disk.blocks) {
        assert DiskHasSuperblock1(s'.disk.blocks);
        assert Superblock1OfDisk(s'.disk.blocks) == Superblock1OfDisk(s.disk.blocks);
      }
      if DiskHasSuperblock2(s.disk.blocks) {
        assert DiskHasSuperblock2(s'.disk.blocks);
        assert Superblock2OfDisk(s'.disk.blocks) == Superblock2OfDisk(s.disk.blocks);
      }
      assert SuperblockOfDisk(s'.disk.blocks) == SuperblockOfDisk(s.disk.blocks);
      assert s'.disk.blocks[SuperblockOfDisk(s'.disk.blocks).indirectionTableLoc]
          == s.disk.blocks[SuperblockOfDisk(s.disk.blocks).indirectionTableLoc];
      assert IndirectionTableOfDisk(s'.disk.blocks)
          == IndirectionTableOfDisk(s.disk.blocks);*/

      assert WFDisk(s'.disk.blocks);
      assert WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    } else if (ValidJournalLocation(req.loc)) {
      /*if overlap(req.loc, Superblock1Location()) {
        overlappingLocsSameType(req.loc, Superblock1Location());
        assert false;
      }
      if overlap(req.loc, Superblock2Location()) {
        overlappingLocsSameType(req.loc, Superblock2Location());
        assert false;
      }
      if overlap(req.loc, SuperblockOfDisk(s.disk.blocks).indirectionTableLoc) {
        overlappingLocsSameType(req.loc, SuperblockOfDisk(s.disk.blocks).indirectionTableLoc);
        assert false;
      }

      forall loc | ValidNodeLocation(loc)
      ensures loc in s.disk.blocks ==> loc in s'.disk.blocks && s'.disk.blocks[loc] == s.disk.blocks[loc];
      {
        if overlap(req.loc, loc) {
          overlappingLocsSameType(req.loc, loc);
          assert false;
        }
      }

      if DiskHasSuperblock1(s.disk.blocks) {
        assert DiskHasSuperblock1(s'.disk.blocks);
        assert Superblock1OfDisk(s'.disk.blocks) == Superblock1OfDisk(s.disk.blocks);
      }
      if DiskHasSuperblock2(s.disk.blocks) {
        assert DiskHasSuperblock2(s'.disk.blocks);
        assert Superblock2OfDisk(s'.disk.blocks) == Superblock2OfDisk(s.disk.blocks);
      }
      assert SuperblockOfDisk(s'.disk.blocks) == SuperblockOfDisk(s.disk.blocks);
      assert s'.disk.blocks[SuperblockOfDisk(s'.disk.blocks).indirectionTableLoc]
          == s.disk.blocks[SuperblockOfDisk(s.disk.blocks).indirectionTableLoc];
      assert IndirectionTableOfDisk(s'.disk.blocks)
          == IndirectionTableOfDisk(s.disk.blocks);*/

      assert WFDisk(s'.disk.blocks);
      assert WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    } else if (ValidSuperblock1Location(req.loc)) {
      assert WFDisk(s'.disk.blocks);
      assert WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    } else if (ValidSuperblock2Location(req.loc)) {
      assert WFDisk(s'.disk.blocks);
      assert WFIndirectionTableWrtDiskQueue(indirectionTable, s'.disk);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    }
  }

  lemma DiskCacheGraphEqDiskGraph(k: Constants, s: Variables, indirectionTable: IndirectionTable)
  requires Inv(k, s)
  requires s.machine.Ready?
  requires M.WFCompleteIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, s.disk.blocks)
  requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
  requires disjointWritesFromIndirectionTable(s.machine.outstandingBlockWrites, indirectionTable)
  ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
       == DiskGraph(indirectionTable, s.disk.blocks)
  {
    /*forall ref | ref in indirectionTable.graph
    ensures RefMapOfDisk(indirectionTable, s.disk.blocks)[ref]
        == DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, ref)
    {
      assert QueueLookupIdByLocation(s.disk.reqWrites, indirectionTable.locs[ref]).None?;
    }*/
  }

  lemma ProcessWritePreservesGraphs(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)

    ensures WFDisk(s'.disk.blocks)
    ensures WFIndirectionTableWrtDisk(IndirectionTableOfDisk(s'.disk.blocks), s'.disk.blocks)
    ensures s.machine.Ready? ==> WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk)
    ensures s'.machine.Ready? && s'.machine.frozenIndirectionTable.Some? ==> WFIndirectionTableWrtDiskQueue(s'.machine.frozenIndirectionTable.value, s'.disk)

    ensures (
      || PersistentGraph(k, s') == PersistentGraph(k, s)
      || Some(PersistentGraph(k, s')) == FrozenGraphOpt(k, s)
    )
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
  {
    if (s.machine.frozenIndirectionTable.Some?) { 
      ProcessWritePreservesDiskCacheGraph(k, s, s', id, s.machine.frozenIndirectionTable.value);
    }
    ProcessWritePreservesDiskCacheGraph(k, s, s', id, s.machine.ephemeralIndirectionTable);

    ProcessWrite_PreservesOtherTypes(k, s, s', id);

    var req := s.disk.reqWrites[id];
    if (Some(id) == s.machine.superblockWrite) {
      if (s.machine.frozenIndirectionTableLoc.Some?
          && s.machine.newSuperblock.value.indirectionTableLoc == s.machine.frozenIndirectionTableLoc.value) {
        var indirectionTable := s.machine.frozenIndirectionTable.value;
        assert WFIndirectionTableWrtDisk(indirectionTable, s.disk.blocks);
        assert disjointWritesFromIndirectionTable(s.machine.outstandingBlockWrites, indirectionTable);
        DiskCacheGraphEqDiskGraph(k, s, indirectionTable);

        assert FrozenGraph(k, s)
            == DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
            == DiskGraph(s.machine.frozenIndirectionTable.value, s.disk.blocks)
            == PersistentGraph(k, s');
      } else {
        assert WFIndirectionTableWrtDisk(IndirectionTableOfDisk(s'.disk.blocks), s'.disk.blocks);

        calc {
          PersistentGraph(k, s);
          DiskGraph(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks);
          DiskGraph(IndirectionTableOfDisk(s'.disk.blocks), s'.disk.blocks);
          PersistentGraph(k, s');
        }
      }
    } else {
      var indirectionTable := IndirectionTableOfDisk(s.disk.blocks);

      /*forall ref | ref in indirectionTable.graph
      ensures RefMapOfDisk(indirectionTable, s.disk.blocks)[ref]
           == RefMapOfDisk(indirectionTable, s'.disk.blocks)[ref]
      {
        assert RecordedWriteRequest(k, s, id, req.loc, req.sector);
        assert CorrectInflightBlockWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, req.loc);
        assert indirectionTable.locs[ref] != req.loc;
      }*/

      assert WFIndirectionTableWrtDisk(
          IndirectionTableOfDisk(s.disk.blocks),
          s'.disk.blocks);
      assert WFIndirectionTableWrtDisk(
          IndirectionTableOfDisk(s'.disk.blocks),
          s'.disk.blocks);

      assert PersistentGraph(k, s)
          == DiskGraph(IndirectionTableOfDisk(s.disk.blocks), s.disk.blocks)
          == DiskGraph(IndirectionTableOfDisk(s.disk.blocks), s'.disk.blocks)
          == DiskGraph(IndirectionTableOfDisk(s'.disk.blocks), s'.disk.blocks)
          == PersistentGraph(k, s');
    }
  }

  lemma ProcessWritePreservesInv(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)
    ensures Inv(k, s')
  {
    ProcessWritePreservesGraphs(k, s, s', id);
    ProcessWrite_PreservesOtherTypes(k, s, s', id);
  }

  lemma DiskInternalStepPreservesInv(k: Constants, s: Variables, s': Variables, step: D.InternalStep)
    requires Inv(k, s)
    requires DiskInternal(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case ProcessReadStep(id) => ProcessReadPreservesInv(k, s, s', id);
      case ProcessReadFailureStep(id) => ProcessReadFailurePreservesInv(k, s, s', id);
      case ProcessWriteStep(id) => ProcessWritePreservesInv(k, s, s', id);
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Crash(k, s, s')
    ensures Inv(k, s')
  {
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop, machineStep) => MachineStepPreservesInv(k, s, s', dop, machineStep);
      case DiskInternalStep(step) => DiskInternalStepPreservesInv(k, s, s', step);
      case CrashStep => CrashStepPreservesInv(k, s, s');
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInv(k, s, s', step);
  }

  /*lemma ReadReqIdIsValid(k: Constants, s: Variables, id: D.ReqId)
  requires Inv(k, s)
  requires id in s.disk.reqReads
  ensures s.disk.reqReads[id].loc in s.disk.blocks
  {
  }*/
}
