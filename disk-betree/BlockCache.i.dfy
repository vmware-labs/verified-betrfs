include "Betree.i.dfy"
include "../lib/sequences.s.dfy"
include "../lib/Maps.s.dfy"
include "Graph.i.dfy"
include "AsyncSectorDiskModel.i.dfy"
include "PivotBetreeSpec.i.dfy"

abstract module BlockCache refines Transactable {
  import opened Maps
  import opened Options
  import opened NativeTypes
  import LBAType

  import Disk = AsyncSectorDisk

  type ReqId = Disk.ReqId
  type LBA = LBAType.LBA
  type Location = LBAType.Location
  datatype Constants = Constants()
  function method IndirectionTableLBA() : LBA { LBAType.IndirectionTableLBA() }
  function method IndirectionTableLocation() : Location { LBAType.IndirectionTableLocation() }

  // TODO make indirectionTable take up more than one block
  datatype IndirectionTable = IndirectionTable(
      locs: map<Reference, Location>,
      graph: map<Reference, seq<Reference>>)

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)

  type DiskOp = Disk.DiskOp<Sector>

  // BlockCache stuff

  datatype OutstandingWrite = OutstandingWrite(ref: Reference, loc: Location)
  datatype OutstandingRead = OutstandingRead(ref: Reference)

  datatype SyncReqStatus = State1 | State2 | State3

  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable,
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,

        outstandingIndirectionTableWrite: Option<ReqId>,
        outstandingBlockWrites: map<ReqId, OutstandingWrite>,
        outstandingBlockReads: map<ReqId, OutstandingRead>,
        syncReqs: map<uint64, SyncReqStatus>,

        cache: map<Reference, Node>)
    | Unready(
        outstandingIndirectionTableRead: Option<ReqId>,
        syncReqs: map<uint64, SyncReqStatus>
        )

  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralIndirectionTable.graph
  }

  predicate method ValidLBAForNode(lba: LBA)
  {
    && LBAType.ValidAddr(lba)
    && lba != IndirectionTableLBA()
  }
  predicate method ValidLocationForNode(loc: Location)
  {
    && ValidLBAForNode(loc.addr)
    && LBAType.ValidLocation(loc)
  }

  predicate method GraphClosed(graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in graph ::
      forall succ | succ in graph[ref] ::
        succ in graph
  }

  // WF IndirectionTable which must have all LBAs filled in
  predicate WFCompleteIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall loc | loc in indirectionTable.locs.Values :: ValidLocationForNode(loc))
    && indirectionTable.graph.Keys == indirectionTable.locs.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  // TODO this may be necessary for an assume in Marshalling, but may be solved by the weights branch
  // predicate IndirectionTableGraphHasUniqueRefsInAdjList(graph: map<Reference, seq<Reference>>)
  // {
  //   && (forall ref | ref in graph :: forall i: nat, j: nat | i <= j < |graph[ref]| :: graph[i] == graph[j] ==> i == j)
  // }

  // WF IndirectionTable which might not have all LBAs filled in
  predicate WFIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall loc | loc in indirectionTable.locs.Values :: ValidLocationForNode(loc))
    && indirectionTable.locs.Keys <= indirectionTable.graph.Keys
    // TODO this may be necessary for an assume in Marshalling, but may be solved by the weights branch
    // && IndirectionTableGraphHasUniqueRefsInAdjList(indirectionTable.graph)
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  // TODO this may be necessary for an assume in Marshalling, but may be solved by the weights branch
  // lemma GraphClosedImpliesSuccsContainedInGraphKeys(graph: map<Reference, seq<Reference>>)
  // requires GraphClosed(graph)
  // requires IndirectionTableGraphHasUniqueRefsInAdjList(graph)
  // ensures forall ref | ref in graph :: (set r | r in graph[ref]) <= graph.Keys
  // {
  // }

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

  datatype Step =
    | WriteBackReqStep(ref: Reference)
    | WriteBackRespStep
    | WriteBackIndirectionTableReqStep
    | WriteBackIndirectionTableRespStep
    | UnallocStep(ref: Reference)
    | PageInReqStep(ref: Reference)
    | PageInRespStep
    | PageInIndirectionTableReqStep
    | PageInIndirectionTableRespStep
    | EvictStep(ref: Reference)
    | FreezeStep
    | PushSyncReqStep(id: uint64)
    | PopSyncReqStep(id: uint64)
    | NoOpStep
    | TransactionStep(ops: seq<Op>)

  function method assignRefToLocation(indirectionTable: IndirectionTable, ref: Reference, loc: Location) : IndirectionTable
  {
    IndirectionTable(
      if ref in indirectionTable.graph && ref !in indirectionTable.locs then indirectionTable.locs[ref := loc] else indirectionTable.locs,
      indirectionTable.graph
    )
  }

  predicate method OutstandingBlockReadsDoesNotHaveRef(outstandingBlockReads: map<ReqId, OutstandingRead>, ref: Reference)
  {
    forall reqId | reqId in outstandingBlockReads :: outstandingBlockReads[reqId].ref != ref
  }

  predicate WriteBackReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.ReqWriteOp?
    && s.Ready?
    && ref in s.cache
    && ValidLocationForNode(dop.reqWrite.loc)
    && dop.reqWrite.sector == SectorBlock(s.cache[ref])
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
    && dop.reqWrite.loc == IndirectionTableLocation()
    && s.frozenIndirectionTable.Some?
    && dop.reqWrite.sector == SectorIndirectionTable(s.frozenIndirectionTable.value)
    && s.frozenIndirectionTable.value.graph.Keys <= s.frozenIndirectionTable.value.locs.Keys
    && s.outstandingIndirectionTableWrite.None?
    && s.outstandingBlockWrites == map[]
    && s.frozenIndirectionTable.Some?
    && s' == s.(outstandingIndirectionTableWrite := Some(dop.id))
  }

  function method syncReqs3to2(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State3 then State2 else syncReqs[id])
  }

  function method syncReqs2to1(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State2 then State1 else syncReqs[id])
  }

  predicate WriteBackIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteOp?
    && s.Ready?
    && s.outstandingIndirectionTableWrite.Some?
    && s.frozenIndirectionTable.Some?
    && dop.id == s.outstandingIndirectionTableWrite.value
    && s' == s.(outstandingIndirectionTableWrite := None)
              .(frozenIndirectionTable := None)
              .(persistentIndirectionTable := s.frozenIndirectionTable.value)
              .(syncReqs := syncReqs2to1(s.syncReqs))
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
    && dop.respRead.sector.value.SectorBlock?
    && var block := dop.respRead.sector.value.block;
    && ref in s.ephemeralIndirectionTable.graph
    && (iset r | r in s.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)
    && s' == s.(cache := s.cache[ref := block])
              .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, dop.id))
  }

  predicate PageInIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadOp?
    && s.Unready?
    && s.outstandingIndirectionTableRead.None?
    && dop.reqRead.loc == IndirectionTableLocation()
    && s' == Unready(Some(dop.id), s.syncReqs)
  }

  predicate PageInIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadOp?
    && s.Unready?
    && s.outstandingIndirectionTableRead == Some(dop.id)
    && dop.respRead.sector.Some?
    && dop.respRead.sector.value.SectorIndirectionTable?
    && WFCompleteIndirectionTable(dop.respRead.sector.value.indirectionTable)
    && AllLocationsForDifferentRefsDontOverlap(dop.respRead.sector.value.indirectionTable)
    && s' == Ready(dop.respRead.sector.value.indirectionTable, None, dop.respRead.sector.value.indirectionTable, None, map[], map[], s.syncReqs, map[])
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
    && s' ==
        s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
         .(syncReqs := syncReqs3to2(s.syncReqs))
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
    s == Unready(None, map[])
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteBackReqStep(ref) => WriteBackReq(k, s, s', dop, ref)
      case WriteBackRespStep => WriteBackResp(k, s, s', dop)
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReq(k, s, s', dop)
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableResp(k, s, s', dop)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, ref)
      case PageInReqStep(ref) => PageInReq(k, s, s', dop, ref)
      case PageInRespStep => PageInResp(k, s, s', dop)
      case PageInIndirectionTableReqStep => PageInIndirectionTableReq(k, s, s', dop)
      case PageInIndirectionTableRespStep => PageInIndirectionTableResp(k, s, s', dop)
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
    indirectionTable.locs[r1] == indirectionTable.locs[r2] ==> r1 == r2
  }

  predicate AllLocationsForDifferentRefsDontOverlap(indirectionTable: IndirectionTable)
  {
    forall r1, r2 | r1 in indirectionTable.locs && r2 in indirectionTable.locs ::
        LocationsForDifferentRefsDontOverlap(indirectionTable, r1, r2)
  }

  predicate OutstandingWriteValidLocation(outstandingBlockWrites: map<ReqId, OutstandingWrite>)
  {
    forall id | id in outstandingBlockWrites ::
      LBAType.ValidLocation(outstandingBlockWrites[id].loc)
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
    && OutstandingWriteValidLocation(s.outstandingBlockWrites)

    // This isn't necessary for the other invariants in this file,
    // but it is useful for the implementation.
    && AllLocationsForDifferentRefsDontOverlap(s.ephemeralIndirectionTable)

    && (s.frozenIndirectionTable.Some? ==> (
      && WFIndirectionTable(s.frozenIndirectionTable.value)
      && IndirectionTableCacheConsistent(s.frozenIndirectionTable.value, s.cache)
      && OverlappingWritesEqForIndirectionTable(k, s, s.frozenIndirectionTable.value)
    ))

    && (s.outstandingIndirectionTableWrite.Some? ==> (
      && s.frozenIndirectionTable.Some?
      && WFCompleteIndirectionTable(s.frozenIndirectionTable.value)
    ))
  }

  predicate Inv(k: Constants, s: Variables)
  {
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
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, ref);
      case PageInReqStep(ref) => PageInReqStepPreservesInv(k, s, s', dop, ref);
      case PageInRespStep => PageInRespStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableReqStep => PageInIndirectionTableReqStepPreservesInv(k, s, s', dop);
      case PageInIndirectionTableRespStep => PageInIndirectionTableRespStepPreservesInv(k, s, s', dop);
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

module {:extern} BetreeGraphBlockCache refines BlockCache {
  import G = PivotBetreeGraph
}
