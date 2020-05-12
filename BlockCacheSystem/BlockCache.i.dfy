include "../Betree/Betree.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../Betree/Graph.i.dfy"
include "../BlockCacheSystem/BlockDisk.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../Versions/VOp.i.dfy"

//
// A BlockCache implements the BlockInterface by caching over an
// BlockDisk. At this layer, the disk provides high-level sectors
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
  import opened SectorType
  import opened ViewOp

  import Disk = BlockDisk

  type ReqId = Disk.ReqId
  datatype Constants = Constants()

  type DiskOp = Disk.DiskOp

  // BlockCache stuff

  datatype OutstandingWrite = OutstandingWrite(ref: Reference, loc: Location)
  datatype OutstandingRead = OutstandingRead(ref: Reference)

  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable,
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,

        persistentIndirectionTableLoc: Location,
        frozenIndirectionTableLoc: Option<Location>,

        outstandingIndirectionTableWrite: Option<ReqId>,
        outstandingBlockWrites: map<ReqId, OutstandingWrite>,
        outstandingBlockReads: map<ReqId, OutstandingRead>,

        cache: map<Reference, Node>
      )

    | LoadingIndirectionTable(
        indirectionTableLoc: Location,
        indirectionTableRead: Option<ReqId>
      )

    | Unready

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

  datatype Step =
    | WriteBackNodeReqStep(ref: Reference)
    | WriteBackNodeRespStep
    | WriteBackIndirectionTableReqStep
    | WriteBackIndirectionTableRespStep
    | UnallocStep(ref: Reference)
    | PageInNodeReqStep(ref: Reference)
    | PageInNodeRespStep
    | PageInIndirectionTableReqStep
    | PageInIndirectionTableRespStep
    | ReceiveLocStep
    | EvictStep(ref: Reference)
    | FreezeStep
    | CleanUpStep
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

  predicate WriteBackNodeReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
  {
    && vop.StatesInternalOp?

    && dop.ReqWriteNodeOp?
    && s.Ready?
    && ref in s.cache
    && ValidNodeLocation(dop.reqWriteNode.loc)
    && dop.reqWriteNode.node == s.cache[ref]
    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    // TODO I don't think we really need this.
    && s.outstandingIndirectionTableWrite.None?

    && ValidAllocation(s, dop.reqWriteNode.loc)

    && s'.ephemeralIndirectionTable == assignRefToLocation(s.ephemeralIndirectionTable, ref, dop.reqWriteNode.loc)

    && (s.frozenIndirectionTable.Some? ==> (
      s'.frozenIndirectionTable == Some(assignRefToLocation(s.frozenIndirectionTable.value, ref, dop.reqWriteNode.loc)))
    )
    && (s.frozenIndirectionTable.None? ==> s'.frozenIndirectionTable.None?)

    && s'.cache == s.cache
    && s'.outstandingBlockWrites == s.outstandingBlockWrites[dop.id := OutstandingWrite(ref, dop.reqWriteNode.loc)]
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.persistentIndirectionTableLoc == s.persistentIndirectionTableLoc
  }

  predicate WriteBackNodeResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.StatesInternalOp?

    && dop.RespWriteNodeOp?
    && s.Ready?
    && dop.id in s.outstandingBlockWrites
    && s' == s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, dop.id))
  }

  predicate WriteBackIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.StatesInternalOp?

    && dop.ReqWriteIndirectionTableOp?
    && s.Ready?
    && s.frozenIndirectionTable.Some?
    && var loc := dop.reqWriteIndirectionTable.loc;
    && ValidIndirectionTableLocation(loc)
    && dop.reqWriteIndirectionTable.indirectionTable == s.frozenIndirectionTable.value
    && s.frozenIndirectionTable.value.graph.Keys <= s.frozenIndirectionTable.value.locs.Keys

    // TODO This actually isn't necessary - we could write indirection
    // table and nodes in parallel
    && s.outstandingBlockWrites == map[]

    && s.frozenIndirectionTableLoc.None?
    && !overlap(
          loc,
          s.persistentIndirectionTableLoc)
    && s' == s
      .(outstandingIndirectionTableWrite := Some(dop.id))
      .(frozenIndirectionTableLoc := Some(loc))
  }

  predicate WriteBackIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && s.Ready?

    && vop.SendFrozenLocOp?
    && Some(vop.loc) == s.frozenIndirectionTableLoc

    && dop.RespWriteIndirectionTableOp?
    && s.outstandingIndirectionTableWrite == Some(dop.id)
    && s' == s.(outstandingIndirectionTableWrite := None)
  }

  predicate NoPredecessors(graph: map<Reference, seq<Reference>>, ref: Reference)
  {
    forall r | r in graph :: ref !in graph[r]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
  {
    && vop.AdvanceOp?
    && vop.uiop.NoOp?

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

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.persistentIndirectionTableLoc == s.persistentIndirectionTableLoc
  }

  predicate PageInNodeReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
  {
    && vop.StatesInternalOp?

    && dop.ReqReadNodeOp?
    && s.Ready?
    && IsAllocated(s, ref)
    && ref in s.ephemeralIndirectionTable.locs
    && ref !in s.cache
    && s.ephemeralIndirectionTable.locs[ref] == dop.loc
    && OutstandingRead(ref) !in s.outstandingBlockReads.Values
    && s' == s.(outstandingBlockReads := s.outstandingBlockReads[dop.id := OutstandingRead(ref)])
  }

  predicate PageInNodeResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.StatesInternalOp?

    && dop.RespReadNodeOp?
    && s.Ready?
    && dop.id in s.outstandingBlockReads
    && var ref := s.outstandingBlockReads[dop.id].ref;
    && ref !in s.cache
    && dop.node.Some?
    && var block := dop.node.value;
    && ref in s.ephemeralIndirectionTable.graph
    && (iset r | r in s.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)
    && s' == s.(cache := s.cache[ref := block])
              .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, dop.id))
  }

  predicate PageInIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.StatesInternalOp?

    && dop.ReqReadIndirectionTableOp?
    && s.LoadingIndirectionTable?

    && s.indirectionTableRead.None?
    && dop.loc == s.indirectionTableLoc
    && s' == s.(indirectionTableRead := Some(dop.id))
  }

  predicate PageInIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.StatesInternalOp?

    && dop.RespReadIndirectionTableOp?
    && s.LoadingIndirectionTable?
    && dop.indirectionTable.Some?
    && WFCompleteIndirectionTable(dop.indirectionTable.value)
    && AllLocationsForDifferentRefsDontOverlap(dop.indirectionTable.value)

    && s.indirectionTableRead == Some(dop.id)

    && s'.Ready?
    && s'.persistentIndirectionTable == dop.indirectionTable.value
    && s'.frozenIndirectionTable == None
    && s'.ephemeralIndirectionTable == dop.indirectionTable.value
    && s'.persistentIndirectionTableLoc == s.indirectionTableLoc
    && s'.frozenIndirectionTableLoc == None
    && s'.outstandingIndirectionTableWrite == None
    && s'.outstandingBlockWrites == map[]
    && s'.outstandingBlockReads == map[]
    && s'.cache == map[]
  }

  predicate ReceiveLoc(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && dop.NoDiskOp?

    && vop.SendPersistentLocOp?
    && ValidIndirectionTableLocation(vop.loc)

    && s.Unready?
    && s'.LoadingIndirectionTable?
    && s'.indirectionTableRead.None?
    && s'.indirectionTableLoc == vop.loc
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
  {
    && vop.StatesInternalOp?

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

  predicate Freeze(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.FreezeOp?

    && s.Ready?
    && dop.NoDiskOp?
    && s.outstandingIndirectionTableWrite.None?
    && s' ==
        s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
         .(frozenIndirectionTableLoc := None)
  }

  predicate CleanUp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.CleanUpOp?

    && s.Ready?
    && dop.NoDiskOp?
    && s.outstandingIndirectionTableWrite.None?
    && s.frozenIndirectionTableLoc.Some?
    && s.frozenIndirectionTable.Some?
    && s' == s.(persistentIndirectionTable := s.frozenIndirectionTable.value)
              .(persistentIndirectionTableLoc := s.frozenIndirectionTableLoc.value)
              .(frozenIndirectionTable := None)
              .(frozenIndirectionTableLoc := None)
  }

  predicate NoOp(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && (vop.StatesInternalOp? || vop.JournalInternalOp?
        || vop.PushSyncOp? || vop.PopSyncOp?)

    && (
      || dop.NoDiskOp?
      || (
        && dop.RespReadIndirectionTableOp?
      )
      || (
        && dop.RespReadNodeOp?
      )
      || (
        && dop.RespWriteIndirectionTableOp?
        && !(s.Ready? && s.outstandingIndirectionTableWrite == Some(dop.id))
      )
      || (
        && dop.RespWriteNodeOp?
        && !(s.Ready? && dop.id in s.outstandingBlockWrites)
      )
    )
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

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.persistentIndirectionTableLoc == s.persistentIndirectionTableLoc
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

    && s'.frozenIndirectionTableLoc == s.frozenIndirectionTableLoc
    && s'.persistentIndirectionTableLoc == s.persistentIndirectionTableLoc
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

  predicate Transaction(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ops: seq<Op>)
  {
    && vop.AdvanceOp?
    && dop.NoDiskOp?
    && s.Ready?
    && OpTransaction(k, s, s', ops)
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == Unready
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: Step) {
    match step {
      case WriteBackNodeReqStep(ref) => WriteBackNodeReq(k, s, s', dop, vop, ref)
      case WriteBackNodeRespStep => WriteBackNodeResp(k, s, s', dop, vop)
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReq(k, s, s', dop, vop)
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableResp(k, s, s', dop, vop)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, vop, ref)
      case PageInNodeReqStep(ref) => PageInNodeReq(k, s, s', dop, vop, ref)
      case PageInNodeRespStep => PageInNodeResp(k, s, s', dop, vop)
      case PageInIndirectionTableReqStep => PageInIndirectionTableReq(k, s, s', dop, vop)
      case PageInIndirectionTableRespStep => PageInIndirectionTableResp(k, s, s', dop, vop)
      case ReceiveLocStep => ReceiveLoc(k, s, s', dop, vop)
      case EvictStep(ref) => Evict(k, s, s', dop, vop, ref)
      case FreezeStep => Freeze(k, s, s', dop, vop)
      case CleanUpStep => CleanUp(k, s, s', dop, vop)
      case NoOpStep => NoOp(k, s, s', dop, vop)
      case TransactionStep(ops) => Transaction(k, s, s', dop, vop, ops)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp) {
    exists step: Step :: NextStep(k, s, s', dop, vop, step)
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
    && (s.frozenIndirectionTableLoc.Some? ==> s.frozenIndirectionTable.Some?)

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

    && ValidIndirectionTableLocation(s.persistentIndirectionTableLoc)
    && (s.frozenIndirectionTableLoc.Some? ==> (
      && ValidIndirectionTableLocation(s.frozenIndirectionTableLoc.value)
      && !overlap(
          s.frozenIndirectionTableLoc.value,
          s.persistentIndirectionTableLoc)
    ))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && (s.Ready? ==> InvReady(k, s))
    && (s.LoadingIndirectionTable? ==>
      && ValidIndirectionTableLocation(s.indirectionTableLoc)
    )
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma WriteBackNodeReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires WriteBackNodeReq(k, s, s', dop, vop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackNodeRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires WriteBackNodeResp(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires WriteBackIndirectionTableReq(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires WriteBackIndirectionTableResp(k, s, s', dop, vop)
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

  lemma OpTransactionStepPreservesInv(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
    requires Inv(k, s)
    requires OpTransaction(k, s, s', ops)
    ensures Inv(k, s')
    decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      OpPreservesInv(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := SplitTransaction(k, s, s', ops);
      OpTransactionStepPreservesInv(k, s, smid, ops1);
      OpTransactionStepPreservesInv(k, smid, s', ops2);
    }
  }


  lemma TransactionStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ops: seq<Op>)
    requires Inv(k, s)
    requires Transaction(k, s, s', dop, vop, ops)
    ensures Inv(k, s')
    decreases |ops|
  {
    OpTransactionStepPreservesInv(k, s, s', ops);
  }

  lemma UnallocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires Unalloc(k, s, s', dop, vop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInNodeReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires PageInNodeReq(k, s, s', dop, vop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInNodeRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires PageInNodeResp(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires PageInIndirectionTableReq(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires PageInIndirectionTableResp(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma ReceiveLocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires ReceiveLoc(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma EvictStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires Evict(k, s, s', dop, vop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma FreezeStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires Freeze(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma CleanUpStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires CleanUp(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', dop, vop, step)
    ensures Inv(k, s')
  {
    match step {
      case WriteBackNodeReqStep(ref) => WriteBackNodeReqStepPreservesInv(k, s, s', dop, vop, ref);
      case WriteBackNodeRespStep => WriteBackNodeRespStepPreservesInv(k, s, s', dop, vop);
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReqStepPreservesInv(k, s, s', dop, vop);
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableRespStepPreservesInv(k, s, s', dop, vop);
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, vop, ref);
      case PageInNodeReqStep(ref) => PageInNodeReqStepPreservesInv(k, s, s', dop, vop, ref);
      case PageInNodeRespStep => PageInNodeRespStepPreservesInv(k, s, s', dop, vop);
      case PageInIndirectionTableReqStep => PageInIndirectionTableReqStepPreservesInv(k, s, s', dop, vop);
      case PageInIndirectionTableRespStep => PageInIndirectionTableRespStepPreservesInv(k, s, s', dop, vop);
      case ReceiveLocStep => ReceiveLocStepPreservesInv(k, s, s', dop, vop);
      case EvictStep(ref) => EvictStepPreservesInv(k, s, s', dop, vop, ref);
      case FreezeStep => FreezeStepPreservesInv(k, s, s', dop, vop);
      case CleanUpStep => CleanUpStepPreservesInv(k, s, s', dop, vop);
      case NoOpStep => { }
      case TransactionStep(ops) => TransactionStepPreservesInv(k, s, s', dop, vop, ops);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires Next(k, s, s', dop, vop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', dop, vop, step);
    NextStepPreservesInv(k, s, s', dop, vop, step);
  }
}
