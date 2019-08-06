include "Betree.dfy"
include "../lib/sequences.s.dfy"
include "../lib/Maps.s.dfy"
include "Graph.dfy"
include "AsyncSectorDiskModel.dfy"
include "PivotBetreeSpec.dfy"

module LBAType {
  import NativeTypes

  type LBA(==,!new) = NativeTypes.uint64
  function method IndirectionTableLBA() : LBA { 0 }

  function method toLBA(i: NativeTypes.uint64) : LBA{ i }
  function method toUint64(i: LBA) : NativeTypes.uint64 { i }

  function method BlockSize() : NativeTypes.uint64 { 8*1024*1024 }
  predicate method {:opaque} ValidAddr(addr: LBA) {
    //exists j: int :: j * BlockSize() as int == addr as int
    addr as int % BlockSize() as int == 0
  }
  lemma ValidAddrDivisor(addr: LBA) returns (i: int)
  requires ValidAddr(addr);
  ensures i * BlockSize() as int == addr as int
  {
    reveal_ValidAddr();
    i := addr as int / BlockSize() as int;
  }

  export S provides LBA, IndirectionTableLBA, toLBA, toUint64, NativeTypes, ValidAddr
      reveals BlockSize
  export extends S
	export Internal reveals *
}

abstract module BlockCache refines Transactable {
  import opened Maps
  import opened Options
  import LBAType

  import Disk = AsyncSectorDisk

  type ReqId = Disk.ReqId
  type LBA = LBAType.LBA
  datatype Constants = Constants()
  function method IndirectionTableLBA() : LBA { LBAType.IndirectionTableLBA() }

  // TODO make indirectionTable take up more than one block
  datatype IndirectionTable = IndirectionTable(
      lbas: map<Reference, LBA>,
      graph: map<Reference, seq<Reference>>)

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)

  type DiskOp = Disk.DiskOp<LBA, Sector>

  // BlockCache stuff

  datatype OutstandingWrite = OutstandingWrite(ref: Reference, lba: LBA)
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
        syncReqs: map<int, SyncReqStatus>,

        cache: map<Reference, Node>)
    | Unready(
        outstandingIndirectionTableRead: Option<ReqId>,
        syncReqs: map<int, SyncReqStatus>
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

  predicate method GraphClosed(graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in graph ::
      forall succ | succ in graph[ref] ::
        succ in graph
  }

  // WF IndirectionTable which must have all LBAs filled in
  predicate WFCompleteIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall lba | lba in indirectionTable.lbas.Values :: ValidLBAForNode(lba))
    && indirectionTable.graph.Keys == indirectionTable.lbas.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  // WF IndirectionTable which might not have all LBAs filled in
  predicate WFIndirectionTable(indirectionTable: IndirectionTable)
  {
    && (forall lba | lba in indirectionTable.lbas.Values :: ValidLBAForNode(lba))
    && indirectionTable.lbas.Keys <= indirectionTable.graph.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  predicate LBAFree(s: Variables, lba: LBA)
  requires s.Ready?
  {
    && lba !in s.persistentIndirectionTable.lbas.Values
    && lba !in s.ephemeralIndirectionTable.lbas.Values
    && (s.frozenIndirectionTable.Some? ==>
        lba !in s.frozenIndirectionTable.value.lbas.Values)
    && (forall id | id in s.outstandingBlockWrites ::
        s.outstandingBlockWrites[id].lba != lba)
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
    | PushSyncReqStep(id: int)
    | PopSyncReqStep(id: int)
    | NoOpStep
    | TransactionStep(ops: seq<Op>)

  function method AssignRefToLBA(indirectionTable: IndirectionTable, ref: Reference, lba: LBA) : IndirectionTable
  {
    IndirectionTable(
      if ref in indirectionTable.graph then indirectionTable.lbas[ref := lba] else indirectionTable.lbas,
      indirectionTable.graph
    )
  }

  predicate WriteBackReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.ReqWriteOp?
    && s.Ready?
    && ref in s.cache
    && ValidLBAForNode(dop.reqWrite.lba)
    && LBAFree(s, dop.reqWrite.lba)
    && dop.reqWrite.sector == SectorBlock(s.cache[ref])
    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    && s.outstandingIndirectionTableWrite.None?

    && ref !in s.ephemeralIndirectionTable.lbas
    && s'.ephemeralIndirectionTable == AssignRefToLBA(s.ephemeralIndirectionTable, ref, dop.reqWrite.lba)

    && (s.frozenIndirectionTable.Some? ==> (
      && ref !in s.frozenIndirectionTable.value.lbas
      && s'.frozenIndirectionTable == Some(AssignRefToLBA(s.frozenIndirectionTable.value, ref, dop.reqWrite.lba))
    ))
    && (s.frozenIndirectionTable.None? ==> s'.frozenIndirectionTable.None?)

    && s'.cache == s.cache
    && s'.outstandingBlockWrites == s.outstandingBlockWrites[dop.id := OutstandingWrite(ref, dop.reqWrite.lba)]
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
    && dop.reqWrite.lba == IndirectionTableLBA()
    && s.frozenIndirectionTable.Some?
    && dop.reqWrite.sector == SectorIndirectionTable(s.frozenIndirectionTable.value)
    && s.frozenIndirectionTable.value.graph.Keys <= s.frozenIndirectionTable.value.lbas.Keys
    && s.outstandingIndirectionTableWrite.None?
    && s.outstandingBlockWrites == map[]
    && s.frozenIndirectionTable.Some?
    && s' == s.(outstandingIndirectionTableWrite := Some(dop.id))
  }

  function method syncReqs3to2(syncReqs: map<int, SyncReqStatus>) : map<int, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State3 then State2 else syncReqs[id])
  }

  function method syncReqs2to1(syncReqs: map<int, SyncReqStatus>) : map<int, SyncReqStatus>
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

  function method OutstandingBlockReadsRemoveRef(outstandingBlockReads: map<ReqId, OutstandingRead>, ref: Reference) : map<ReqId, OutstandingRead>
  {
    map reqId | reqId in outstandingBlockReads && outstandingBlockReads[reqId].ref != ref :: outstandingBlockReads[reqId]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.NoDiskOp?
    && s.Ready?

    && IsAllocated(s, ref)

    // We can only dealloc this if nothing is pointing to it.
    && ref != G.Root()
    && NoPredecessors(s.ephemeralIndirectionTable.graph, ref)

    && (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.lbas)

    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.lbas == MapRemove(s.ephemeralIndirectionTable.lbas, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && s'.ephemeralIndirectionTable.graph == MapRemove(s.ephemeralIndirectionTable.graph, {ref})

    && s'.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
    && s'.outstandingBlockWrites == s.outstandingBlockWrites
    && s'.outstandingBlockReads == OutstandingBlockReadsRemoveRef(s.outstandingBlockReads, ref)
    && s'.frozenIndirectionTable == s.frozenIndirectionTable
    && s'.syncReqs == s.syncReqs
  }

  predicate PageInReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && dop.ReqReadOp?
    && s.Ready?
    && IsAllocated(s, ref)
    && ref in s.ephemeralIndirectionTable.lbas
    && ref !in s.cache
    && s.ephemeralIndirectionTable.lbas[ref] == dop.reqRead.lba
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
    && dop.reqRead.lba == IndirectionTableLBA()
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
    && s' == Ready(dop.respRead.sector.value.indirectionTable, None, dop.respRead.sector.value.indirectionTable, None, map[], map[], s.syncReqs, map[])
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?
    && ref in s.cache
    && (ref in s.ephemeralIndirectionTable.graph ==>
      && ref in s.ephemeralIndirectionTable.lbas
      && OutstandingWrite(ref, s.ephemeralIndirectionTable.lbas[ref]) !in s.outstandingBlockWrites.Values
    )
    && (s.frozenIndirectionTable.Some? ==>
        ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.lbas)
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

  predicate PushSyncReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
  {
    && dop.NoDiskOp?
    && id !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[id := State3])
  }

  predicate PopSyncReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
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

    && s'.ephemeralIndirectionTable.lbas == MapRemove(s.ephemeralIndirectionTable.lbas, {ref})

    && BlockPointsToValidReferences(block, s.ephemeralIndirectionTable.graph)

    && (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.lbas)
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

    && s'.ephemeralIndirectionTable.lbas == s.ephemeralIndirectionTable.lbas

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
      case PushSyncReqStep(id: int) => PushSyncReq(k, s, s', dop, id)
      case PopSyncReqStep(id: int) => PopSyncReq(k, s, s', dop, id)
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
    && indirectionTable.graph.Keys <= cache.Keys + indirectionTable.lbas.Keys
  }

  predicate EphemeralTableEntriesInCacheOrNotBeingWritten(k: Constants, s: Variables)
  requires s.Ready?
  requires IndirectionTableCacheConsistent(s.ephemeralIndirectionTable, s.cache)
  {
    forall ref | ref in s.ephemeralIndirectionTable.graph ::
      ref !in s.cache ==> OutstandingWrite(ref, s.ephemeralIndirectionTable.lbas[ref]) !in s.outstandingBlockWrites.Values
  }

  predicate OutstandingReadRefsUnique(outstandingBlockReads: map<ReqId, OutstandingRead>)
  {
    forall id1, id2 | id1 in outstandingBlockReads && id2 in outstandingBlockReads && outstandingBlockReads[id1] == outstandingBlockReads[id2] ::
      id1 == id2
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

    && (s.frozenIndirectionTable.Some? ==> (
      && WFIndirectionTable(s.frozenIndirectionTable.value)
      && IndirectionTableCacheConsistent(s.frozenIndirectionTable.value, s.cache)
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

  lemma PushSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
    requires Inv(k, s)
    requires PushSyncReq(k, s, s', dop, id)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PopSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
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
