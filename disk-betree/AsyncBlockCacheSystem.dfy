include "AsyncBlockCache.dfy"

abstract module AsyncBlockCacheSystem {
  import M : AsyncBlockCache
  import D = AsyncDisk

  import opened Maps
  import opened Sequences
  import opened Options
  import opened AsyncDiskModelTypes

  type LBA = M.LBA
  type Sector = M.Sector
  type DiskOp = M.DiskOp

  type Constants = AsyncDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncDiskModelVariables<M.Variables, D.Variables<LBA, Sector>>

  type IndirectionTable = M.IndirectionTable
  type Reference = M.G.Reference
  type Node = M.G.Node
  type Op = M.Op

  predicate WFDisk(blocks: map<LBA, Sector>)
  {
    && var indirectionTableLBA := M.IndirectionTableLBA();
    && indirectionTableLBA in blocks
    && blocks[indirectionTableLBA].SectorIndirectionTable?
    && M.WFCompleteIndirectionTable(blocks[indirectionTableLBA].indirectionTable)
  }

  predicate WFIndirectionTableRefWrtDisk(indirectionTable: IndirectionTable, blocks: map<LBA,Sector>,
      ref: Reference)
  requires ref in indirectionTable.lbas
  {
    && indirectionTable.lbas[ref] in blocks
    && blocks[indirectionTable.lbas[ref]].SectorBlock?
  }

  predicate WFIndirectionTableWrtDisk(indirectionTable: IndirectionTable, blocks: map<LBA, Sector>)
  {
    && (forall ref | ref in indirectionTable.lbas :: WFIndirectionTableRefWrtDisk(indirectionTable, blocks, ref))
  }

  function DiskIndirectionTable(blocks: map<LBA, Sector>) : IndirectionTable
  requires WFDisk(blocks)
  {
    blocks[M.IndirectionTableLBA()].indirectionTable
  }

  function RefMapOfDisk(
      indirectionTable: IndirectionTable,
      blocks: map<LBA, Sector>) : map<Reference, Node>
  requires WFDisk(blocks)
  requires WFIndirectionTableWrtDisk(indirectionTable, blocks)
  {
    map ref | ref in indirectionTable.lbas :: blocks[indirectionTable.lbas[ref]].block
  }

  function Graph(refs: set<Reference>, refmap: map<Reference, Node>) : map<Reference, Node>
  requires refs <= refmap.Keys
  {
    map ref | ref in refs :: refmap[ref]
  }

  function DiskGraph(indirectionTable: IndirectionTable, blocks: map<LBA, Sector>) : map<Reference, Node>
  requires WFDisk(blocks)
  requires M.WFCompleteIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, blocks)
  {
    Graph(indirectionTable.graph.Keys, RefMapOfDisk(indirectionTable, blocks))
  }

  function PersistentGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(s.disk.blocks)
  requires WFIndirectionTableWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
  {
    DiskGraph(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
  }

  function {:opaque} QueueLookupIdByLBA(reqWrites: map<D.ReqId, D.ReqWrite<LBA, Sector>>, lba: LBA) : (res : Option<D.ReqId>)
  ensures res.None? ==> forall id | id in reqWrites :: reqWrites[id].lba != lba
  ensures res.Some? ==> res.value in reqWrites && reqWrites[res.value].lba == lba
  {
    if id :| id in reqWrites && reqWrites[id].lba == lba then Some(id) else None
  }

  predicate WFReqWriteBlocks(reqWrites: map<D.ReqId, D.ReqWrite<LBA, Sector>>)
  {
    forall id | id in reqWrites && M.ValidLBAForNode(reqWrites[id].lba) ::
        reqWrites[id].sector.SectorBlock?
  }

  function DiskQueueCacheLookup(indirectionTable: IndirectionTable, disk: D.Variables<LBA,Sector>, cache: map<Reference, Node>, ref: Reference) : Node
  requires WFDisk(disk.blocks)
  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, disk.blocks)
  requires M.IndirectionTableCacheConsistent(indirectionTable, cache)
  requires WFReqWriteBlocks(disk.reqWrites)
  requires ref in indirectionTable.graph
  {
    if ref in indirectionTable.lbas then (
      if QueueLookupIdByLBA(disk.reqWrites, indirectionTable.lbas[ref]).Some? then
        disk.reqWrites[QueueLookupIdByLBA(disk.reqWrites, indirectionTable.lbas[ref]).value].sector.block
      else
        disk.blocks[indirectionTable.lbas[ref]].block
    ) else (
      cache[ref]
    )
  }

  function DiskCacheGraph(indirectionTable: IndirectionTable, disk: D.Variables<LBA,Sector>, cache: map<Reference, Node>) : map<Reference, Node>
  requires WFDisk(disk.blocks)
  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, disk.blocks)
  requires M.IndirectionTableCacheConsistent(indirectionTable, cache)
  requires WFReqWriteBlocks(disk.reqWrites)
  {
    map ref | ref in indirectionTable.graph :: DiskQueueCacheLookup(indirectionTable, disk, cache, ref)
  }

  function FrozenGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(s.disk.blocks)
  requires s.machine.Ready?
  requires s.machine.frozenIndirectionTable.Some?
  requires M.WFCompleteIndirectionTable(s.machine.frozenIndirectionTable.value)
  requires WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.blocks)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
  }

  function EphemeralGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires M.Inv(k.machine, s.machine)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  requires WFIndirectionTableWrtDisk(s.machine.ephemeralIndirectionTable, s.disk.blocks)
  requires WFReqWriteBlocks(s.disk.reqWrites)
  {
    DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
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
    && WFIndirectionTableWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && PersistentGraph(k, s).Keys == {M.G.Root()}
    && M.G.Successors(PersistentGraph(k, s)[M.G.Root()]) == iset{}
  }

  ////// Next

  datatype Step =
    | CommStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
  
  predicate Comm(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, dop)
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
      case CommStep(dop) => Comm(k, s, s', dop)
      case DiskInternalStep(step) => DiskInternal(k, s, s', step)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  ////// Invariants

  predicate IsCleanCacheEntry(k: Constants, s: Variables, ref: Reference)
  requires s.machine.Ready?
  requires ref in s.machine.cache
  {
    && ref in s.machine.ephemeralIndirectionTable.lbas
    && M.OutstandingWrite(ref, s.machine.ephemeralIndirectionTable.lbas[ref]) !in
        s.machine.outstandingBlockWrites.Values
  }

  predicate CleanCacheEntriesAreCorrect(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall ref | ref in s.machine.cache ::
      IsCleanCacheEntry(k, s, ref) ==>
      MapsTo(
          s.disk.blocks,
          s.machine.ephemeralIndirectionTable.lbas[ref],
          M.SectorBlock(s.machine.cache[ref]))
  }

  // Any outstanding read we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockRead(k: Constants, s: Variables, id: D.ReqId, ref: Reference)
  requires s.machine.Ready?
  {
    && ref in s.machine.ephemeralIndirectionTable.lbas
    && var lba := s.machine.ephemeralIndirectionTable.lbas[ref];
    && lba in s.disk.blocks
    && var sector := s.disk.blocks[lba];
    && !(id in s.disk.reqReads && id in s.disk.respReads)
    && (id in s.disk.reqReads ==> s.disk.reqReads[id] == D.ReqRead(lba))
    && (id in s.disk.respReads ==> s.disk.respReads[id] == D.RespRead(sector))
  }

  predicate CorrectInflightBlockReads(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall id | id in s.machine.outstandingBlockReads ::
      CorrectInflightBlockRead(k, s, id, s.machine.outstandingBlockReads[id].ref)
  }

  predicate CorrectInflightIndirectionTableReads(k: Constants, s: Variables)
  requires s.machine.Unready?
  {
    s.machine.outstandingIndirectionTableRead.Some? ==> (
      MapsTo(s.disk.reqReads,
        s.machine.outstandingIndirectionTableRead.value,
        D.ReqRead(M.IndirectionTableLBA())
      )
    )
  }

  // Any outstanding write we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockWrite(k: Constants, s: Variables, id: D.ReqId, ref: Reference, lba: LBA)
  requires s.machine.Ready?
  {
    && lba !in s.machine.persistentIndirectionTable.lbas.Values
    && (s.machine.frozenIndirectionTable.Some? ==>
        lba !in s.machine.frozenIndirectionTable.value.lbas.Values)

    && (forall r | r in s.machine.ephemeralIndirectionTable.lbas ::
        s.machine.ephemeralIndirectionTable.lbas[r] == lba ==> r == ref)

    && (s.machine.frozenIndirectionTable.Some? ==>
        forall r | r in s.machine.frozenIndirectionTable.value.lbas ::
        s.machine.frozenIndirectionTable.value.lbas[r] == lba ==> r == ref)

    && !(id in s.disk.reqWrites && id in s.disk.respWrites)
  }

  predicate CorrectInflightBlockWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall id | id in s.machine.outstandingBlockWrites ::
      CorrectInflightBlockWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, s.machine.outstandingBlockWrites[id].lba)
  }

  predicate CorrectInflightIndirectionTableWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    s.machine.outstandingIndirectionTableWrite.Some? ==> (
      && s.machine.frozenIndirectionTable.Some?
      && MapsTo(s.disk.reqWrites,
        s.machine.outstandingIndirectionTableWrite.value,
        D.ReqWrite(
          M.IndirectionTableLBA(),
          M.SectorIndirectionTable(
            s.machine.frozenIndirectionTable.value
          )
        )
      )
    )
  }

  // If there's a write in progress, then the in-memory state must know about it.

  predicate RecordedWriteRequest(k: Constants, s: Variables, id: D.ReqId, lba: LBA, sector: Sector)
  {
    && s.machine.Ready?
    && (match sector {
      case SectorIndirectionTable(indirectionTable) => (
        && s.machine.outstandingIndirectionTableWrite == Some(id)
        && s.machine.frozenIndirectionTable == Some(indirectionTable)
      )
      case SectorBlock(block) => (
        && id in s.machine.outstandingBlockWrites
      )
    })
  }

  predicate RecordedWriteRequests(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqWrites :: RecordedWriteRequest(k, s, id, s.disk.reqWrites[id].lba, s.disk.reqWrites[id].sector)
  }

  predicate Inv(k: Constants, s: Variables) {
    && M.Inv(k.machine, s.machine)
    && WFDisk(s.disk.blocks)
    && WFReqWriteBlocks(s.disk.reqWrites)
    && WFIndirectionTableWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && (s.machine.outstandingIndirectionTableWrite.Some? ==>
        && WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.blocks)
      )
      && s.machine.persistentIndirectionTable == DiskIndirectionTable(s.disk.blocks)
      && WFIndirectionTableWrtDisk(s.machine.ephemeralIndirectionTable, s.disk.blocks)
      && SuccessorsAgree(s.machine.ephemeralIndirectionTable.graph, EphemeralGraph(k, s))
      && NoDanglingPointers(EphemeralGraph(k, s))
      && CleanCacheEntriesAreCorrect(k, s)
      && CorrectInflightBlockReads(k, s)
      && CorrectInflightBlockWrites(k, s)
      && CorrectInflightIndirectionTableWrites(k, s)
    )
    && (s.machine.Unready? ==>
      && CorrectInflightIndirectionTableReads(k, s)
    )
    && RecordedWriteRequests(k, s)
  }

  ////// Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma WriteBackReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma WriteBackReqStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackReqStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma WriteBackRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma WriteBackRespStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackRespStepPreservesGraphs(k, s, s', dop);
  }

  lemma WriteBackIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
  }

  lemma WriteBackIndirectionTableReqStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
  }

  lemma WriteBackIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
  }

  lemma WriteBackIndirectionTableRespStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendWrite(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
  }

  lemma DirtyStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  lemma AllocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  lemma OpPreservesInvariant(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires M.OpStep(k.machine, s.machine, s'.machine, op)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
    match op {
      case WriteOp(ref, block) => DirtyStepPreservesInvariant(k, s, s', ref, block);
      case AllocOp(ref, block) => AllocStepPreservesInvariant(k, s, s', ref, block);
    }
  }

  lemma TransactionStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ops: seq<Op>)
    requires Inv(k, s)
    requires M.Transaction(k.machine, s.machine, s'.machine, dop, ops)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
    decreases |ops|
  {
    if |ops| == 0 {
    } else if |ops| == 1 {
      OpPreservesInvariant(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := M.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      TransactionStepPreservesInvariant(k, s, AsyncDiskModelVariables(smid, s.disk), dop, ops1);
      TransactionStepPreservesInvariant(k, AsyncDiskModelVariables(smid, s.disk), s', dop, ops2);
    }
  }

  lemma UnallocStepPreservesPersistentGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
  {
  }

  lemma UnallocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
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
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma PageInReqStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageInReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInReqStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma PageInRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendRead(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma PageInRespStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInResp(k.machine, s.machine, s'.machine, dop)
    requires D.SendRead(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInRespStepPreservesGraphs(k, s, s', dop);
  }


  /*
  lemma PageInIndirectionTableStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTable(k.machine, s.machine, s'.machine, dop)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures PersistentGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma PageInIndirectionTableStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTable(k.machine, s.machine, s'.machine, dop)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInIndirectionTableStepPreservesGraphs(k, s, s', dop);
  }

  lemma EvictStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma EvictStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    EvictStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma MachineStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| M.NextStep(k.machine, s.machine, s'.machine, dop, step);
    match step {
      case WriteBackStep(ref) => WriteBackStepPreservesInvariant(k, s, s', dop, ref);
      case WriteBackIndirectionTableStep => WriteBackIndirectionTableStepPreservesInvariant(k, s, s', dop);
      case UnallocStep(ref) => UnallocStepPreservesInvariant(k, s, s', dop, ref);
      case PageInStep(ref) => PageInStepPreservesInvariant(k, s, s', dop, ref);
      case PageInIndirectionTableStep => PageInIndirectionTableStepPreservesInvariant(k, s, s', dop);
      case EvictStep(ref) => EvictStepPreservesInvariant(k, s, s', dop, ref);
      case NoOpStep => { }
      case TransactionStep(ops) => TransactionStepPreservesInvariant(k, s, s', dop, ops);
    }
  }

  lemma CrashStepPreservesInvariant(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Crash(k, s, s')
    ensures Inv(k, s')
  {
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop: DiskOp) => MachineStepPreservesInvariant(k, s, s', dop);
      case CrashStep => CrashStepPreservesInvariant(k, s, s');
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInvariant(k, s, s', step);
  }

  */
}
