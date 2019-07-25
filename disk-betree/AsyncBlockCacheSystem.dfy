include "AsyncBlockCache.dfy"
include "PivotBetreeSpec.dfy"

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
    && (forall lba | lba in blocks :: lba != M.IndirectionTableLBA() ==> blocks[lba].SectorBlock?)
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

  predicate WFIndirectionTableRefWrtDiskQueue(indirectionTable: IndirectionTable, disk: D.Variables<LBA, Sector>, ref: Reference)
  requires ref in indirectionTable.lbas
  {
    && (indirectionTable.lbas[ref] !in disk.blocks ==>
      QueueLookupIdByLBA(disk.reqWrites, indirectionTable.lbas[ref]).Some?
    )
  }

  predicate WFIndirectionTableWrtDiskQueue(indirectionTable: IndirectionTable, disk: D.Variables<LBA, Sector>)
  {
    && (forall ref | ref in indirectionTable.lbas :: WFIndirectionTableRefWrtDiskQueue(indirectionTable, disk, ref))
  }

  predicate WFReqWriteBlocks(reqWrites: map<D.ReqId, D.ReqWrite<LBA, Sector>>)
  {
    forall id | id in reqWrites && M.ValidLBAForNode(reqWrites[id].lba) ::
        reqWrites[id].sector.SectorBlock?
  }

  function DiskQueueLookup(disk: D.Variables<LBA,Sector>, lba: LBA) : Node
  requires WFDisk(disk.blocks)
  requires WFReqWriteBlocks(disk.reqWrites)
  requires M.ValidLBAForNode(lba)
  requires lba !in disk.blocks ==> QueueLookupIdByLBA(disk.reqWrites, lba).Some?
  {
    if QueueLookupIdByLBA(disk.reqWrites, lba).Some? then
      disk.reqWrites[QueueLookupIdByLBA(disk.reqWrites, lba).value].sector.block
    else
      disk.blocks[lba].block
  }

  function DiskQueueCacheLookup(indirectionTable: IndirectionTable, disk: D.Variables<LBA,Sector>, cache: map<Reference, Node>, ref: Reference) : Node
  requires WFDisk(disk.blocks)
  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDiskQueue(indirectionTable, disk)
  requires M.IndirectionTableCacheConsistent(indirectionTable, cache)
  requires WFReqWriteBlocks(disk.reqWrites)
  requires ref in indirectionTable.graph
  {
    if ref in indirectionTable.lbas then (
      DiskQueueLookup(disk, indirectionTable.lbas[ref])
    ) else (
      cache[ref]
    )
  }

  function DiskCacheGraph(indirectionTable: IndirectionTable, disk: D.Variables<LBA,Sector>, cache: map<Reference, Node>) : map<Reference, Node>
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
    && WFIndirectionTableWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(s.disk.blocks).graph, PersistentGraph(k, s))
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
      ref in s.machine.ephemeralIndirectionTable.lbas ==>
        s.machine.cache[ref] == DiskQueueLookup(s.disk, s.machine.ephemeralIndirectionTable.lbas[ref])
  }

  // Any outstanding read we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockRead(k: Constants, s: Variables, id: D.ReqId, ref: Reference)
  requires s.machine.Ready?
  {
    && ref !in s.machine.cache
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
  requires WFDisk(s.disk.blocks)
  {
    s.machine.outstandingIndirectionTableRead.Some? ==> (
      && var reqId := s.machine.outstandingIndirectionTableRead.value;
      && !(reqId in s.disk.reqReads && reqId in s.disk.respReads)
      && (reqId in s.disk.reqReads ==>
        s.disk.reqReads[reqId] == D.ReqRead(M.IndirectionTableLBA())
      )
      && (reqId in s.disk.respReads ==>
        s.disk.respReads[reqId] == D.RespRead(M.SectorIndirectionTable(DiskIndirectionTable(s.disk.blocks)))
      )
    )
  }

  // Any outstanding write we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockWrite(k: Constants, s: Variables, id: D.ReqId, ref: Reference, lba: LBA)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    && lba != M.IndirectionTableLBA()
    && (forall r | r in s.machine.ephemeralIndirectionTable.lbas ::
        s.machine.ephemeralIndirectionTable.lbas[r] == lba ==> r == ref)

    && (s.machine.frozenIndirectionTable.Some? ==>
        forall r | r in s.machine.frozenIndirectionTable.value.lbas ::
        s.machine.frozenIndirectionTable.value.lbas[r] == lba ==> r == ref)

    && (forall r | r in DiskIndirectionTable(s.disk.blocks).lbas ::
        DiskIndirectionTable(s.disk.blocks).lbas[r] != lba)

    && (id in s.disk.reqWrites ==>
      && s.disk.reqWrites[id].lba == lba
      && s.disk.reqWrites[id].sector.SectorBlock?
    )

    && !(id in s.disk.reqWrites && id in s.disk.respWrites)
  }

  predicate CorrectInflightBlockWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    forall id | id in s.machine.outstandingBlockWrites ::
      CorrectInflightBlockWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, s.machine.outstandingBlockWrites[id].lba)
  }

  predicate CorrectInflightIndirectionTableWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires WFDisk(s.disk.blocks)
  {
    s.machine.outstandingIndirectionTableWrite.Some? ==> (
      && s.machine.frozenIndirectionTable.Some?
      && var reqId := s.machine.outstandingIndirectionTableWrite.value;
      && !(reqId in s.disk.reqWrites && reqId in s.disk.respWrites)
      && (reqId in s.disk.reqWrites ==>
          s.disk.reqWrites[reqId] ==
          D.ReqWrite(
            M.IndirectionTableLBA(),
            M.SectorIndirectionTable(
              s.machine.frozenIndirectionTable.value
            )
          )
      )
      && (reqId in s.disk.respWrites ==>
        s.machine.frozenIndirectionTable == Some(DiskIndirectionTable(s.disk.blocks))
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

  predicate WriteRequestsUniqueLBAs(reqWrites: map<D.ReqId, D.ReqWrite<LBA, Sector>>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && reqWrites[id1].lba == reqWrites[id2].lba :: id1 == id2
  }

  predicate Inv(k: Constants, s: Variables) {
    && M.Inv(k.machine, s.machine)
    && WFDisk(s.disk.blocks)
    && WFReqWriteBlocks(s.disk.reqWrites)
    && WFIndirectionTableWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && (s.machine.frozenIndirectionTable.Some? ==>
        && WFIndirectionTableWrtDiskQueue(s.machine.frozenIndirectionTable.value, s.disk)
        && SuccessorsAgree(s.machine.frozenIndirectionTable.value.graph, FrozenGraph(k, s))
      )
      && (s.machine.outstandingIndirectionTableWrite.Some? ==>
        && WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.blocks)
        && s.machine.outstandingBlockWrites == map[]
      )
      && (
        || s.machine.persistentIndirectionTable == DiskIndirectionTable(s.disk.blocks)
        || s.machine.frozenIndirectionTable == Some(DiskIndirectionTable(s.disk.blocks))
      )
      && (s.machine.outstandingIndirectionTableWrite.None? ==>
        || s.machine.persistentIndirectionTable == DiskIndirectionTable(s.disk.blocks)
      )
      && WFIndirectionTableWrtDiskQueue(s.machine.ephemeralIndirectionTable, s.disk)
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
    && WriteRequestsUniqueLBAs(s.disk.reqWrites)
    && RecordedWriteRequests(k, s)
  }

  ////// Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma QueueLookupIdByLBAInsert(
      reqWrites: map<D.ReqId, D.ReqWrite<LBA, Sector>>,
      reqWrites': map<D.ReqId, D.ReqWrite<LBA, Sector>>,
      id: D.ReqId,
      req: D.ReqWrite<LBA, Sector>,
      lba: LBA)
  requires id !in reqWrites
  requires reqWrites' == reqWrites[id := req]
  requires WriteRequestsUniqueLBAs(reqWrites')
  ensures QueueLookupIdByLBA(reqWrites', req.lba) == Some(id)
  ensures lba != req.lba ==>
      QueueLookupIdByLBA(reqWrites', lba) == QueueLookupIdByLBA(reqWrites, lba)
  {
    assert reqWrites'[id].lba == req.lba;
    //if (QueueLookupIdByLBA(reqWrites', req.lba).None?) {
    //  assert forall id | id in reqWrites' :: reqWrites'[id].lba != req.lba;
    //  assert false;
    //}
    //assert QueueLookupIdByLBA(reqWrites', req.lba).Some?;
    //assert QueueLookupIdByLBA(reqWrites', req.lba).value == id;

    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && reqWrites[id1].lba == reqWrites[id2].lba
    ensures id1 == id2
    {
      assert reqWrites'[id1] == reqWrites[id1];
      assert reqWrites'[id2] == reqWrites[id2];
    }
    assert WriteRequestsUniqueLBAs(reqWrites);

    if (lba != req.lba) {
      if id' :| id' in reqWrites && reqWrites[id'].lba == lba {
        assert reqWrites'[id'].lba == lba;
        //assert QueueLookupIdByLBA(reqWrites', lba)
        //    == Some(id')
        //    == QueueLookupIdByLBA(reqWrites, lba);
      } else {
        //assert QueueLookupIdByLBA(reqWrites', lba) == QueueLookupIdByLBA(reqWrites, lba);
      }
    }
  }

  lemma WriteBackReqStepUniqueLBAs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, indirectionTable: IndirectionTable, indirectionTable': IndirectionTable)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures WriteRequestsUniqueLBAs(s'.disk.reqWrites)
  {
    /*forall id1, id2 | id1 in s'.disk.reqWrites && id2 in s'.disk.reqWrites && s'.disk.reqWrites[id1].lba == s'.disk.reqWrites[id2].lba
    ensures id1 == id2
    {
      var lba := s'.disk.reqWrites[id1].lba;
      if (lba == dop.reqWrite.lba) {
        if (id1 in s.disk.reqWrites) {
          assert RecordedWriteRequest(k, s, id1, s.disk.reqWrites[id1].lba, s.disk.reqWrites[id1].sector);
          assert id1 in s.machine.outstandingBlockWrites;
          assert CorrectInflightBlockWrite(k, s, id1, s.machine.outstandingBlockWrites[id1].ref, s.machine.outstandingBlockWrites[id1].lba);
          assert s.machine.outstandingBlockWrites[id1].lba == dop.reqWrite.lba;
          assert false;
        }
        assert id1 == dop.id;
        assert id2 == dop.id;
        assert id1 == id2;
      } else {
        assert id1 == id2;
      }
    }*/
  }

  lemma WriteBackReqStepPreservesDiskCacheGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, indirectionTable: IndirectionTable, indirectionTable': IndirectionTable)
    requires Inv(k, s)
    requires M.WriteBackReq(k.machine, s.machine, s'.machine, dop, ref)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);

    requires M.WFIndirectionTable(indirectionTable)
    requires WFIndirectionTableWrtDiskQueue(indirectionTable, s.disk)
    requires indirectionTable' == M.AssignRefToLBA(indirectionTable, ref, dop.reqWrite.lba)
    requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
    requires ref !in indirectionTable.lbas
    requires dop.reqWrite.lba !in indirectionTable.lbas.Values

    ensures M.WFIndirectionTable(indirectionTable')
    ensures WFIndirectionTableWrtDiskQueue(indirectionTable', s'.disk)
    ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
         == DiskCacheGraph(indirectionTable', s'.disk, s'.machine.cache)
  {
    assert dop.id !in s.disk.reqWrites;

    forall r | r in indirectionTable'.lbas
    ensures WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r)
    {
      if (r == ref) {
        assert s'.disk.reqWrites[dop.id].lba == dop.reqWrite.lba;
        //assert indirectionTable'.lbas[ref] == dop.reqWrite.lba;
        //assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable'.lbas[ref]).Some?;
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r);
      } else {
        //assert r in indirectionTable.lbas;
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable, s.disk, r);
        //assert indirectionTable.lbas[r] == indirectionTable'.lbas[r];
        //assert s.disk.blocks == s'.disk.blocks;
        if QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[r]).Some? {
          var oid := QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[r]).value;
          //assert oid in s.disk.reqWrites;
          //assert s.disk.reqWrites[oid].lba == indirectionTable.lbas[r];
          assert s'.disk.reqWrites[oid].lba == indirectionTable.lbas[r];
          //assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable.lbas[r]).Some?;
        }
        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable', s'.disk, r);
      }
    }

    forall r | r in indirectionTable.graph
    ensures DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
         == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r)
    {
      if (r == ref) {
        QueueLookupIdByLBAInsert(s.disk.reqWrites, s'.disk.reqWrites, dop.id, dop.reqWrite, indirectionTable'.lbas[ref]);

        //assert s'.disk.reqWrites[dop.id].lba == dop.reqWrite.lba;
        /*
        assert indirectionTable'.lbas[ref] == dop.reqWrite.lba;
        assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable'.lbas[ref]).Some?;
        assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable'.lbas[ref]) == Some(dop.id);
        assert s'.disk.reqWrites[dop.id].sector.SectorBlock?;
        assert r !in indirectionTable.lbas;

        assert DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
            == s.machine.cache[r]
            == s'.disk.reqWrites[dop.id].sector.block
            == DiskQueueCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
        */
      } else if (r in indirectionTable.lbas) {
        //assert indirectionTable.lbas[r] != dop.reqWrite.lba;
        QueueLookupIdByLBAInsert(s.disk.reqWrites, s'.disk.reqWrites, dop.id, dop.reqWrite, indirectionTable.lbas[r]);

        //assert WFIndirectionTableRefWrtDiskQueue(indirectionTable, s.disk, r);
        //assert indirectionTable.lbas[r] == indirectionTable'.lbas[r];
        //assert s.disk.blocks == s'.disk.blocks;

        /*
        if QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[r]).Some? {
          var oid := QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[r]).value;
          assert oid in s.disk.reqWrites;
          assert s.disk.reqWrites[oid].lba == indirectionTable.lbas[r];
          assert s'.disk.reqWrites[oid].lba == indirectionTable.lbas[r];
          assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable.lbas[r]).Some?;
          assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable'.lbas[r])
              == QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[r]);
        } else {
          assert QueueLookupIdByLBA(s'.disk.reqWrites, indirectionTable.lbas[r]).None?;
          assert s.disk.blocks[indirectionTable.lbas[r]].block
              == s'.disk.blocks[indirectionTable.lbas[r]].block
              == s'.disk.blocks[indirectionTable'.lbas[r]].block;
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
    WriteBackReqStepPreservesGraphs(k, s, s', dop, ref);
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
  }

  lemma WriteBackIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop)
    requires D.RecvWrite(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s) == FrozenGraphOpt(k, s');
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
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
  }

  lemma WriteBackIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop)
    requires D.AckWrite(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine)
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
    M.WriteBackIndirectionTableRespStepPreservesInv(k.machine, s.machine, s'.machine, dop);
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
      TransactionStepPreservesInv(k, s, AsyncDiskModelVariables(smid, s.disk), dop, ops1);
      TransactionStepPreservesInv(k, AsyncDiskModelVariables(smid, s.disk), s', dop, ops2);
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

    ensures WFIndirectionTableWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk)

    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraph(k, s') == PersistentGraph(k, s);
  {
    assert DiskIndirectionTable(s.disk.blocks) == s'.machine.persistentIndirectionTable;
    /*
    forall ref | ref in s'.machine.ephemeralIndirectionTable.lbas
    ensures WFIndirectionTableRefWrtDiskQueue(s'.machine.ephemeralIndirectionTable, s'.disk, ref)
    {
      assert ref in DiskIndirectionTable(s.disk.blocks).lbas;
      assert WFIndirectionTableRefWrtDisk(DiskIndirectionTable(s.disk.blocks), s.disk.blocks, ref);
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

  lemma PushSyncReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
    requires Inv(k, s)
    requires M.PushSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
  {
  }

  lemma PushSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
    requires Inv(k, s)
    requires M.PushSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PushSyncReqStepPreservesGraphs(k, s, s', dop, id);
  }

  lemma PopSyncReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
    requires Inv(k, s)
    requires M.PopSyncReq(k.machine, s.machine, s'.machine, dop, id)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);
    ensures PersistentGraph(k, s') == PersistentGraph(k, s);
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
  {
  }

  lemma PopSyncReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, id: int)
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

  lemma ProcessWritePreservesDiskCacheGraph(k: Constants, s: Variables, s': Variables, id: D.ReqId, indirectionTable: IndirectionTable)
  requires Inv(k, s)
  requires s.machine == s'.machine
  requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)

  requires M.WFIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDiskQueue(indirectionTable, s.disk)
  requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)

  ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
       == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache)
  {
    /*var req := s.disk.reqWrites[id];
    if (req.lba == M.IndirectionTableLBA()) {
      assert WFDisk(s'.disk.blocks);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    } else {
      assert WFDisk(s'.disk.blocks);
      assert DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(indirectionTable, s'.disk, s'.machine.cache);
    }*/
  }

  lemma DiskCacheGraphEqDiskGraph(k: Constants, s: Variables, indirectionTable: IndirectionTable)
  requires Inv(k, s)
  requires s.machine.Ready?
  requires M.WFCompleteIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(indirectionTable, s.disk.blocks)
  requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
  requires s.machine.outstandingBlockWrites == map[]
  ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
       == DiskGraph(indirectionTable, s.disk.blocks)
  {
    /*forall ref | ref in indirectionTable.graph
    ensures RefMapOfDisk(indirectionTable, s.disk.blocks)[ref]
        == DiskQueueCacheLookup(indirectionTable, s.disk, s.machine.cache, ref)
    {
      assert QueueLookupIdByLBA(s.disk.reqWrites, indirectionTable.lbas[ref]).None?;
    }*/
  }

  lemma ProcessWritePreservesGraphs(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)

    ensures WFDisk(s'.disk.blocks)

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

    var req := s.disk.reqWrites[id];
    if (req.lba == M.IndirectionTableLBA()) {
      var indirectionTable := s.machine.frozenIndirectionTable.value;
      DiskCacheGraphEqDiskGraph(k, s, indirectionTable);

      assert FrozenGraph(k, s)
          == DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskGraph(s.machine.frozenIndirectionTable.value, s.disk.blocks)
          == PersistentGraph(k, s');
    } else {
      var indirectionTable := DiskIndirectionTable(s.disk.blocks);

      /*forall ref | ref in indirectionTable.graph
      ensures RefMapOfDisk(indirectionTable, s.disk.blocks)[ref]
           == RefMapOfDisk(indirectionTable, s'.disk.blocks)[ref]
      {
        assert RecordedWriteRequest(k, s, id, req.lba, req.sector);
        assert CorrectInflightBlockWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, req.lba);
        assert indirectionTable.lbas[ref] != req.lba;
      }*/

      assert PersistentGraph(k, s)
          == DiskGraph(DiskIndirectionTable(s.disk.blocks), s.disk.blocks)
          == DiskGraph(DiskIndirectionTable(s.disk.blocks), s'.disk.blocks)
          == DiskGraph(DiskIndirectionTable(s'.disk.blocks), s'.disk.blocks)
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
  }

  lemma DiskInternalStepPreservesInv(k: Constants, s: Variables, s': Variables, step: D.InternalStep)
    requires Inv(k, s)
    requires DiskInternal(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      case ProcessReadStep(id) => ProcessReadPreservesInv(k, s, s', id);
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
}

module BetreeGraphAsyncBlockCacheSystem refines AsyncBlockCacheSystem {
  import M = BetreeGraphAsyncBlockCache
}
