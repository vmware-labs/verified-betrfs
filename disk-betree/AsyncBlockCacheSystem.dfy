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

  predicate WFDisk(k: Constants, blocks: map<LBA, Sector>)
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

  predicate WFIndirectionTableWrtDisk(k: Constants, indirectionTable: IndirectionTable, blocks: map<LBA, Sector>)
  {
    && (forall ref | ref in indirectionTable.lbas :: WFIndirectionTableRefWrtDisk(indirectionTable, blocks, ref))
  }

  function DiskIndirectionTable(k: Constants, blocks: map<LBA, Sector>) : IndirectionTable
  requires WFDisk(k, blocks)
  {
    blocks[M.IndirectionTableLBA()].indirectionTable
  }

  function RefMapOfDisk(
      k: Constants,
      indirectionTable: IndirectionTable,
      blocks: map<LBA, Sector>) : map<Reference, Node>
  requires WFDisk(k, blocks)
  requires WFIndirectionTableWrtDisk(k, indirectionTable, blocks)
  {
    map ref | ref in indirectionTable.lbas :: blocks[indirectionTable.lbas[ref]].block
  }

  function Graph(refs: set<Reference>, refmap: map<Reference, Node>) : map<Reference, Node>
  requires refs <= refmap.Keys
  {
    map ref | ref in refs :: refmap[ref]
  }

  function DiskGraph(k: Constants, indirectionTable: IndirectionTable, blocks: map<LBA, Sector>) : map<Reference, Node>
  requires WFDisk(k, blocks)
  requires M.WFCompleteIndirectionTable(indirectionTable)
  requires WFIndirectionTableWrtDisk(k, indirectionTable, blocks)
  {
    Graph(indirectionTable.graph.Keys, RefMapOfDisk(k, indirectionTable, blocks))
  }

  function PersistentGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(k, s.disk.blocks)
  requires WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
  {
    DiskGraph(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
  }

  function WritingGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(k, s.disk.blocks)
  requires s.machine.Ready?
  requires s.machine.outstandingIndirectionTableWrite.Some?
  requires M.WFCompleteIndirectionTable(s.machine.outstandingIndirectionTableWrite.value.indirectionTable)
  requires WFIndirectionTableWrtDisk(k, s.machine.outstandingIndirectionTableWrite.value.indirectionTable, s.disk.blocks)
  {
    DiskGraph(k,
      s.machine.outstandingIndirectionTableWrite.value.indirectionTable,
      s.disk.blocks)
  }

  function EphemeralGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires M.Inv(k.machine, s.machine)
  requires s.machine.Ready?
  requires WFDisk(k, s.disk.blocks)
  requires WFIndirectionTableWrtDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks)
  {
    Graph(
      s.machine.ephemeralIndirectionTable.graph.Keys,
      MapUnionPreferB(RefMapOfDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks), s.machine.cache)
    )
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
    && WFDisk(k, s.disk.blocks)
    && WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(k, s.disk.blocks).graph, PersistentGraph(k, s))
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
    && (s.machine.outstandingIndirectionTableWrite.Some? ==>
        lba !in s.machine.outstandingIndirectionTableWrite.value.indirectionTable.lbas.Values)
    && (forall r | r in s.machine.ephemeralIndirectionTable.lbas ::
        s.machine.ephemeralIndirectionTable.lbas[r] == lba ==> r == ref)
    && !(id in s.disk.reqWrites && id in s.disk.respWrites)
    && (MapsTo(s.machine.ephemeralIndirectionTable.lbas, ref, lba) ==> (
      && ref in s.machine.cache
      && (id in s.disk.reqWrites ==> (
        s.disk.reqWrites[id] == D.ReqWrite(lba, M.SectorBlock(s.machine.cache[ref]))
      ))
      && (id in s.disk.respWrites ==> (
        MapsTo(s.disk.blocks, lba, M.SectorBlock(s.machine.cache[ref]))
      ))
    ))
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
      MapsTo(s.disk.reqWrites,
        s.machine.outstandingIndirectionTableWrite.value.reqId,
        D.ReqWrite(
          M.IndirectionTableLBA(),
          M.SectorIndirectionTable(
            s.machine.outstandingIndirectionTableWrite.value.indirectionTable
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
        s.machine.outstandingIndirectionTableWrite == Some(M.OutstandingIndirectionTableWrite(id, indirectionTable))
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
    && WFDisk(k, s.disk.blocks)
    && WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(k, s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && (s.machine.outstandingIndirectionTableWrite.Some? ==>
        && WFIndirectionTableWrtDisk(k, s.machine.outstandingIndirectionTableWrite.value.indirectionTable, s.disk.blocks)
      )
      && s.machine.persistentIndirectionTable == DiskIndirectionTable(k, s.disk.blocks)
      && WFIndirectionTableWrtDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks)
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

}
