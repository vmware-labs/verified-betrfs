include "AsyncBlockCache.dfy"

abstract module AsyncBlockCacheSystem {
  import M : AsyncBlockCache
  import D = AsyncDisk

  import opened Maps
  import opened Sequences
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
}
