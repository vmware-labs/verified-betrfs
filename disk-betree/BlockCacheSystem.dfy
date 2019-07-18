include "Disk.dfy"
include "BlockCache.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "DiskAccessModel.dfy"

abstract module BlockCacheSystem {
  import opened Maps
  import opened Sequences
  import opened DAMTypes

  import M : BlockCache
  import D = Disk

  type LBA = M.LBA
  type Sector = M.Sector
  type DiskOp = M.DiskOp

  type Constants = DAMConstants<M.Constants, D.Constants>
  type Variables = DAMVariables<M.Variables, D.Variables<LBA, Sector>>

  type IndirectionTable = M.IndirectionTable
  type Reference = M.G.Reference
  type Node = M.G.Node
  type Op = M.Op

  predicate WFDisk(k: Constants, blocks: map<LBA, Sector>)
  {
    && var indirectionTableLBA := M.IndirectionTableLBA();
    && indirectionTableLBA in blocks
    && blocks[indirectionTableLBA].SectorIndirectionTable?
    && var indirectionTable := blocks[indirectionTableLBA].indirectionTable;
    && M.WFPersistentIndirectionTable(indirectionTable)
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

  function Graph(indirectionTable: set<Reference>, block: map<Reference, Node>) : map<Reference, Node>
  requires indirectionTable <= block.Keys
  {
    map ref | ref in indirectionTable :: block[ref]
  }

  function PersistentGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(k, s.disk.blocks)
  requires WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
  {
    Graph(
      DiskIndirectionTable(k, s.disk.blocks).graph.Keys,
      RefMapOfDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks))
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

  datatype Step =
    | MachineStep(dop: DiskOp)
    | CrashStep

  predicate Machine(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', dop)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  // Invariant

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

  predicate CleanCacheEntriesAreCorrect(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall ref | ref in s.machine.cache ::
      ref in s.machine.ephemeralIndirectionTable.lbas ==>
      MapsTo(
          s.disk.blocks,
          s.machine.ephemeralIndirectionTable.lbas[ref],
          M.SectorBlock(s.machine.cache[ref]))
  }

  predicate Inv(k: Constants, s: Variables) {
    && M.Inv(k.machine, s.machine)
    && WFDisk(k, s.disk.blocks)
    && WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s.disk.blocks), s.disk.blocks)
    && SuccessorsAgree(DiskIndirectionTable(k, s.disk.blocks).graph, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && s.machine.persistentIndirectionTable == DiskIndirectionTable(k, s.disk.blocks)
      && WFIndirectionTableWrtDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks)
      && SuccessorsAgree(s.machine.ephemeralIndirectionTable.graph, EphemeralGraph(k, s))
      && NoDanglingPointers(EphemeralGraph(k, s))
      && CleanCacheEntriesAreCorrect(k, s)
    )
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma WriteBackStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma WriteBackStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackStepPreservesGraphs(k, s, s', dop, ref);
  }

  lemma WriteBackIndirectionTableStepSyncsGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTable(k.machine, s.machine, s'.machine, dop)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s') == EphemeralGraph(k, s);
    ensures EphemeralGraph(k, s') == EphemeralGraph(k, s);
  {
    //assert M.Inv(k.machine, s'.machine);
    //assert WFDisk(k, s'.disk.blocks);
    //assert WFIndirectionTableWrtDisk(k, DiskIndirectionTable(k, s'.disk.blocks), s'.disk.blocks);

    assert DiskIndirectionTable(k, s'.disk.blocks) == s.machine.ephemeralIndirectionTable;

    /*
    forall ref | ref in s.machine.cache
    ensures MapsTo(
          RefMapOfDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks),
          ref, s.machine.cache)[ref]
    {
    }
    */

    assert RefMapOfDisk(k, DiskIndirectionTable(k, s'.disk.blocks), s'.disk.blocks)
        == RefMapOfDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks)
        == MapUnionPreferB(RefMapOfDisk(k, s.machine.ephemeralIndirectionTable, s.disk.blocks), s.machine.cache);
    assert PersistentGraph(k, s') == EphemeralGraph(k, s);
  }

  lemma WriteBackIndirectionTableStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTable(k.machine, s.machine, s'.machine, dop)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackIndirectionTableStepSyncsGraphs(k, s, s', dop);
  }

  lemma DirtyStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
    /*
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;
    */
  }

  lemma AllocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  /*
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;
    */
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
      TransactionStepPreservesInvariant(k, s, DAMVariables(smid, s.disk), dop, ops1);
      TransactionStepPreservesInvariant(k, DAMVariables(smid, s.disk), s', dop, ops2);
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

  lemma PageInStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageIn(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures PersistentGraph(k, s) == PersistentGraph(k, s');
    ensures EphemeralGraph(k, s) == EphemeralGraph(k, s');
  {
  }

  lemma PageInStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageIn(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInStepPreservesGraphs(k, s, s', dop, ref);
  }

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

}
