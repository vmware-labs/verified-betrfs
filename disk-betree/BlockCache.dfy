include "Betree.dfy"
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "Graph.dfy"
include "Disk.dfy"

module LBAType {

  import NativeTypes

  type LBA(==,!new) = NativeTypes.uint64
  function method IndirectionTableLBA() : LBA { 0 }

  function method toLBA(i: NativeTypes.uint64) : LBA{ i }
  function method toUint64(i: LBA) : NativeTypes.uint64 { i }

  export S provides LBA, IndirectionTableLBA, toLBA, toUint64, NativeTypes
  export extends S
	export Internal reveals *
}

abstract module BlockCache refines Transactable {
  import opened Maps
  import LBAType

  import Disk = Disk

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

  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable,
        ephemeralIndirectionTable: IndirectionTable,
        cache: map<Reference, Node>)
    | Unready


  predicate IsNotDirty(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralIndirectionTable.lbas
  }
  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralIndirectionTable.graph
  }
  predicate ValidLBAForNode(k: Constants, lba: LBA)
  {
    lba != IndirectionTableLBA()
  }

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackIndirectionTableStep
    | UnallocStep(ref: Reference)
    | PageInStep(ref: Reference)
    | PageInIndirectionTableStep
    | EvictStep(ref: Reference)
    | NoOpStep
    | TransactionStep(ops: seq<Op>)

  predicate method GraphClosed(graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in graph ::
      forall succ | succ in graph[ref] ::
        succ in graph
  }

  predicate WFPersistentIndirectionTable(indirectionTable: IndirectionTable)
  {
    && IndirectionTableLBA() !in indirectionTable.lbas.Values
    && indirectionTable.graph.Keys == indirectionTable.lbas.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  predicate WFIndirectionTable(k: Constants, indirectionTable: IndirectionTable)
  {
    && IndirectionTableLBA() !in indirectionTable.lbas.Values
    && indirectionTable.lbas.Keys <= indirectionTable.graph.Keys
    && G.Root() in indirectionTable.graph
    && GraphClosed(indirectionTable.graph)
  }

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.WriteOp?
    && ref in s.cache
    && ValidLBAForNode(k, dop.lba)
    && dop.lba !in s.persistentIndirectionTable.lbas.Values
    && dop.lba !in s.ephemeralIndirectionTable.lbas.Values
    && dop.sector == SectorBlock(s.cache[ref])
    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.lbas == s.ephemeralIndirectionTable.lbas[ref := dop.lba]
    && s'.ephemeralIndirectionTable.graph == s.ephemeralIndirectionTable.graph
    && s'.cache == s.cache
  }

  predicate WriteBackIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.WriteOp?
    && dop.lba == IndirectionTableLBA()
    && dop.sector == SectorIndirectionTable(s.ephemeralIndirectionTable)
    && s.cache.Keys <= s.ephemeralIndirectionTable.lbas.Keys
    && s' == s.(persistentIndirectionTable := s.ephemeralIndirectionTable)
  }

  predicate BlockPointsToValidReferences(block: Node, graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in G.Successors(block) :: ref in graph
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && ref in s.cache
    && s'.Ready?
    && s'.cache == s.cache[ref := block]
    && s'.persistentIndirectionTable == s.persistentIndirectionTable

    && s'.ephemeralIndirectionTable.lbas == MapRemove(s.ephemeralIndirectionTable.lbas, {ref})

    && BlockPointsToValidReferences(block, s.ephemeralIndirectionTable.graph)

    && ref in s'.ephemeralIndirectionTable.graph
    && s'.ephemeralIndirectionTable.graph == s.ephemeralIndirectionTable.graph[ref := s'.ephemeralIndirectionTable.graph[ref]]
    && (iset r | r in s'.ephemeralIndirectionTable.graph[ref]) == G.Successors(block)
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
  }

  predicate ReadStep(k: Constants, s: Variables, op: ReadOp)
  {
    s.Ready? && MapsTo(s.cache, op.ref, op.node)
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

  predicate NoPredecessors(graph: map<Reference, seq<Reference>>, ref: Reference)
  {
    forall r | r in graph :: ref !in graph[r]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?

    && IsAllocated(s, ref)

    // We can only dealloc this if nothing is pointing to it.
    && ref != G.Root()
    && NoPredecessors(s.ephemeralIndirectionTable.graph, ref)

    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.lbas == MapRemove(s.ephemeralIndirectionTable.lbas, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && s'.ephemeralIndirectionTable.graph == MapRemove(s.ephemeralIndirectionTable.graph, {ref})
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.ReadOp?
    && IsAllocated(s, ref)
    && IsNotDirty(s, ref)
    && s.ephemeralIndirectionTable.lbas[ref] == dop.lba
    && dop.sector.SectorBlock?
    && (iset r | r in s.ephemeralIndirectionTable.graph[ref]) == G.Successors(dop.sector.block)
    && s' == s.(cache := s.cache[ref := dop.sector.block])
  }

  predicate PageInIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Unready?
    && dop.ReadOp?
    && dop.lba == IndirectionTableLBA()
    && dop.sector.SectorIndirectionTable?
    && WFPersistentIndirectionTable(dop.sector.indirectionTable)
    && s' == Ready(dop.sector.indirectionTable, dop.sector.indirectionTable, map[])
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?
    && ref in s.cache
    && IsNotDirty(s, ref)
    && s' == s.(cache := MapRemove(s.cache, {ref}))
  }

  predicate NoOp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && (dop.ReadOp? || dop.NoDiskOp?)
    && s' == s
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == Unready
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteBackStep(ref) => WriteBack(k, s, s', dop, ref)
      case WriteBackIndirectionTableStep => WriteBackIndirectionTable(k, s, s', dop)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, ref)
      case PageInStep(ref) => PageIn(k, s, s', dop, ref)
      case PageInIndirectionTableStep => PageInIndirectionTable(k, s, s', dop)
      case EvictStep(ref) => Evict(k, s, s', dop, ref)
      case NoOpStep => NoOp(k, s, s', dop)
      case TransactionStep(ops) => Transaction(k, s, s', dop, ops)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step: Step :: NextStep(k, s, s', dop, step)
  }

  predicate CacheConsistentWithSuccessors(cache: map<Reference, Node>, graph: map<Reference, seq<Reference>>)
  requires cache.Keys <= graph.Keys
  {
    forall ref | ref in cache :: (iset r | r in graph[ref]) == G.Successors(cache[ref])
  }

  predicate InvReady(k: Constants, s: Variables)
  requires s.Ready?
  {
    && WFPersistentIndirectionTable(s.persistentIndirectionTable)
    && WFIndirectionTable(k, s.ephemeralIndirectionTable)
    && s.cache.Keys <= s.ephemeralIndirectionTable.graph.Keys
    && s.ephemeralIndirectionTable.graph.Keys <= s.cache.Keys + s.ephemeralIndirectionTable.lbas.Keys
    && CacheConsistentWithSuccessors(s.cache, s.ephemeralIndirectionTable.graph)
    && GraphClosed(s.ephemeralIndirectionTable.graph)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    match s {
      case Ready(persistentIndirectionTable, ephemeralIndirectionTable, cache) => InvReady(k, s)
      case Unready => true
    }
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma WriteBackStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires WriteBack(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma WriteBackIndirectionTableStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackIndirectionTable(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma DirtyStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Dirty(k, s, s', ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma AllocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Alloc(k, s, s', ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma OpPreservesInvariant(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires OpStep(k, s, s', op)
    ensures Inv(k, s')
  {
    match op {
      case WriteOp(ref, block) => DirtyStepPreservesInvariant(k, s, s', ref, block);
      case AllocOp(ref, block) => AllocStepPreservesInvariant(k, s, s', ref, block);
    }
  }

  lemma TransactionStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ops: seq<Op>)
    requires Inv(k, s)
    requires Transaction(k, s, s', dop, ops)
    ensures Inv(k, s')
    decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      OpPreservesInvariant(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := SplitTransaction(k, s, s', ops);
      TransactionStepPreservesInvariant(k, s, smid, dop, ops1);
      TransactionStepPreservesInvariant(k, smid, s', dop, ops2);
    }
  }

  lemma UnallocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires Unalloc(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      /*
      forall key | key in s'.ephemeralIndirectionTable.lbas.Keys
      ensures key in s'.ephemeralIndirectionTable.graph.Keys
      {
        assert key in s.ephemeralIndirectionTable.lbas.Keys;
        assert key != ref;
        assert key in s.ephemeralIndirectionTable.graph.Keys;
        assert key in s.ephemeralIndirectionTable.graph;
        assert key in MapRemove(s.ephemeralIndirectionTable.graph, {ref});
        assert key in s'.ephemeralIndirectionTable.graph;
      }
      assert s'.ephemeralIndirectionTable.lbas.Keys <= s'.ephemeralIndirectionTable.graph.Keys;
      */
      assert InvReady(k, s');
    }
  }

  lemma PageInStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires PageIn(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma PageInIndirectionTableStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires PageInIndirectionTable(k, s, s', dop)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma EvictStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires Evict(k, s, s', dop, ref)
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

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Next(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', dop, step);
    NextStepPreservesInv(k, s, s', dop, step);
  }
}
