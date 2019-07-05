include "Betree.dfy"
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "Graph.dfy"
include "Disk.dfy"

module LBAType {

  import NativeTypes

  type LBA(==,!new) = NativeTypes.uint64
  function method SuperblockLBA() : LBA { 0 }

  function method toLBA(i: NativeTypes.uint64) : LBA{ i }
  function method toUint64(i: LBA) : NativeTypes.uint64 { i }

  export S provides LBA, SuperblockLBA, toLBA, toUint64, NativeTypes
  export extends S
	export Internal reveals *
}

abstract module BlockCache refines Transactable {
  import opened Maps
  import LBAType

  import Disk = Disk

  type LBA = LBAType.LBA
  datatype Constants = Constants()
  function method SuperblockLBA() : LBA { LBAType.SuperblockLBA() }

  // TODO make superblock take up more than one block (it's not really a superblock)
  datatype Superblock = Superblock(
      lbas: map<Reference, LBA>,
      graph: map<Reference, seq<Reference>>)

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorSuperblock(superblock: Superblock)

  type DiskOp = Disk.DiskOp<LBA, Sector>

  // BlockCache stuff

  datatype Variables =
    | Ready(
        persistentSuperblock: Superblock,
        ephemeralSuperblock: Superblock,
        cache: map<Reference, Node>)
    | Unready


  predicate IsNotDirty(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralSuperblock.lbas
  }
  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralSuperblock.graph
  }
  predicate ValidLBAForNode(k: Constants, lba: LBA)
  {
    lba != SuperblockLBA()
  }

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackSuperblockStep
    | UnallocStep(ref: Reference)
    | PageInStep(ref: Reference)
    | PageInSuperblockStep
    | EvictStep(ref: Reference)
    | ReadNoOpStep
    | TransactionStep(ops: seq<Op>)

  predicate GraphClosed(graph: map<Reference, seq<Reference>>)
  {
    forall ref | ref in graph ::
      forall succ | succ in graph[ref] ::
        succ in graph
  }

  predicate WFPersistentSuperblock(superblock: Superblock)
  {
    && SuperblockLBA() !in superblock.lbas.Values
    && superblock.graph.Keys == superblock.lbas.Keys
    && G.Root() in superblock.graph
    && GraphClosed(superblock.graph)
  }

  predicate WFSuperblock(k: Constants, superblock: Superblock)
  {
    && SuperblockLBA() !in superblock.lbas.Values
    && superblock.lbas.Keys <= superblock.graph.Keys
    && G.Root() in superblock.graph
    && GraphClosed(superblock.graph)
  }

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.WriteOp?
    && ref in s.cache
    && ValidLBAForNode(k, dop.lba)
    && dop.lba !in s.persistentSuperblock.lbas.Values
    && dop.lba !in s.ephemeralSuperblock.lbas.Values
    && dop.sector == SectorBlock(s.cache[ref])
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas[ref := dop.lba]
    && s'.ephemeralSuperblock.graph == s.ephemeralSuperblock.graph
    && s'.cache == s.cache
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.WriteOp?
    && dop.lba == SuperblockLBA()
    && dop.sector == SectorSuperblock(s.ephemeralSuperblock)
    && s.cache.Keys <= s.ephemeralSuperblock.lbas.Keys
    && s' == s.(persistentSuperblock := s.ephemeralSuperblock)
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
    && s'.persistentSuperblock == s.persistentSuperblock

    && s'.ephemeralSuperblock.lbas == MapRemove(s.ephemeralSuperblock.lbas, {ref})

    && BlockPointsToValidReferences(block, s.ephemeralSuperblock.graph)

    && ref in s'.ephemeralSuperblock.graph
    && s'.ephemeralSuperblock.graph == s.ephemeralSuperblock.graph[ref := s'.ephemeralSuperblock.graph[ref]]
    && (iset r | r in s'.ephemeralSuperblock.graph[ref]) == G.Successors(block)
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && ref !in s.cache
    && !IsAllocated(s, ref)
    && s'.Ready?
    && s'.cache == s.cache[ref := block]
    && s'.persistentSuperblock == s.persistentSuperblock

    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas

    && BlockPointsToValidReferences(block, s.ephemeralSuperblock.graph)

    && ref in s'.ephemeralSuperblock.graph
    && s'.ephemeralSuperblock.graph == s.ephemeralSuperblock.graph[ref := s'.ephemeralSuperblock.graph[ref]]
    && (iset r | r in s'.ephemeralSuperblock.graph[ref]) == G.Successors(block)
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
    && NoPredecessors(s.ephemeralSuperblock.graph, ref)

    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == MapRemove(s.ephemeralSuperblock.lbas, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && s'.ephemeralSuperblock.graph == MapRemove(s.ephemeralSuperblock.graph, {ref})
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.ReadOp?
    && IsAllocated(s, ref)
    && IsNotDirty(s, ref)
    && s.ephemeralSuperblock.lbas[ref] == dop.lba
    && dop.sector.SectorBlock?
    && (iset r | r in s.ephemeralSuperblock.graph[ref]) == G.Successors(dop.sector.block)
    && s' == s.(cache := s.cache[ref := dop.sector.block])
  }

  predicate PageInSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Unready?
    && dop.ReadOp?
    && dop.lba == SuperblockLBA()
    && dop.sector.SectorSuperblock?
    && WFPersistentSuperblock(dop.sector.superblock)
    && s' == Ready(dop.sector.superblock, dop.sector.superblock, map[])
  }

  predicate Evict(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?
    && ref in s.cache
    && IsNotDirty(s, ref)
    && s' == s.(cache := MapRemove(s.cache, {ref}))
  }

  predicate ReadNoOp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReadOp?
    && s' == s
  }

  predicate Init(k: Constants, s: Variables)
  {
    s == Unready
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteBackStep(ref) => WriteBack(k, s, s', dop, ref)
      case WriteBackSuperblockStep => WriteBackSuperblock(k, s, s', dop)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, ref)
      case PageInStep(ref) => PageIn(k, s, s', dop, ref)
      case PageInSuperblockStep => PageInSuperblock(k, s, s', dop)
      case EvictStep(ref) => Evict(k, s, s', dop, ref)
      case ReadNoOpStep => ReadNoOp(k, s, s', dop)
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
    && WFPersistentSuperblock(s.persistentSuperblock)
    && WFSuperblock(k, s.ephemeralSuperblock)
    && s.cache.Keys <= s.ephemeralSuperblock.graph.Keys
    && s.ephemeralSuperblock.graph.Keys <= s.cache.Keys + s.ephemeralSuperblock.lbas.Keys
    && CacheConsistentWithSuccessors(s.cache, s.ephemeralSuperblock.graph)
    && GraphClosed(s.ephemeralSuperblock.graph)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    match s {
      case Ready(persistentSuperblock, ephemeralSuperblock, cache) => InvReady(k, s)
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

  lemma WriteBackSuperblockStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires WriteBackSuperblock(k, s, s', dop)
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
      forall key | key in s'.ephemeralSuperblock.lbas.Keys
      ensures key in s'.ephemeralSuperblock.graph.Keys
      {
        assert key in s.ephemeralSuperblock.lbas.Keys;
        assert key != ref;
        assert key in s.ephemeralSuperblock.graph.Keys;
        assert key in s.ephemeralSuperblock.graph;
        assert key in MapRemove(s.ephemeralSuperblock.graph, {ref});
        assert key in s'.ephemeralSuperblock.graph;
      }
      assert s'.ephemeralSuperblock.lbas.Keys <= s'.ephemeralSuperblock.graph.Keys;
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

  lemma PageInSuperblockStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires PageInSuperblock(k, s, s', dop)
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
      case WriteBackSuperblockStep => WriteBackSuperblockStepPreservesInvariant(k, s, s', dop);
      case UnallocStep(ref) => UnallocStepPreservesInvariant(k, s, s', dop, ref);
      case PageInStep(ref) => PageInStepPreservesInvariant(k, s, s', dop, ref);
      case PageInSuperblockStep => PageInSuperblockStepPreservesInvariant(k, s, s', dop);
      case EvictStep(ref) => EvictStepPreservesInvariant(k, s, s', dop, ref);
      case ReadNoOpStep => { }
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
