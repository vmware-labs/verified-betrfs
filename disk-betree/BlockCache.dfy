include "DiskBetree.dfy"
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "Graph.dfy"
include "Disk.dfy"

abstract module BlockCache {
  // Ideally BlockCache would be parameterized by the graph type,
  // but right now it's instantiated to BetreeGraph.
  import G : Graph 

  import opened Sequences
  import opened Maps

  import Disk = Disk

  type LBA = Disk.LBA

  datatype Constants = Constants()
  function SuperblockLBA(k: Constants) : LBA

  // TODO make superblock take up more than one block (it's not really a superblock)
  type Reference = G.Reference
  type Node = G.Node

  datatype Superblock = Superblock(
      lbas: map<Reference, LBA>,
      refcounts: map<Reference, int>)

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorSuperblock(superblock: Superblock)

  type DiskOp = Disk.DiskOp<Sector>

  // BlockCache stuff

  datatype CacheLine = CacheLine(block: Node)

  datatype Variables =
    | Ready(
        persistentSuperblock: Superblock,
        ephemeralSuperblock: Superblock,
        cache: map<Reference, CacheLine>)
    | Unready

  predicate IsNotDirty(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralSuperblock.lbas
  }
  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralSuperblock.refcounts
  }
  predicate ValidLBAForNode(k: Constants, lba: LBA)
  {
    lba != SuperblockLBA(k)
  }

  datatype Step =
    | WriteBackStep(ref: Reference)
    | WriteBackSuperblockStep
    | DirtyStep(ref: Reference, block: Node)
    | AllocStep(ref: Reference, block: Node)
    | UnallocStep(ref: Reference)
    | PageInStep(ref: Reference)
    | PageInSuperblockStep
    | EvictStep(ref: Reference)

  predicate WFSuperblock(k: Constants, superblock: Superblock)
  {
    && SuperblockLBA(k) !in superblock.lbas.Values
    && superblock.lbas.Keys <= superblock.refcounts.Keys
  }

  predicate refCountsChangeConsistently(
      refcounts: map<Reference, int>,
      refcounts': map<Reference, int>,
      cache: map<Reference, CacheLine>,
      cache': map<Reference, CacheLine>,
      ref: Reference)
  {
    && (forall r :: r in refcounts && r != ref ==> (
      MapsTo(refcounts', r,
          refcounts[r] +
          (if ref in cache' && r in G.Successors(cache'[ref].block) then 1 else 0) -
          (if ref in cache && r in G.Successors(cache[ref].block) then 1 else 0)
      )
    ))
    && (ref in refcounts && ref in refcounts' ==>
      MapsTo(refcounts', ref,
          refcounts[ref] +
          (if ref in cache' && ref in G.Successors(cache'[ref].block) then 1 else 0) -
          (if ref in cache && ref in G.Successors(cache[ref].block) then 1 else 0)
      )
    )
  }

  predicate WriteBack(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.WriteOp?
    && ref in s.cache
    && ValidLBAForNode(k, dop.lba)
    && dop.lba !in s.persistentSuperblock.lbas.Values
    && dop.lba !in s.ephemeralSuperblock.lbas.Values
    && dop.sector == SectorBlock(s.cache[ref].block)
    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas[ref := dop.lba]
    && s'.ephemeralSuperblock.refcounts == s.ephemeralSuperblock.refcounts
    && s'.cache == s.cache
  }

  predicate WriteBackSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.WriteOp?
    && dop.lba == SuperblockLBA(k)
    && dop.sector == SectorSuperblock(s.ephemeralSuperblock)
    && s.cache.Keys <= s.ephemeralSuperblock.lbas.Keys
    && s' == s.(persistentSuperblock := s.ephemeralSuperblock)
  }

  predicate BlockPointsToValidReferences(block: Node, refcounts: map<Reference, int>)
  {
    forall ref | ref in G.Successors(block) :: ref in refcounts
  }

  predicate Dirty(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && dop.NoDiskOp?
    && ref in s.cache
    && s'.Ready?
    && s'.cache == s.cache[ref := CacheLine(block)]
    && s'.persistentSuperblock == s.persistentSuperblock

    && s'.ephemeralSuperblock.lbas == MapRemove(s.ephemeralSuperblock.lbas, {ref})

    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, s'.cache, ref)
    && s'.ephemeralSuperblock.refcounts.Keys == s.ephemeralSuperblock.refcounts.Keys
    && BlockPointsToValidReferences(block, s.ephemeralSuperblock.refcounts)
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
  {
    // Possibly allocs ref, possibly overwrites it.
    && s.Ready?
    && dop.NoDiskOp?
    && ref !in s.cache
    && !IsAllocated(s, ref)
    && s'.Ready?
    && s'.cache == s.cache[ref := CacheLine(block)]
    && s'.persistentSuperblock == s.persistentSuperblock

    && s'.ephemeralSuperblock.lbas == s.ephemeralSuperblock.lbas

    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, s'.cache, ref)
    && s'.ephemeralSuperblock.refcounts.Keys == s.ephemeralSuperblock.refcounts.Keys + {ref}
    && MapsTo(s'.ephemeralSuperblock.refcounts, ref, 0)
    && BlockPointsToValidReferences(block, s.ephemeralSuperblock.refcounts)
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?

    // This kind of sucks. It needs to be in cache so we know it's successors we can decrement
    // refcounts. TODO There is an optimization to be made such that we can unalloc leaves
    // which are not in cache (because they have no outgoing pointers)
    && ref in s.cache 

    // We can only dealloc this if nothing is pointing to it.
    && ref != G.Root()
    && MapsTo(s.ephemeralSuperblock.refcounts, ref, 0)

    && s'.Ready?
    && s'.persistentSuperblock == s.persistentSuperblock
    && s'.ephemeralSuperblock.lbas == MapRemove(s.ephemeralSuperblock.lbas, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && refCountsChangeConsistently(s.ephemeralSuperblock.refcounts, s'.ephemeralSuperblock.refcounts, s.cache, s'.cache, ref)
    && ref !in s'.ephemeralSuperblock.refcounts
    && s'.ephemeralSuperblock.refcounts.Keys == s.ephemeralSuperblock.refcounts.Keys - {ref}
  }

  predicate PageIn(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.ReadOp?
    && IsAllocated(s, ref)
    && IsNotDirty(s, ref)
    && s.ephemeralSuperblock.lbas[ref] == dop.lba
    && dop.sector.SectorBlock?
    && s' == s.(cache := s.cache[ref := CacheLine(dop.sector.block)])
  }

  predicate PageInSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Unready?
    && dop.ReadOp?
    && dop.lba == SuperblockLBA(k)
    && dop.sector.SectorSuperblock?
    && WFSuperblock(k, dop.sector.superblock)
    && dop.sector.superblock.lbas.Keys == dop.sector.superblock.refcounts.Keys
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

  predicate Init(k: Constants, s: Variables)
  {
    s == Unready
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case WriteBackStep(ref) => WriteBack(k, s, s', dop, ref)
      case WriteBackSuperblockStep => WriteBackSuperblock(k, s, s', dop)
      case DirtyStep(ref, block) => Dirty(k, s, s', dop, ref, block)
      case AllocStep(ref, block) => Alloc(k, s, s', dop, ref, block)
      case UnallocStep(ref) => Unalloc(k, s, s', dop, ref)
      case PageInStep(ref) => PageIn(k, s, s', dop, ref)
      case PageInSuperblockStep => PageInSuperblock(k, s, s', dop)
      case EvictStep(ref) => Evict(k, s, s', dop, ref)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step: Step :: NextStep(k, s, s', dop, step)
  }

  predicate InvReady(k: Constants, s: Variables)
  requires s.Ready?
  {
    && WFSuperblock(k, s.persistentSuperblock)
    && WFSuperblock(k, s.ephemeralSuperblock)
    && s.persistentSuperblock.lbas.Keys == s.persistentSuperblock.refcounts.Keys
    && s.cache.Keys <= s.ephemeralSuperblock.refcounts.Keys
    && s.ephemeralSuperblock.refcounts.Keys <= s.cache.Keys + s.ephemeralSuperblock.lbas.Keys
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
      /*
      forall ref
      ensures ref in s'.persistentSuperblock.lbas.Keys
         ==> ref in s'.persistentSuperblock.refcounts.Keys
      ensures ref in s'.persistentSuperblock.refcounts.Keys
         ==> ref in s'.persistentSuperblock.lbas.Keys
      {
      }
      assert s'.persistentSuperblock.lbas.Keys == s'.persistentSuperblock.refcounts.Keys;
      */
      assert InvReady(k, s');
    }
  }

  lemma DirtyStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Dirty(k, s, s', dop, ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      /*
      forall r | r in s'.ephemeralSuperblock.refcounts.Keys
      ensures r in s'.cache.Keys + s'.ephemeralSuperblock.lbas.Keys
      {
        if (r == ref) {
          assert r in s'.cache.Keys;
        } else if (r in s.cache.Keys) {
          assert r in s'.cache.Keys;
        } else {
          assert s.ephemeralSuperblock.refcounts.Keys
              == s'.ephemeralSuperblock.refcounts.Keys;
          assert r in s.ephemeralSuperblock.refcounts.Keys;
          assert r in s.cache.Keys + s.ephemeralSuperblock.lbas.Keys;
          assert r in s.ephemeralSuperblock.lbas.Keys;
          assert r in s'.ephemeralSuperblock.lbas.Keys;
        }
      }
      */
      assert InvReady(k, s');
    }
  }

  lemma AllocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Alloc(k, s, s', dop, ref, block)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
      assert InvReady(k, s');
    }
  }

  lemma UnallocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires Unalloc(k, s, s', dop, ref)
    ensures Inv(k, s')
  {
    if (s'.Ready?) {
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

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', dop, step)
    ensures Inv(k, s')
  {
    match step {
      case WriteBackStep(ref) => WriteBackStepPreservesInvariant(k, s, s', dop, ref);
      case WriteBackSuperblockStep => WriteBackSuperblockStepPreservesInvariant(k, s, s', dop);
      case DirtyStep(ref, block) => DirtyStepPreservesInvariant(k, s, s', dop, ref, block);
      case AllocStep(ref, block) => AllocStepPreservesInvariant(k, s, s', dop, ref, block);
      case UnallocStep(ref) => UnallocStepPreservesInvariant(k, s, s', dop, ref);
      case PageInStep(ref) => PageInStepPreservesInvariant(k, s, s', dop, ref);
      case PageInSuperblockStep => PageInSuperblockStepPreservesInvariant(k, s, s', dop);
      case EvictStep(ref) => EvictStepPreservesInvariant(k, s, s', dop, ref);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Next(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', dop, step);
    NextStepPreservesInvariant(k, s, s', dop, step);
  }

}
