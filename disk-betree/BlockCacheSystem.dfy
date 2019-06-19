include "Disk.dfy"
include "BlockCache.dfy"
include "../lib/Maps.dfy"

abstract module BlockCacheSystem {
  import opened Maps

  import M : BlockCache
  import D = Disk

  type LBA = D.LBA
  type Sector = M.Sector
  type DiskOp = M.DiskOp

  datatype Constants = Constants(machine: M.Constants, disk: D.Constants)
  // TODO TTY
  // TODO disk message queue for async disk operations
  datatype Variables = Variables(
    machine: M.Variables,
    disk: D.Variables<Sector>)

  predicate Init(k: Constants, s: Variables)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
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

  type Superblock = M.Superblock
  type Reference = M.G.Reference
  type Node = M.G.Node

  predicate WFDisk(k: Constants, blocks: map<LBA, Sector>)
  {
    && var superblockLBA := M.SuperblockLBA(k.machine);
    && superblockLBA in blocks
    && blocks[superblockLBA].SectorSuperblock?
    && var superblock := blocks[superblockLBA].superblock;
    && superblock.refcounts.Keys == superblock.lbas.Keys
  }

  predicate WFSuperblockWrtDisk(k: Constants, superblock: Superblock, blocks: map<LBA, Sector>)
  {
    && (forall ref | ref in superblock.lbas ::
        && superblock.lbas[ref] in blocks
        && blocks[superblock.lbas[ref]].SectorBlock?)
  }

  function DiskSuperblock(k: Constants, blocks: map<LBA, Sector>) : Superblock
  requires WFDisk(k, blocks)
  {
    blocks[M.SuperblockLBA(k.machine)].superblock
  }

  function RefMapOfDisk(
      k: Constants,
      superblock: Superblock,
      blocks: map<LBA, Sector>) : map<Reference, Node>
  requires WFDisk(k, blocks)
  requires WFSuperblockWrtDisk(k, superblock, blocks)
  {
    map ref | ref in superblock.lbas :: blocks[superblock.lbas[ref]].block
  }

  function Graph(superblock: set<Reference>, block: map<Reference, Node>) : map<Reference, Node>
  requires superblock <= block.Keys
  {
    map ref | ref in superblock :: block[ref]
  }

  function PersistentGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires WFDisk(k, s.disk.blocks)
  requires WFSuperblockWrtDisk(k, DiskSuperblock(k, s.disk.blocks), s.disk.blocks)
  {
    Graph(
      DiskSuperblock(k, s.disk.blocks).refcounts.Keys,
      RefMapOfDisk(k, DiskSuperblock(k, s.disk.blocks), s.disk.blocks))
  }

  function CacheMap(cache: map<Reference, M.CacheLine>) : map<Reference, Node>
  {
    map ref | ref in cache :: cache[ref].block
  }

  function EphemeralGraph(k: Constants, s: Variables) : map<Reference, Node>
  requires M.Inv(k.machine, s.machine)
  requires s.machine.Ready?
  requires WFDisk(k, s.disk.blocks)
  requires WFSuperblockWrtDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks)
  {
    /*assert s.machine.ephemeralSuperblock.refcounts.Keys
        <= s.machine.ephemeralSuperblock.lbas.Keys + s.machine.cache.Keys
        == MapUnionPreferB(RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks), CacheMap(s.machine.cache)).Keys;*/
    Graph(
      s.machine.ephemeralSuperblock.refcounts.Keys,
      MapUnionPreferB(RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks), CacheMap(s.machine.cache))
    )
  }

  predicate CleanCacheEntriesAreCorrect(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall ref | ref in s.machine.cache ::
      ref in s.machine.ephemeralSuperblock.lbas ==>
      MapsTo(
          s.disk.blocks,
          s.machine.ephemeralSuperblock.lbas[ref],
          M.SectorBlock(s.machine.cache[ref].block))
  }

  function Predecessors(graph: map<Reference, Node>, ref: Reference) : set<Reference>
  {
    set r | r in graph && ref in M.G.Successors(graph[r])
  }

  predicate RefcountsAgree(refcounts: map<Reference, int>, graph: map<Reference, Node>)
  {
    forall ref | ref in refcounts :: refcounts[ref] == |Predecessors(graph, ref)|
  }

  predicate NoDanglingPointers(graph: map<Reference, Node>)
  {
    forall r1, r2 {:trigger r2 in M.G.Successors(graph[r1])}
      | r1 in graph && r2 in M.G.Successors(graph[r1])
      :: r2 in graph
  }

  predicate Inv(k: Constants, s: Variables) {
    && M.Inv(k.machine, s.machine)
    && WFDisk(k, s.disk.blocks)
    && WFSuperblockWrtDisk(k, DiskSuperblock(k, s.disk.blocks), s.disk.blocks)
    && RefcountsAgree(DiskSuperblock(k, s.disk.blocks).refcounts, PersistentGraph(k, s))
    && NoDanglingPointers(PersistentGraph(k, s))
    && (s.machine.Ready? ==>
      && s.machine.persistentSuperblock == DiskSuperblock(k, s.disk.blocks)
      && WFSuperblockWrtDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks)
      && RefcountsAgree(s.machine.ephemeralSuperblock.refcounts, EphemeralGraph(k, s))
      && NoDanglingPointers(EphemeralGraph(k, s))
      && CleanCacheEntriesAreCorrect(k, s)
    )
  }

  lemma WriteBackStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    assert PersistentGraph(k, s) == PersistentGraph(k, s');
    assert EphemeralGraph(k, s) == EphemeralGraph(k, s');
  }

  lemma WriteBackSuperblockStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.WriteBackSuperblock(k.machine, s.machine, s'.machine, dop)
    requires D.Write(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    //assert M.Inv(k.machine, s'.machine);
    //assert WFDisk(k, s'.disk.blocks);
    //assert WFSuperblockWrtDisk(k, DiskSuperblock(k, s'.disk.blocks), s'.disk.blocks);

    assert DiskSuperblock(k, s'.disk.blocks) == s.machine.ephemeralSuperblock;

    /*
    forall ref | ref in CacheMap(s.machine.cache)
    ensures MapsTo(
          RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks),
          ref, CacheMap(s.machine.cache)[ref])
    {
    }
    */

    assert RefMapOfDisk(k, DiskSuperblock(k, s'.disk.blocks), s'.disk.blocks)
        == RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks)
        == MapUnionPreferB(RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks), CacheMap(s.machine.cache));
    assert PersistentGraph(k, s') == EphemeralGraph(k, s);

    //assert RefcountsAgree(DiskSuperblock(k, s'.disk.blocks).refcounts, PersistentGraph(k, s'));

    //assert s'.machine.persistentSuperblock == DiskSuperblock(k, s'.disk.blocks);
    //assert WFSuperblockWrtDisk(k, s'.machine.ephemeralSuperblock, s'.disk.blocks);
    //assert RefcountsAgree(s'.machine.ephemeralSuperblock.refcounts, EphemeralGraph(k, s'));
  }

  lemma RefcountConservation(k: Constants, s: Variables, s': Variables, graph: map<Reference, Node>, graph': map<Reference, Node>, ref: Reference, r: Reference)
  requires Inv(k, s);
  requires M.Inv(k.machine, s'.machine)
  requires s'.machine.Ready?
  requires s'.disk == s.disk
  requires WFDisk(k, s'.disk.blocks)
  requires WFSuperblockWrtDisk(k, s'.machine.ephemeralSuperblock, s'.disk.blocks)
  requires s.machine.Ready?
  requires s'.machine.Ready?
  requires graph == EphemeralGraph(k, s)
  requires graph' == EphemeralGraph(k, s')
  requires ref in s.machine.ephemeralSuperblock.lbas ==> ref in s.machine.cache
  requires ref in s'.machine.ephemeralSuperblock.lbas ==> ref in s'.machine.cache
  requires MapRemove(s.machine.cache, {ref}) == MapRemove(s'.machine.cache, {ref})
  requires MapRemove(s.machine.ephemeralSuperblock.lbas, {ref}) == MapRemove(s'.machine.ephemeralSuperblock.lbas, {ref})

  ensures |Predecessors(graph, r)| - (if ref in s.machine.cache && r in M.G.Successors(s.machine.cache[ref].block) then 1 else 0)
       == |Predecessors(graph', r)| - (if ref in s'.machine.cache && r in M.G.Successors(s'.machine.cache[ref].block) then 1 else 0)
  {
    assert |Predecessors(graph, r)| - (if ref in s.machine.cache && r in M.G.Successors(s.machine.cache[ref].block) then 1 else 0) == |Predecessors(graph, r) - {ref}|;
    assert |Predecessors(graph', r)| - (if ref in s'.machine.cache && r in M.G.Successors(s'.machine.cache[ref].block) then 1 else 0) == |Predecessors(graph', r) - {ref}|;

    forall r1 | r1 in Predecessors(graph, r) - {ref}
    ensures r1 in Predecessors(graph', r) - {ref}
    {
      assert r1 != ref;
      if (r1 in s'.machine.ephemeralSuperblock.lbas) {
        assert r1 in MapRemove(s'.machine.ephemeralSuperblock.lbas, {ref});
        assert r1 in MapRemove(s.machine.ephemeralSuperblock.lbas, {ref});
        assert r1 in s.machine.ephemeralSuperblock.lbas;
        assert s.machine.ephemeralSuperblock.lbas[r1] == 
               s'.machine.ephemeralSuperblock.lbas[r1];
        assert RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks)[r1]
            == RefMapOfDisk(k, s'.machine.ephemeralSuperblock, s'.disk.blocks)[r1];
      }
      if (r1 in s.machine.ephemeralSuperblock.lbas) {
        assert r1 in MapRemove(s.machine.ephemeralSuperblock.lbas, {ref});
        assert r1 in MapRemove(s'.machine.ephemeralSuperblock.lbas, {ref});
        assert r1 in s'.machine.ephemeralSuperblock.lbas;
        assert s'.machine.ephemeralSuperblock.lbas[r1] == 
               s.machine.ephemeralSuperblock.lbas[r1];
        assert RefMapOfDisk(k, s.machine.ephemeralSuperblock, s.disk.blocks)[r1]
            == RefMapOfDisk(k, s'.machine.ephemeralSuperblock, s'.disk.blocks)[r1];
      }

      if (r1 in s.machine.cache) {
        assert s.machine.cache.Keys - {ref} == s'.machine.cache.Keys - {ref};
        assert r1 in (s.machine.cache.Keys - {ref});
        assert r1 in (s'.machine.cache.Keys - {ref});
        assert r1 in s'.machine.cache;
        assert graph[r1] == s.machine.cache[r1].block
            == s'.machine.cache[r1].block
            == graph'[r1];
        assert MapsTo(graph', r1, graph[r1]);
      } else {
        assert MapsTo(graph', r1, graph[r1]);
      }
      assert r1 in Predecessors(graph', r) - {ref};
    }

    forall r1 | r1 in Predecessors(graph', r) - {ref}
    ensures r1 in Predecessors(graph, r) - {ref}
    {
      assert r1 != ref;
      if (r1 in s'.machine.cache) {
        assert MapsTo(graph, r1, graph[r1]);
      } else {
        assert MapsTo(graph, r1, graph[r1]);
      }
      assert r1 in Predecessors(graph, r) - {ref};
    }

    assert Predecessors(graph, r) - {ref} == Predecessors(graph', r) - {ref};
  }

  lemma DirtyStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, dop, ref, block)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    var refcounts := s.machine.ephemeralSuperblock.refcounts;
    var refcounts' := s'.machine.ephemeralSuperblock.refcounts;
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;

    forall r | r in refcounts'
    ensures refcounts'[r] == |Predecessors(graph', r)|
    {
      RefcountConservation(k, s, s', graph, graph', ref, r);

      /*
      assert refcounts'[r]
          == refcounts[r] +
            (if ref in cache' && r in M.Successors(cache'[ref].block) then 1 else 0) -
            (if ref in cache && r in M.Successors(cache[ref].block) then 1 else 0)
          == |Predecessors(graph, r)| +
            (if ref in cache' && r in M.Successors(cache'[ref].block) then 1 else 0) -
            (if ref in cache && r in M.Successors(cache[ref].block) then 1 else 0)
          == |Predecessors(graph', r)|;
      */
    }
  }

  lemma AllocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, dop, ref, block)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    var refcounts := s.machine.ephemeralSuperblock.refcounts;
    var refcounts' := s'.machine.ephemeralSuperblock.refcounts;
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;

    forall r | r in refcounts'
    ensures refcounts'[r] == |Predecessors(graph', r)|
    {
      if (r == ref) {
        //assert ref !in M.Successors(block);
        //assert ref !in s.machine.cache;
        //assert ref !in M.Successors(s'.machine.cache[ref].block);

        RefcountConservation(k, s, s', graph, graph', ref, r);
        /*if (|Predecessors(graph, r)| != 0) {
          var x :| x in Predecessors(graph, r);
          assert r in M.Successors(graph[x]);
          assert r in graph;
          assert false;
        }*/
        assert |Predecessors(graph, r)| == 0;

        assert |Predecessors(graph', r)| == 0;
        assert refcounts'[r] == 0;
      } else {
        RefcountConservation(k, s, s', graph, graph', ref, r);
      }
    }

    /*forall r1, r2 | r1 in graph && r2 in M.Successors(graph[r1])
    ensures r2 in graph'
    {
      /*
      if (r_node in graph) {
        assert node in graph.Values;
        assume false;
        assert r in graph;
        assert r in graph';
      } else {
        assume false;
        assert node == block;
        assert r in graph;
        assert r in graph';
      }
      */
    }*/
  }

  lemma UnallocStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    var refcounts := s.machine.ephemeralSuperblock.refcounts;
    var refcounts' := s'.machine.ephemeralSuperblock.refcounts;
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;

    forall r | r in refcounts'
    ensures refcounts'[r] == |Predecessors(graph', r)|
    {
      assert r != ref;
      RefcountConservation(k, s, s', graph, graph', ref, r);
    }
  }

  lemma PageInStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageIn(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    assert PersistentGraph(k, s) == PersistentGraph(k, s');
    assert EphemeralGraph(k, s) == EphemeralGraph(k, s');
  }

  lemma PageInSuperblockStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires M.PageInSuperblock(k.machine, s.machine, s'.machine, dop)
    requires D.Read(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    assert PersistentGraph(k, s) == PersistentGraph(k, s');
    assert PersistentGraph(k, s) == EphemeralGraph(k, s');
  }

  lemma EvictStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    assert EphemeralGraph(k, s) == EphemeralGraph(k, s');
  }

  lemma MachineStepPreservesInvariant(k: Constants, s: Variables, s': Variables, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', dop)
    ensures Inv(k, s')
  {
    var step :| M.NextStep(k.machine, s.machine, s'.machine, dop, step);
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
