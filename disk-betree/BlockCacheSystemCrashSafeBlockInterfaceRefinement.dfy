include "BlockCache.dfy"
include "BlockCacheSystem.dfy"
include "CrashSafe.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"

module BetreeGraphBlockCache refines BlockCache {
  import G = BetreeGraph
}

module BetreeGraphBlockCacheSystem refines BlockCacheSystem {
  import M = BetreeGraphBlockCache
}

module BlockCacheSystemCrashSafeBlockInterfaceRefinement {
  // Ideally we would prove the refinement for an arbitrary graph,
  // but if we imported the abstract BlockCacheSystem and CrashSafeBlockInterface
  // separately then we wouldn't know they were using the same graph.
  // So for now, we just prove the refinement specifically for BetreeGraph.
  import opened G = BetreeGraph
  import BCS = BetreeGraphBlockCacheSystem
  import CSBI = CrashSafeBlockInterface

  import opened Maps
  import opened Sequences

  import BC = BetreeGraphBlockCache
  import BI = BetreeBlockInterface
  import D = Disk
  import DiskBetree
  type DiskOp = BC.DiskOp

  function Ik(k: BCS.Constants) : CSBI.Constants
  {
    BI.Constants()
  }

  function I(k: BCS.Constants, s: BCS.Variables) : CSBI.Variables
  requires BCS.Inv(k, s)
  {
    var persistentGraph := BCS.PersistentGraph(k, s);
    var ephemeralGraph := if s.machine.Ready? then BCS.EphemeralGraph(k, s) else persistentGraph;
    CSBI.Variables(
      BI.Variables(MapToImap(persistentGraph)),
      BI.Variables(MapToImap(ephemeralGraph))
    )
  }

  lemma RefinesInit(k: BCS.Constants, s: BCS.Variables)
  requires BCS.Init(k, s)
  ensures BCS.Inv(k, s)
  ensures CSBI.Init(Ik(k), I(k, s))

  lemma RefinesWriteBack(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.WriteBack(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Write(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s).persistent == I(k, s').persistent;
    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.StutterStep);
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesWriteBackSuperblock(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.WriteBackSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Write(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s').ephemeral == I(k, s).ephemeral;
    assert I(k, s').persistent == I(k, s).ephemeral;
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.SyncStep);
  }

  lemma RefinesDirty(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, ref: Reference, block: Node)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Dirty(k.machine, s.machine, s'.machine, ref, block)
  requires s.disk == s'.disk
  ensures BI.OpStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, WriteOp(ref, block))
  {
  }

  lemma RefinesAlloc(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, ref: Reference, block: Node)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Alloc(k.machine, s.machine, s'.machine, ref, block)
  requires s.disk == s'.disk
  ensures BI.OpStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, AllocOp(ref, block))
  {
  }



  lemma RefinesOp(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, op: Op)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.OpStep(k.machine, s.machine, s'.machine, op)
  requires s.disk == s'.disk
  ensures BI.OpStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, op)
  {
    match op {
      case WriteOp(ref, block) => RefinesDirty(k, s, s', ref, block);
      case AllocOp(ref, block) => RefinesAlloc(k, s, s', ref, block);
    }
  }

  

  lemma RefinesOpTransaction(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, ops: seq<Op>)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.OpTransaction(k.machine, s.machine, s'.machine, ops)
  requires s.disk == s'.disk
  ensures BI.OpTransaction(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, ops)
  decreases ops
  {
    // TODO this is a conceptually simple induction but rather annoying anyway.
    // Idea: Have a helper function which splits an OpTransaction s .. s' into two OpTransactions s .. s'' .. s'
    // Recurse, then have a helper function glues them back together.
    if (|ops| == 1) {
      assert BC.OpStep(k.machine, s.machine, s'.machine, ops[0]);
      RefinesOp(k, s, s', ops[0]);
      assert BI.IsStatePath(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, ops, [I(k, s).ephemeral, I(k, s').ephemeral]);
      assert BI.OpTransaction(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, ops);
    } else {
      var path :| BC.IsStatePath(k.machine, s.machine, s'.machine, ops, path);
      var subpath := path[..|path| - 1];
      var subops := ops[..|ops| - 1];
      var penultimateMachine := Last(subpath);
      assert BC.IsStatePath(k.machine, s.machine, penultimateMachine, subops, subpath);
      BCS.TransactionStepPreservesInvariant(k, s, BCS.Variables(penultimateMachine, s.disk), D.NoDiskOp, subops);
      assert BCS.Inv(k, BCS.Variables(penultimateMachine, s.disk));
      RefinesOpTransaction(k, s, BCS.Variables(penultimateMachine, s.disk), subops);
      RefinesOp(k, BCS.Variables(penultimateMachine, s.disk), s', Last(ops));
      BI.OpTransactionAugment(Ik(k), I(k, s).ephemeral, I(k, BCS.Variables(penultimateMachine, s.disk)).ephemeral, I(k, s').ephemeral, subops, Last(ops));
      assert subops + [Last(ops)] == ops;
    }
  }



  lemma RefinesTransaction(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ops: seq<Op>)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Transaction(k.machine, s.machine, s'.machine, dop, ops)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))

  lemma RefinesUnalloc(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.GCStep(iset{ref}));
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    var refs := iset{ref};

    if (ref in BI.LiveReferences(Ik(k), I(k, s).ephemeral)) {
      assert BI.ReachableReference(Ik(k), I(k, s).ephemeral, ref);
      var lookup :| BI.LookupIsValid(Ik(k), I(k, s).ephemeral, lookup) && Last(lookup) == ref;
      if (|lookup| == 1) {
        assert ref == Root();
        assert false;
      } else {
        var graph := BCS.EphemeralGraph(k, s);
        assert lookup[|lookup|-1] in Successors(graph[lookup[|lookup|-2]]);
        assert ref in Successors(graph[lookup[|lookup|-2]]);
        assert lookup[|lookup|-2] in BCS.Predecessors(graph, ref);
        assert s.machine.ephemeralSuperblock.refcounts[ref] >= 1;
        assert false;
      }
      assert false;
    }

    assert refs !! BI.LiveReferences(Ik(k), I(k, s).ephemeral);
    assert refs <= I(k, s).ephemeral.view.Keys;
    assert BI.ClosedUnderPredecessor(I(k, s).ephemeral.view, refs);
    assert I(k, s').ephemeral.view == IMapRemove(I(k, s).ephemeral.view, refs);

    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.GCStep(iset{ref}));
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesPageIn(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.PageIn(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Read(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s).persistent == I(k, s').persistent;
    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.StutterStep);
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesPageInSuperblock(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.PageInSuperblock(k.machine, s.machine, s'.machine, dop)
  requires D.Read(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s).persistent == I(k, s').persistent;
    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.StutterStep);
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesEvict(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Evict(k.machine, s.machine, s'.machine, dop, ref)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s).persistent == I(k, s').persistent;
    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.StutterStep);
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

  lemma RefinesCrashStep(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Init(k.machine, s'.machine)
  requires s.disk == s'.disk
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    assert I(k, s').ephemeral == I(k, s).persistent;
    assert I(k, s').persistent == I(k, s).persistent;
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.CrashStep);
  }

  lemma RefinesNextStep(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires BCS.NextStep(k, s, s', step)
  ensures BCS.Inv(k, s')
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    BCS.NextPreservesInv(k, s, s');
    match step {
      case MachineStep(dop: DiskOp) => {
        var mstep :| BC.NextStep(k.machine, s.machine, s'.machine, dop, mstep);
        match mstep {
          case WriteBackStep(ref) => RefinesWriteBack(k, s, s', dop, ref);
          case WriteBackSuperblockStep => RefinesWriteBackSuperblock(k, s, s', dop);
          case UnallocStep(ref) => RefinesUnalloc(k, s, s', dop, ref);
          case PageInStep(ref) => RefinesPageIn(k, s, s', dop, ref);
          case PageInSuperblockStep => RefinesPageInSuperblock(k, s, s', dop);
          case EvictStep(ref) => RefinesEvict(k, s, s', dop, ref);

          //case DirtyStep(ref, block) => RefinesDirty(k, s, s', dop, ref, block);
          //case AllocStep(ref, block) => RefinesAlloc(k, s, s', dop, ref, block);
          case TransactionStep(ops) => RefinesTransaction(k, s, s', dop, ops);
        }
      }
      case CrashStep => {
        RefinesCrashStep(k, s, s');
      }
    }
  }
}
