include "BlockCache.dfy"
include "BlockCacheSystem.dfy"
include "CrashSafe.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "PivotBetreeSpec.dfy"

module {:extern} BetreeGraphBlockCache refines BlockCache {
  import G = PivotBetreeGraph
}

module BetreeGraphBlockCacheSystem refines BlockCacheSystem {
  import M = BetreeGraphBlockCache
}

module BlockCacheSystemCrashSafeBlockInterfaceRefinement {
  // Ideally we would prove the refinement for an arbitrary graph,
  // but if we imported the abstract BlockCacheSystem and CrashSafeBlockInterface
  // separately then we wouldn't know they were using the same graph.
  // So for now, we just prove the refinement specifically for BetreeGraph.
  import opened G = PivotBetreeGraph
  import BCS = BetreeGraphBlockCacheSystem
  import CSBI = CrashSafeBlockInterface
  import opened DAMTypes

  import opened Maps
  import opened Sequences

  import BC = BetreeGraphBlockCache
  import BI = PivotBetreeBlockInterface
  import D = Disk
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
  {
    //assert BI.Init(Ik(k), I(k, s).persistent);
  }

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

  lemma RefinesWriteBackIndirectionTable(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.WriteBackIndirectionTable(k.machine, s.machine, s'.machine, dop)
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
  decreases |ops|
  {
    if (|ops| == 0) {
    } else if (|ops| == 1) {
      RefinesOp(k, s, s', ops[0]);
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := DAMVariables(mid, s.disk);
      BCS.TransactionStepPreservesInvariant(k, s, smid, D.NoDiskOp, ops1);
      RefinesOpTransaction(k, s, smid, ops1);
      RefinesOpTransaction(k, smid, s', ops2);
      BI.JoinTransactions(Ik(k), I(k, s).ephemeral, I(k, smid).ephemeral, I(k, s').ephemeral, ops1, ops2);
    }
  }

  lemma RefinesTransaction(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp, ops: seq<Op>)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.Transaction(k.machine, s.machine, s'.machine, dop, ops)
  requires D.Stutter(k.disk, s.disk, s'.disk, dop)
  ensures CSBI.Next(Ik(k), I(k, s), I(k, s'))
  {
    RefinesOpTransaction(k, s, s', ops);
    assert BI.NextStep(Ik(k), I(k, s).ephemeral, I(k, s').ephemeral, BI.TransactionStep(ops));
    assert CSBI.NextStep(Ik(k), I(k, s), I(k, s'), CSBI.EphemeralMoveStep);
  }

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
        assert Successors(graph[lookup[|lookup|-2]]) == (iset r | r in s.machine.ephemeralIndirectionTable.graph[lookup[|lookup|-2]]);
        assert ref in s.machine.ephemeralIndirectionTable.graph[lookup[|lookup|-2]];
        assert false;
      }
    }

    assert refs !! BI.LiveReferences(Ik(k), I(k, s).ephemeral);
    assert refs <= I(k, s).ephemeral.view.Keys;

    forall ref | ref in refs
    ensures BI.Predecessors(I(k, s).ephemeral.view, ref) <= refs
    {
    }
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

  lemma RefinesPageInIndirectionTable(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.PageInIndirectionTable(k.machine, s.machine, s'.machine, dop)
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

  lemma RefinesNoOp(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, dop: DiskOp)
  requires BCS.Inv(k, s)
  requires BCS.Inv(k, s')
  requires BC.NoOp(k.machine, s.machine, s'.machine, dop)
  requires D.Read(k.disk, s.disk, s'.disk, dop)
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
          case WriteBackIndirectionTableStep => RefinesWriteBackIndirectionTable(k, s, s', dop);
          case UnallocStep(ref) => RefinesUnalloc(k, s, s', dop, ref);
          case PageInStep(ref) => RefinesPageIn(k, s, s', dop, ref);
          case PageInIndirectionTableStep => RefinesPageInIndirectionTable(k, s, s', dop);
          case EvictStep(ref) => RefinesEvict(k, s, s', dop, ref);
          case NoOpStep => RefinesNoOp(k, s, s', dop);
          case TransactionStep(ops) => RefinesTransaction(k, s, s', dop, ops);
        }
      }
      case CrashStep => {
        RefinesCrashStep(k, s, s');
      }
    }
  }
}
