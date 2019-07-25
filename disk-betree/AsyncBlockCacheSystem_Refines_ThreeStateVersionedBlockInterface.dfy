include "AsyncBlockCache.dfy"
include "AsyncBlockCacheSystem.dfy"
include "../lib/Maps.dfy"
include "../lib/sequences.dfy"

module AsyncBlockCacheSystem_Refines_ThreeStateVersionedBlockInterface {
  // Ideally we would prove the refinement for an arbitrary graph,
  // but if we imported the abstract BlockCacheSystem and CrashSafeBlockInterface
  // separately then we wouldn't know they were using the same graph.
  // So for now, we just prove the refinement specifically for BetreeGraph.
  import opened G = PivotBetreeGraph
  import BCS = BetreeGraphAsyncBlockCacheSystem
  import opened AsyncDiskModelTypes

  import opened Maps
  import opened Sequences

  import BC = BetreeGraphAsyncBlockCache
  import BI = PivotBetreeBlockInterface
  import D = AsyncDisk
  type DiskOp = BC.DiskOp

  function Ik(k: BCS.Constants) : BI.Constants
  {
    BI.Constants()
  }

  function {:opaque} PersistentGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(BCS.PersistentGraph(k, s))
  }

  function {:opaque} EphemeralGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(if BCS.EphemeralGraphOpt(k, s).Some? then
      BCS.EphemeralGraphOpt(k, s).value
    else
      BCS.PersistentGraph(k, s))
  }

  function {:opaque} FrozenGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(if BCS.FrozenGraphOpt(k, s).Some? then
      BCS.FrozenGraphOpt(k, s).value
    else
      BCS.PersistentGraph(k, s))
  }

  lemma InitImpliesGraphsEq(k: BCS.Constants, s: BCS.Variables)
  requires BCS.Init(k, s)
  ensures PersistentGraph(k, s) == FrozenGraph(k, s)
  ensures PersistentGraph(k, s) == EphemeralGraph(k, s)
  {
    reveal_PersistentGraph();
    reveal_FrozenGraph();
    reveal_EphemeralGraph();
  }

  lemma TransactionUpdate(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, ops: seq<Op>)
  requires BCS.Inv(k, s)
  requires s.disk == s'.disk
  requires BC.Transaction(k.machine, s.machine, s'.machine, D.NoDiskOp, ops)
  ensures BCS.Inv(k, s')
  ensures PersistentGraph(k, s') == PersistentGraph(k, s)
  ensures FrozenGraph(k, s') == FrozenGraph(k, s)
  ensures BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s)),
            BI.Variables(EphemeralGraph(k, s')),
            ops)
  decreases |ops|
  {
    reveal_PersistentGraph();
    reveal_FrozenGraph();
    reveal_EphemeralGraph();
    if |ops| == 0 {
    } else if |ops| == 1 {
      match ops[0] {
        case WriteOp(ref, block) => {
          BCS.DirtyStepUpdatesGraph(k, s, s', ref, block);
        }
        case AllocOp(ref, block) => {
          BCS.AllocStepUpdatesGraph(k, s, s', ref, block);
        }
      }
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := AsyncDiskModelVariables(mid, s.disk);
      TransactionUpdate(k, s, smid, ops1);
      TransactionUpdate(k, smid, s', ops2);
      BI.JoinTransactions(BI.Constants(),
        BI.Variables(EphemeralGraph(k, s)),
        BI.Variables(EphemeralGraph(k, smid)),
        BI.Variables(EphemeralGraph(k, s')),
        ops1, ops2);
    }
  }

  lemma RefinesReads(k: BCS.Constants, s: BCS.Variables, ops: seq<ReadOp>)
  requires BCS.Inv(k, s)
  requires BC.Reads(k.machine, s.machine, ops)
  ensures BI.Reads(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), ops)
  {
    reveal_EphemeralGraph();
    /*forall op | op in ops
    ensures BI.ReadStep(BI.Constants, BI.Variables(EphemeralGraph(k, s)), op)
    {
      assert s.machine.cache[op.ref] == op.node;
      assert op.ref in EphemeralGraph(k, s);
      assert EphemeralGraph(k, s)[op.ref] == op.node;
    }*/
  }

  lemma UnallocStepMeetsGCConditions(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables,
      dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires s'.disk == s.disk
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
  ensures BI.CanGCRefs(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), iset{ref})
  {
    reveal_EphemeralGraph();
    if (ref in BI.LiveReferences(BI.Constants(), BI.Variables(EphemeralGraph(k, s)))) {
      assert BI.ReachableReference(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), ref);
      var lookup :| BI.LookupIsValid(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), lookup) && Last(lookup) == ref;
      assert |lookup| > 1;
      var pred := lookup[|lookup| - 2];
      assert ref in G.Successors(EphemeralGraph(k, s)[pred]);
      assert false;
    }
  }

  // This is the uber lemma that explains how the graphs transform
  // for all the different step types

  lemma StepGraphs(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires BCS.NextStep(k, s, s', step)
  ensures BCS.Inv(k, s')

  ensures (step.CrashStep? ==>
      && PersistentGraph(k, s') == PersistentGraph(k, s)
      && FrozenGraph(k, s') == PersistentGraph(k, s)
      && EphemeralGraph(k, s') == PersistentGraph(k, s)
    )

  ensures (step.DiskInternalStep? ==>
      && (PersistentGraph(k, s') == PersistentGraph(k, s) || PersistentGraph(k, s') == FrozenGraph(k, s))
      && FrozenGraph(k, s') == FrozenGraph(k, s)
      && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    )

  ensures (step.MachineStep? && step.machineStep.FreezeStep? ==>
      && PersistentGraph(k, s') == PersistentGraph(k, s)
      && FrozenGraph(k, s') == EphemeralGraph(k, s)
      && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    )

  ensures (step.MachineStep? && step.machineStep.TransactionStep? ==>
      && PersistentGraph(k, s') == PersistentGraph(k, s)
      && FrozenGraph(k, s') == FrozenGraph(k, s)
      && BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s)),
            BI.Variables(EphemeralGraph(k, s')),
            step.machineStep.ops)
    )

  ensures (step.MachineStep? && step.machineStep.UnallocStep? ==>
      && PersistentGraph(k, s') == PersistentGraph(k, s)
      && FrozenGraph(k, s') == FrozenGraph(k, s)
      && EphemeralGraph(k, s') == IMapRemove1(EphemeralGraph(k, s), step.machineStep.ref)
    )

  ensures (step.MachineStep? && !(
      || step.machineStep.FreezeStep?
      || step.machineStep.TransactionStep?
      || step.machineStep.UnallocStep?)
    ) ==> (
      && PersistentGraph(k, s') == PersistentGraph(k, s)
      && FrozenGraph(k, s') == FrozenGraph(k, s)
      && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    )
  {
    BCS.NextStepPreservesInv(k, s, s', step);

    reveal_PersistentGraph();
    reveal_FrozenGraph();
    reveal_EphemeralGraph();

    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackReqStep(ref) => BCS.WriteBackReqStepPreservesGraphs(k, s, s', dop, ref);
          case WriteBackRespStep => BCS.WriteBackRespStepPreservesGraphs(k, s, s', dop);
          case WriteBackIndirectionTableReqStep => BCS.WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
          case WriteBackIndirectionTableRespStep => BCS.WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
          case UnallocStep(ref: Reference) => BCS.UnallocStepUpdatesGraph(k, s, s', dop, ref);
          case PageInReqStep(ref: Reference) => BCS.PageInReqStepPreservesGraphs(k, s, s', dop, ref);
          case PageInRespStep => BCS.PageInRespStepPreservesGraphs(k, s, s', dop);
          case PageInIndirectionTableReqStep => BCS.PageInIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
          case PageInIndirectionTableRespStep => BCS.PageInIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
          case EvictStep(ref: Reference) => BCS.EvictStepPreservesGraphs(k, s, s', dop, ref);
          case FreezeStep => BCS.FreezeStepPreservesGraphs(k, s, s', dop);
          case NoOpStep => { }
          case TransactionStep(ops) => TransactionUpdate(k, s, s', ops);
        }
      }
      case DiskInternalStep(step) => {
        match step {
          case ProcessReadStep(id) => BCS.ProcessReadPreservesGraphs(k, s, s', id);
          case ProcessWriteStep(id) => BCS.ProcessWritePreservesGraphs(k, s, s', id);
        }
      }
      case CrashStep => { }
    }
  }

  /*function I(k: BCS.Constants, s: BCS.Variables) : CSBI.Variables
  requires BCS.Inv(k, s)
  {
    CSBI.Variables(
      BI.Variables(MapToImap(persistentGraph)),
      BI.Variables(MapToImap(ephemeralGraph))
    )
  }*/


  /*
  lemma RefinesInit(k: BCS.Constants, s: BCS.Variables)
  requires BCS.Init(k, s)
  ensures BCS.Inv(k, s)
  ensures CSBI.Init(Ik(k), I(k, s))
  {
    //assert BI.Init(Ik(k), I(k, s).persistent);
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
  */
}
