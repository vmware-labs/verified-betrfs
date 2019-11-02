include "BlockCache.i.dfy"
include "BlockCacheSystem.i.dfy"
include "ThreeStateVersioned.s.dfy"
include "../lib/Maps.s.dfy"
include "../lib/sequences.i.dfy"

module BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface {
  // Ideally we would prove the refinement for an arbitrary graph,
  // but if we imported the abstract BlockCacheSystem and CrashSafeBlockInterface
  // separately then we wouldn't know they were using the same graph.
  // So for now, we just prove the refinement specifically for BetreeGraph.
  import opened G = PivotBetreeGraph
  import BCS = BetreeGraphBlockCacheSystem
  import opened AsyncSectorDiskModelTypes

  import opened Maps
  import opened Sequences
  import opened Options
  import opened NativeTypes

  import BC = BetreeGraphBlockCache
  import BI = PivotBetreeBlockInterface
  import D = AsyncSectorDisk
  import ThreeState = ThreeStateTypes
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
    MapToImap(
      if BCS.FrozenGraphOpt(k, s).Some? then
        BCS.FrozenGraphOpt(k, s).value
      else
        BCS.PersistentGraph(k, s)
    )
  }
  
  function SyncReqState(k: BCS.Constants, s: BCS.Variables, status: BC.SyncReqStatus) : ThreeState.SyncReqStatus
  {
    match status {
      case State1 => ThreeState.State1
      case State2 => (
        // It's possible that the disk has written the superblock but the BlockCache
        // hasn't heard about it yet. In that case, we need to upgrade State2 to State1.
        if s.machine.Ready? && s.machine.outstandingIndirectionTableWrite.Some?
            && s.machine.outstandingIndirectionTableWrite.value in s.disk.respWrites then
          ThreeState.State1
        else
          ThreeState.State2
      )
      case State3 => ThreeState.State3
    }
  }

  function {:opaque} SyncReqs(k: BCS.Constants, s: BCS.Variables) : map<int, ThreeState.SyncReqStatus>
  requires BCS.Inv(k, s)
  {
    map id | 0 <= id < 0x1_0000_0000_0000_0000 && id as uint64 in s.machine.syncReqs :: SyncReqState(k, s, s.machine.syncReqs[id as uint64])
  }

  predicate IsPersistStep(k: BCS.Constants, s: BCS.Variables, step: BCS.Step)
  {
    && s.machine.Ready?
    && step.DiskInternalStep?
    && step.step.ProcessWriteStep?
    && Some(step.step.id) == s.machine.outstandingIndirectionTableWrite
  }

  predicate IsFreezeStep(step: BCS.Step)
  {
    && step.MachineStep?
    && step.machineStep.FreezeStep?
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
  ensures SyncReqs(k, s) == SyncReqs(k, s');
  decreases |ops|
  {
    reveal_PersistentGraph();
    reveal_FrozenGraph();
    reveal_EphemeralGraph();
    if |ops| == 0 {
    } else if |ops| == 1 {
      reveal_SyncReqs();
      match ops[0] {
        case WriteOp(ref, block) => {
          BCS.DirtyStepUpdatesGraph(k, s, s', ref, block);
          assert s.machine.syncReqs == s'.machine.syncReqs;
        }
        case AllocOp(ref, block) => {
          BCS.AllocStepUpdatesGraph(k, s, s', ref, block);
          assert s.machine.syncReqs == s'.machine.syncReqs;
        }
      }
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := AsyncSectorDiskModelVariables(mid, s.disk);
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
      && (!IsPersistStep(k, s, step) ==> PersistentGraph(k, s') == PersistentGraph(k, s))
      && (IsPersistStep(k, s, step) ==> PersistentGraph(k, s') == FrozenGraph(k, s))
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
          case PushSyncReqStep(id) => BCS.PushSyncReqStepPreservesGraphs(k, s, s', dop, id);
          case PopSyncReqStep(id) => BCS.PopSyncReqStepPreservesGraphs(k, s, s', dop, id);
          case NoOpStep => { }
          case TransactionStep(ops) => TransactionUpdate(k, s, s', ops);
        }
      }
      case DiskInternalStep(step) => {
        match step {
          case ProcessReadStep(id) => BCS.ProcessReadPreservesGraphs(k, s, s', id);
          case ProcessReadFailureStep(id) => BCS.ProcessReadFailurePreservesGraphs(k, s, s', id);
          case ProcessWriteStep(id) => BCS.ProcessWritePreservesGraphs(k, s, s', id);
        }
      }
      case CrashStep => { }
    }
  }

  lemma StepSyncReqs(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires BCS.NextStep(k, s, s', step)
  ensures BCS.Inv(k, s')

  ensures IsPersistStep(k, s, step) ==> SyncReqs(k, s') == ThreeState.SyncReqs2to1(SyncReqs(k, s))
  ensures IsFreezeStep(step) ==> SyncReqs(k, s') == ThreeState.SyncReqs3to2(SyncReqs(k, s))
  ensures step.MachineStep? && step.machineStep.PushSyncReqStep? ==>
      && step.machineStep.id as int !in SyncReqs(k, s)
      && SyncReqs(k, s') == SyncReqs(k, s)[step.machineStep.id as int := ThreeState.State3]
  ensures step.MachineStep? && step.machineStep.PopSyncReqStep? ==>
      && step.machineStep.id as int in SyncReqs(k, s)
      && SyncReqs(k, s)[step.machineStep.id as int] == ThreeState.State1
      && SyncReqs(k, s') == MapRemove1(SyncReqs(k, s), step.machineStep.id as int)
  ensures step.CrashStep? ==> SyncReqs(k, s') == map[]
  ensures
    && !IsPersistStep(k, s, step)
    && !IsFreezeStep(step)
    && !step.CrashStep?
    && !(step.MachineStep? && step.machineStep.PushSyncReqStep?)
    && !(step.MachineStep? && step.machineStep.PopSyncReqStep?)
    ==> SyncReqs(k, s') == SyncReqs(k, s)
  {
    reveal_SyncReqs();
    BCS.NextStepPreservesInv(k, s, s', step);

    if (
      && !IsPersistStep(k, s, step)
      && !IsFreezeStep(step)
      && !step.CrashStep?
      && !(step.MachineStep? && step.machineStep.PushSyncReqStep?)
      && !(step.MachineStep? && step.machineStep.PopSyncReqStep?)
    ) {
      match step {
        case MachineStep(dop, machineStep) => {
          match machineStep {
            case WriteBackReqStep(ref) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case WriteBackRespStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case WriteBackIndirectionTableReqStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case WriteBackIndirectionTableRespStep => {
              /*assert SyncReqState(k, s, BC.State1) == SyncReqState(k, s', BC.State1);
              assert SyncReqState(k, s, BC.State2) == SyncReqState(k, s', BC.State1);
              assert SyncReqState(k, s, BC.State3) == SyncReqState(k, s', BC.State3);
              forall id | id in SyncReqs(k, s)
              ensures id in SyncReqs(k, s')
              ensures SyncReqs(k, s)[id] == SyncReqs(k, s')[id]
              {
              }
              forall id | id in SyncReqs(k, s')
              ensures id in SyncReqs(k, s)
              {
              }*/
              assert SyncReqs(k,s) == SyncReqs(k, s');
            }
            case UnallocStep(ref: Reference) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case PageInReqStep(ref: Reference) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case PageInRespStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case PageInIndirectionTableReqStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case PageInIndirectionTableRespStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case EvictStep(ref: Reference) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case FreezeStep => assert false;
            case PushSyncReqStep(id) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case PopSyncReqStep(id) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case NoOpStep => assert SyncReqs(k,s) == SyncReqs(k,s');
            case TransactionStep(ops) => {
              TransactionUpdate(k, s, s', ops);
              assert SyncReqs(k,s) == SyncReqs(k,s');
            }
          }
        }
        case DiskInternalStep(step) => {
          match step {
            case ProcessReadStep(id) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case ProcessReadFailureStep(id) => assert SyncReqs(k,s) == SyncReqs(k,s');
            case ProcessWriteStep(id) => assert SyncReqs(k,s) == SyncReqs(k,s');
          }
        }
        case CrashStep => assert false;
      }

      assert SyncReqs(k,s) == SyncReqs(k,s');
    }
  }
}
