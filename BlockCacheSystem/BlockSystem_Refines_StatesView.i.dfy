include "../BlockCacheSystem/BlockSystem.i.dfy"
include "../Versions/StatesView.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/sequences.i.dfy"

module BlockSystem_Refines_StatesView {
  import opened G = PivotBetreeGraph
  import System = BlockSystem
  import opened AsyncSectorDiskModelTypes

  import opened Maps
  import opened Sequences
  import opened Options
  import opened NativeTypes
  import opened ViewOp
  import opened DiskLayout

  import BC = BlockCache
  import BI = PivotBetreeBlockInterface
  import D = BlockDisk
  type DiskOp = BC.DiskOp

  predicate IsTransactionStep(step: System.Step)
  {
    && step.MachineStep?
    && step.machineStep.TransactionStep?
  }

  function DiskGraphMap(s: System.Variables)
    : imap<Location, imap<Reference, Node>>
  {
    System.DiskGraphMap(s)
  }

  function FrozenGraph(s: System.Variables) : Option<imap<Reference, Node>>
  {
    System.FrozenGraphOpt(s)
  }

  function EphemeralGraph(s: System.Variables) : Option<imap<Reference, Node>>
  {
    System.EphemeralGraphOpt(s)
  }

  function PersistentLoc(s: System.Variables) : Option<Location>
  {
    System.PersistentLoc(s)
  }

  function FrozenLoc(s: System.Variables) : Option<Location>
  {
    System.FrozenLoc(s)
  }

  predicate UpdateAllEq(
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(s)
    && System.Inv(s')
    && DiskGraphMap(s') == DiskGraphMap(s)
    && FrozenGraph(s') == FrozenGraph(s)
    && EphemeralGraph(s') == EphemeralGraph(s)
    && PersistentLoc(s') == PersistentLoc(s)
    && FrozenLoc(s') == FrozenLoc(s)
  }

  predicate UpdateCrash(
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(s)
    && System.Inv(s')
    && System.DiskChangesPreservesPersistentAndFrozen(s, s')
    && FrozenGraph(s') == None
    && EphemeralGraph(s') == None
    && PersistentLoc(s') == None
    && FrozenLoc(s') == None
  }

  predicate UpdateObtainPersistentLoc(
    s: System.Variables,
    s': System.Variables,
    vop: VOp)
  {
    && vop.SendPersistentLocOp?
    && System.Inv(s)
    && System.Inv(s')
    && PersistentLoc(s) == None
    && DiskGraphMap(s') == DiskGraphMap(s)
    && FrozenGraph(s') == FrozenGraph(s)
    && vop.loc in DiskGraphMap(s)
    && EphemeralGraph(s') == Some(DiskGraphMap(s)[vop.loc])
    && PersistentLoc(s') == Some(vop.loc)
    && FrozenLoc(s') == FrozenLoc(s)
  }

  predicate UpdateFreeze(
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(s)
    && System.Inv(s')
    && DiskGraphMap(s') == DiskGraphMap(s)
    && FrozenGraph(s') == EphemeralGraph(s)
    && EphemeralGraph(s') == EphemeralGraph(s)
    && PersistentLoc(s') == PersistentLoc(s)
    && FrozenLoc(s') == None
  }

  predicate UpdateDiskChange(
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(s)
    && System.Inv(s')
    && System.DiskChangesPreservesPersistentAndFrozen(s, s')
    && FrozenGraph(s') == FrozenGraph(s)
    && EphemeralGraph(s') == EphemeralGraph(s)
    && PersistentLoc(s') == PersistentLoc(s)
    && FrozenLoc(s') == FrozenLoc(s)
  }

  predicate UpdateProvideFrozenLoc(
    s: System.Variables,
    s': System.Variables,
    vop: VOp)
  {
    && vop.SendFrozenLocOp?
    && FrozenLoc(s) == None
    && FrozenLoc(s') == Some(vop.loc)
    && FrozenGraph(s).Some?
    && FrozenLoc(s').value in DiskGraphMap(s)
    && DiskGraphMap(s)[FrozenLoc(s').value] == FrozenGraph(s).value
    && DiskGraphMap(s') == DiskGraphMap(s)
    && FrozenGraph(s') == FrozenGraph(s)
    && EphemeralGraph(s') == EphemeralGraph(s)
    && PersistentLoc(s') == PersistentLoc(s)
  }

  predicate UpdateForgetOld(
    s: System.Variables,
    s': System.Variables)
  {
    && DiskGraphMap(s') == DiskGraphMap(s)
    && FrozenGraph(s') == None
    && EphemeralGraph(s') == EphemeralGraph(s)
    && FrozenLoc(s') == None
    && PersistentLoc(s') == FrozenLoc(s)
  }

  predicate UpdateUnalloc(
    s: System.Variables,
    s': System.Variables,
    step: System.Step)
  {
    && System.Inv(s)
    && System.Inv(s')

    && step.MachineStep?
    && step.machineStep.UnallocStep?

    && DiskGraphMap(s') == DiskGraphMap(s)
    && PersistentLoc(s') == PersistentLoc(s)
    && FrozenLoc(s') == FrozenLoc(s)
    && FrozenGraph(s') == FrozenGraph(s)

    && EphemeralGraph(s).Some?
    && EphemeralGraph(s').Some?

    && EphemeralGraph(s').value == IMapRemove1(EphemeralGraph(s).value, step.machineStep.ref)
  }

  predicate UpdateTransaction(
    s: System.Variables,
    s': System.Variables,
    step: System.Step)
  {
    && IsTransactionStep(step)
    && System.Inv(s)
    && System.Inv(s')

    && step.MachineStep?
    && step.machineStep.TransactionStep?

    && DiskGraphMap(s') == DiskGraphMap(s)
    && PersistentLoc(s') == PersistentLoc(s)
    && FrozenLoc(s') == FrozenLoc(s)
    && FrozenGraph(s') == FrozenGraph(s)

    && EphemeralGraph(s).Some?
    && EphemeralGraph(s').Some?

    && BI.OpTransaction(
            BI.Variables(EphemeralGraph(s).value),
            BI.Variables(EphemeralGraph(s').value),
            step.machineStep.ops)
  }

  lemma OpTransactionUpdate(s: System.Variables, s': System.Variables, ops: seq<Op>)
  requires System.Inv(s)
  requires s.disk == s'.disk
  requires BC.OpTransaction(s.machine, s'.machine, ops)
  requires s.machine.Ready?
  ensures System.Inv(s')
  ensures DiskGraphMap(s') == DiskGraphMap(s)
  ensures PersistentLoc(s') == PersistentLoc(s)
  ensures FrozenLoc(s') == FrozenLoc(s)
  ensures FrozenGraph(s') == FrozenGraph(s)
  ensures s'.machine.Ready?
  ensures EphemeralGraph(s).Some?
  ensures EphemeralGraph(s').Some?
  ensures BI.OpTransaction(
            BI.Variables(EphemeralGraph(s).value),
            BI.Variables(EphemeralGraph(s').value),
            ops)

  decreases |ops|
  {
    //reveal_PersistentGraph();
    //reveal_FrozenGraph();
    //reveal_EphemeralGraph();
    if |ops| == 0 {
    } else if |ops| == 1 {
      System.OpPreservesInv(s, s', ops[0]);
      match ops[0] {
        case WriteOp(ref, block) => {
          System.DirtyStepUpdatesGraph(s, s', ref, block);
          assert BI.Write(
              BI.Variables(EphemeralGraph(s).value),
              BI.Variables(EphemeralGraph(s').value),
              ref, block);
          assert BI.OpStep(
              BI.Variables(EphemeralGraph(s).value),
              BI.Variables(EphemeralGraph(s').value),
              ops[0]);
        }
        case AllocOp(ref, block) => {
          System.AllocStepUpdatesGraph(s, s', ref, block);
          assert BI.OpStep(
              BI.Variables(EphemeralGraph(s).value),
              BI.Variables(EphemeralGraph(s').value),
              ops[0]);
        }
      }
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(s.machine, s'.machine, ops);
      var smid := AsyncSectorDiskModelVariables(mid, s.disk);
      OpTransactionUpdate(s, smid, ops1);
      OpTransactionUpdate(smid, s', ops2);
      BI.JoinTransactions(
        BI.Variables(EphemeralGraph(s).value),
        BI.Variables(EphemeralGraph(smid).value),
        BI.Variables(EphemeralGraph(s').value),
        ops1, ops2);
    }
  }

  lemma TransactionUpdate(s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
  requires System.Inv(s)
  requires s.disk == s'.disk
  requires step.MachineStep?
  requires step.machineStep.TransactionStep?
  requires BC.Transaction(s.machine, s'.machine, D.NoDiskOp, vop, step.machineStep.ops)

  ensures System.Inv(s')
  ensures UpdateTransaction(s, s', step)
  {
    OpTransactionUpdate(s, s', step.machineStep.ops);
  }

  lemma RefinesReads(s: System.Variables, ops: seq<ReadOp>)
  requires System.Inv(s)
  requires BC.Reads(s.machine, ops)
  requires s.machine.Ready?
  ensures EphemeralGraph(s).Some?
  ensures BI.Reads(BI.Variables(EphemeralGraph(s).value), ops)
  {
    //reveal_EphemeralGraph();
    forall op | op in ops
    ensures BI.ReadStep(BI.Variables(EphemeralGraph(s).value), op)
    {
      System.EphemeralGraphRead(s, op);
      //assert s.machine.cache[op.ref] == op.node;
      //assert op.ref in EphemeralGraph(s);
      //assert EphemeralGraph(s)[op.ref] == op.node;
    }
  }

  lemma UnallocStepMeetsGCConditions(s: System.Variables, s': System.Variables,
      dop: DiskOp, vop: VOp, ref: Reference)
  requires System.Inv(s)
  requires s'.disk == s.disk
  requires BC.Unalloc(s.machine, s'.machine, dop, vop, ref)
  ensures EphemeralGraph(s).Some?
  ensures EphemeralGraph(s').Some?
  ensures BI.CanGCRefs(BI.Variables(EphemeralGraph(s).value), iset{ref})
  ensures System.Inv(s')
  ensures ref in EphemeralGraph(s).value
  ensures EphemeralGraph(s').value == IMapRemove1(EphemeralGraph(s).value, ref)
  {
    System.UnallocStepPreservesInv(s, s', dop, vop, ref);
    System.UnallocStepUpdatesGraph(s, s', dop, vop, ref);
    //reveal_EphemeralGraph();
    if (ref in BI.LiveReferences(BI.Variables(EphemeralGraph(s).value))) {
      assert BI.ReachableReference(BI.Variables(EphemeralGraph(s).value), ref);
      var lookup :| BI.LookupIsValid(BI.Variables(EphemeralGraph(s).value), lookup) && Last(lookup) == ref;
      assert |lookup| > 1;
      var pred := lookup[|lookup| - 2];
      assert ref in G.Successors(EphemeralGraph(s).value[pred]);
      assert false;
    }
  }

  // This is the uber lemma that explains how the graphs transform
  // for all the different step types

  lemma StepGraphs(s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
  requires System.Inv(s)
  requires System.NextStep(s, s', vop, step)
  ensures System.Inv(s')

  ensures vop.FreezeOp? ==>
      || UpdateFreeze(s, s')

  ensures vop.CrashOp? ==>
      UpdateCrash(s, s')

  ensures vop.SendPersistentLocOp? ==>
      UpdateObtainPersistentLoc(s, s', vop)

  ensures vop.SendFrozenLocOp? ==>
      UpdateProvideFrozenLoc(s, s', vop)

  ensures vop.CleanUpOp? ==>
      UpdateForgetOld(s, s')

  ensures vop.AdvanceOp? ==>
      || UpdateTransaction(s, s', step)
      || UpdateUnalloc(s, s', step)

  ensures vop.StatesInternalOp? ==> (
      || UpdateAllEq(s, s')
      || UpdateDiskChange(s, s')
    )

  ensures vop.JournalInternalOp? ==>
      UpdateAllEq(s, s')
  ensures vop.PushSyncOp? ==>
      UpdateAllEq(s, s')
  ensures vop.PopSyncOp? ==>
      UpdateAllEq(s, s')
  {
    System.NextStepPreservesInv(s, s', vop, step);

    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackNodeReqStep(ref) => {
            System.WriteBackNodeReqStepPreservesGraphs(s, s', dop, vop, ref);
          }
          case WriteBackNodeRespStep => {
            System.WriteBackNodeRespStepPreservesGraphs(s, s', dop, vop);
          }
          case WriteBackIndirectionTableReqStep => {
            System.WriteBackIndirectionTableReqStepPreservesGraphs(s, s', dop, vop);
          }
          case WriteBackIndirectionTableRespStep => {
            System.WriteBackIndirectionTableRespStepPreservesGraphs(s, s', dop, vop);
          }
          case UnallocStep(ref: Reference) => {
            System.UnallocStepUpdatesGraph(s, s', dop, vop, ref);
            assert UpdateUnalloc(s, s', step);
          }
          case PageInNodeReqStep(ref: Reference) => {
            System.PageInNodeReqStepPreservesGraphs(s, s', dop, vop, ref);
          }
          case PageInNodeRespStep => {
            System.PageInNodeRespStepPreservesGraphs(s, s', dop, vop);
          }
          case PageInIndirectionTableReqStep => {
            System.PageInIndirectionTableReqStepPreservesGraphs(s, s', dop, vop);
          }
          case PageInIndirectionTableRespStep => {
            System.PageInIndirectionTableRespStepPreservesGraphs(s, s', dop, vop);
          }
          case EvictStep(ref: Reference) => {
            System.EvictStepPreservesGraphs(s, s', dop, vop, ref);
          }
          case FreezeStep => {
            System.FreezeStepPreservesGraphs(s, s', dop, vop);
          }
          case CleanUpStep => {
            System.CleanUpStepPreservesGraphs(s, s', dop, vop);
          }
          case ReceiveLocStep => {
            System.ReceiveLocStepPreservesGraphs(s, s', dop, vop);
            assert UpdateObtainPersistentLoc(s, s', vop);
          }
          case NoOpStep => {
            System.NoOpStepPreservesGraphs(s, s', dop, vop);
          }
          case TransactionStep(ops) => TransactionUpdate(s, s', vop, step);
        }
      }
      case CrashStep => {
        System.CrashPreservesGraphs(s, s', vop);
        assert UpdateCrash(s, s');
      }
    }
  }
}
