include "../BlockCacheSystem/BlockSystem.i.dfy"
include "../Versions/StatesView.i.dfy"
include "../lib/Base/Maps.s.dfy"
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

  function Ik(k: System.Constants) : BI.Constants
  {
    BI.Constants()
  }

  predicate IsTransactionStep(step: System.Step)
  {
    && step.MachineStep?
    && step.machineStep.TransactionStep?
  }

  function DiskGraphMap(k: System.Constants, s: System.Variables)
    : imap<Location, imap<Reference, Node>>
  {
    System.DiskGraphMap(k, s)
  }

  function FrozenGraph(k: System.Constants, s: System.Variables) : Option<imap<Reference, Node>>
  {
    System.FrozenGraphOpt(k, s)
  }

  function EphemeralGraph(k: System.Constants, s: System.Variables) : Option<imap<Reference, Node>>
  {
    System.EphemeralGraphOpt(k, s)
  }

  function PersistentLoc(k: System.Constants, s: System.Variables) : Option<Location>
  {
    System.PersistentLoc(k, s)
  }

  function FrozenLoc(k: System.Constants, s: System.Variables) : Option<Location>
  {
    System.FrozenLoc(k, s)
  }

  predicate UpdateAllEq(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(k, s)
    && System.Inv(k, s')
    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
    && FrozenLoc(k, s') == FrozenLoc(k, s)
  }

  predicate UpdateCrash(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(k, s)
    && System.Inv(k, s')
    && System.DiskChangesPreservesPersistentAndFrozen(k, s, s')
    && FrozenGraph(k, s') == None
    && EphemeralGraph(k, s') == None
    && PersistentLoc(k, s') == None
    && FrozenLoc(k, s') == None
  }

  predicate UpdateObtainPersistentLoc(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables,
    vop: VOp)
  {
    && vop.SendPersistentLocOp?
    && System.Inv(k, s)
    && System.Inv(k, s')
    && PersistentLoc(k, s) == None
    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && vop.loc in DiskGraphMap(k, s)
    && EphemeralGraph(k, s') == Some(DiskGraphMap(k, s)[vop.loc])
    && PersistentLoc(k, s') == Some(vop.loc)
    && FrozenLoc(k, s') == FrozenLoc(k, s)
  }

  predicate UpdateFreeze(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(k, s)
    && System.Inv(k, s')
    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && FrozenGraph(k, s') == EphemeralGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
    && FrozenLoc(k, s') == None
  }

  predicate UpdateDiskChange(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables)
  {
    && System.Inv(k, s)
    && System.Inv(k, s')
    && System.DiskChangesPreservesPersistentAndFrozen(k, s, s')
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
    && FrozenLoc(k, s') == FrozenLoc(k, s)
  }

  predicate UpdateProvideFrozenLoc(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables,
    vop: VOp)
  {
    && vop.SendFrozenLocOp?
    && FrozenLoc(k, s) == None
    && FrozenLoc(k, s') == Some(vop.loc)
    && FrozenGraph(k, s).Some?
    && FrozenLoc(k, s').value in DiskGraphMap(k, s)
    && DiskGraphMap(k, s)[FrozenLoc(k, s').value] == FrozenGraph(k, s).value
    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
  }

  predicate UpdateForgetOld(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables)
  {
    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && FrozenGraph(k, s') == None
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && FrozenLoc(k, s') == None
    && PersistentLoc(k, s') == FrozenLoc(k, s)
  }

  predicate UpdateUnalloc(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables,
    step: System.Step)
  {
    && System.Inv(k, s)
    && System.Inv(k, s')

    && step.MachineStep?
    && step.machineStep.UnallocStep?

    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
    && FrozenLoc(k, s') == FrozenLoc(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)

    && EphemeralGraph(k, s).Some?
    && EphemeralGraph(k, s').Some?

    && EphemeralGraph(k, s').value == IMapRemove1(EphemeralGraph(k, s).value, step.machineStep.ref)
  }

  predicate UpdateTransaction(
    k: System.Constants,
    s: System.Variables,
    s': System.Variables,
    step: System.Step)
  {
    && IsTransactionStep(step)
    && System.Inv(k, s)
    && System.Inv(k, s')

    && step.MachineStep?
    && step.machineStep.TransactionStep?

    && DiskGraphMap(k, s') == DiskGraphMap(k, s)
    && PersistentLoc(k, s') == PersistentLoc(k, s)
    && FrozenLoc(k, s') == FrozenLoc(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)

    && EphemeralGraph(k, s).Some?
    && EphemeralGraph(k, s').Some?

    && BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s).value),
            BI.Variables(EphemeralGraph(k, s').value),
            step.machineStep.ops)
  }

  lemma OpTransactionUpdate(k: System.Constants, s: System.Variables, s': System.Variables, ops: seq<Op>)
  requires System.Inv(k, s)
  requires s.disk == s'.disk
  requires BC.OpTransaction(k.machine, s.machine, s'.machine, ops)
  requires s.machine.Ready?
  ensures System.Inv(k, s')
  ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
  ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  ensures FrozenLoc(k, s') == FrozenLoc(k, s)
  ensures FrozenGraph(k, s') == FrozenGraph(k, s)
  ensures s'.machine.Ready?
  ensures EphemeralGraph(k, s).Some?
  ensures EphemeralGraph(k, s').Some?
  ensures BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s).value),
            BI.Variables(EphemeralGraph(k, s').value),
            ops)

  decreases |ops|
  {
    //reveal_PersistentGraph();
    //reveal_FrozenGraph();
    //reveal_EphemeralGraph();
    if |ops| == 0 {
    } else if |ops| == 1 {
      System.OpPreservesInv(k, s, s', ops[0]);
      match ops[0] {
        case WriteOp(ref, block) => {
          System.DirtyStepUpdatesGraph(k, s, s', ref, block);
          assert BI.Write(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s).value),
              BI.Variables(EphemeralGraph(k, s').value),
              ref, block);
          assert BI.OpStep(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s).value),
              BI.Variables(EphemeralGraph(k, s').value),
              ops[0]);
        }
        case AllocOp(ref, block) => {
          System.AllocStepUpdatesGraph(k, s, s', ref, block);
          assert BI.OpStep(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s).value),
              BI.Variables(EphemeralGraph(k, s').value),
              ops[0]);
        }
      }
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := AsyncSectorDiskModelVariables(mid, s.disk);
      OpTransactionUpdate(k, s, smid, ops1);
      OpTransactionUpdate(k, smid, s', ops2);
      BI.JoinTransactions(BI.Constants(),
        BI.Variables(EphemeralGraph(k, s).value),
        BI.Variables(EphemeralGraph(k, smid).value),
        BI.Variables(EphemeralGraph(k, s').value),
        ops1, ops2);
    }
  }

  lemma TransactionUpdate(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
  requires System.Inv(k, s)
  requires s.disk == s'.disk
  requires step.MachineStep?
  requires step.machineStep.TransactionStep?
  requires BC.Transaction(k.machine, s.machine, s'.machine, D.NoDiskOp, vop, step.machineStep.ops)

  ensures System.Inv(k, s')
  ensures UpdateTransaction(k, s, s', step)
  {
    OpTransactionUpdate(k, s, s', step.machineStep.ops);
  }

  lemma RefinesReads(k: System.Constants, s: System.Variables, ops: seq<ReadOp>)
  requires System.Inv(k, s)
  requires BC.Reads(k.machine, s.machine, ops)
  requires s.machine.Ready?
  ensures EphemeralGraph(k, s).Some?
  ensures BI.Reads(BI.Constants(), BI.Variables(EphemeralGraph(k, s).value), ops)
  {
    //reveal_EphemeralGraph();
    forall op | op in ops
    ensures BI.ReadStep(BI.Constants, BI.Variables(EphemeralGraph(k, s).value), op)
    {
      System.EphemeralGraphRead(k, s, op);
      //assert s.machine.cache[op.ref] == op.node;
      //assert op.ref in EphemeralGraph(k, s);
      //assert EphemeralGraph(k, s)[op.ref] == op.node;
    }
  }

  lemma UnallocStepMeetsGCConditions(k: System.Constants, s: System.Variables, s': System.Variables,
      dop: DiskOp, vop: VOp, ref: Reference)
  requires System.Inv(k, s)
  requires s'.disk == s.disk
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, vop, ref)
  ensures EphemeralGraph(k, s).Some?
  ensures EphemeralGraph(k, s').Some?
  ensures BI.CanGCRefs(BI.Constants(), BI.Variables(EphemeralGraph(k, s).value), iset{ref})
  ensures System.Inv(k, s')
  ensures ref in EphemeralGraph(k, s).value
  ensures EphemeralGraph(k, s').value == IMapRemove1(EphemeralGraph(k, s).value, ref)
  {
    System.UnallocStepPreservesInv(k, s, s', dop, vop, ref);
    System.UnallocStepUpdatesGraph(k, s, s', dop, vop, ref);
    //reveal_EphemeralGraph();
    if (ref in BI.LiveReferences(BI.Constants(), BI.Variables(EphemeralGraph(k, s).value))) {
      assert BI.ReachableReference(BI.Constants(), BI.Variables(EphemeralGraph(k, s).value), ref);
      var lookup :| BI.LookupIsValid(BI.Constants(), BI.Variables(EphemeralGraph(k, s).value), lookup) && Last(lookup) == ref;
      assert |lookup| > 1;
      var pred := lookup[|lookup| - 2];
      assert ref in G.Successors(EphemeralGraph(k, s).value[pred]);
      assert false;
    }
  }

  // This is the uber lemma that explains how the graphs transform
  // for all the different step types

  lemma StepGraphs(k: System.Constants, s: System.Variables, s': System.Variables, vop: VOp, step: System.Step)
  requires System.Inv(k, s)
  requires System.NextStep(k, s, s', vop, step)
  ensures System.Inv(k, s')

  ensures vop.FreezeOp? ==>
      || UpdateFreeze(k, s, s')

  ensures vop.CrashOp? ==>
      UpdateCrash(k, s, s')

  ensures vop.SendPersistentLocOp? ==>
      UpdateObtainPersistentLoc(k, s, s', vop)

  ensures vop.SendFrozenLocOp? ==>
      UpdateProvideFrozenLoc(k, s, s', vop)

  ensures vop.CleanUpOp? ==>
      UpdateForgetOld(k, s, s')

  ensures vop.AdvanceOp? ==>
      || UpdateTransaction(k, s, s', step)
      || UpdateUnalloc(k, s, s', step)

  ensures vop.StatesInternalOp? ==> (
      || UpdateAllEq(k, s, s')
      || UpdateDiskChange(k, s, s')
    )

  ensures vop.JournalInternalOp? ==>
      UpdateAllEq(k, s, s')
  ensures vop.PushSyncOp? ==>
      UpdateAllEq(k, s, s')
  ensures vop.PopSyncOp? ==>
      UpdateAllEq(k, s, s')
  {
    System.NextStepPreservesInv(k, s, s', vop, step);

    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackNodeReqStep(ref) => {
            System.WriteBackNodeReqStepPreservesGraphs(k, s, s', dop, vop, ref);
          }
          case WriteBackNodeRespStep => {
            System.WriteBackNodeRespStepPreservesGraphs(k, s, s', dop, vop);
          }
          case WriteBackIndirectionTableReqStep => {
            System.WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop, vop);
          }
          case WriteBackIndirectionTableRespStep => {
            System.WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop, vop);
          }
          case UnallocStep(ref: Reference) => {
            System.UnallocStepUpdatesGraph(k, s, s', dop, vop, ref);
            assert UpdateUnalloc(k, s, s', step);
          }
          case PageInNodeReqStep(ref: Reference) => {
            System.PageInNodeReqStepPreservesGraphs(k, s, s', dop, vop, ref);
          }
          case PageInNodeRespStep => {
            System.PageInNodeRespStepPreservesGraphs(k, s, s', dop, vop);
          }
          case PageInIndirectionTableReqStep => {
            System.PageInIndirectionTableReqStepPreservesGraphs(k, s, s', dop, vop);
          }
          case PageInIndirectionTableRespStep => {
            System.PageInIndirectionTableRespStepPreservesGraphs(k, s, s', dop, vop);
          }
          case EvictStep(ref: Reference) => {
            System.EvictStepPreservesGraphs(k, s, s', dop, vop, ref);
          }
          case FreezeStep => {
            System.FreezeStepPreservesGraphs(k, s, s', dop, vop);
          }
          case CleanUpStep => {
            System.CleanUpStepPreservesGraphs(k, s, s', dop, vop);
          }
          case ReceiveLocStep => {
            System.ReceiveLocStepPreservesGraphs(k, s, s', dop, vop);
            assert UpdateObtainPersistentLoc(k, s, s', vop);
          }
          case NoOpStep => {
            System.NoOpStepPreservesGraphs(k, s, s', dop, vop);
          }
          case TransactionStep(ops) => TransactionUpdate(k, s, s', vop, step);
        }
      }
      case CrashStep => {
        System.CrashPreservesGraphs(k, s, s', vop);
        assert UpdateCrash(k, s, s');
      }
    }
  }
}
