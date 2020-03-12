include "../BlockCacheSystem/BlockCache.i.dfy"
include "../BlockCacheSystem/BlockCacheSystem.i.dfy"
include "../MapSpec/ThreeStateVersioned.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
//
// A BlockCacheSystem -- a crash-safe block cache running a client program and
// attached to our disk model -- correctly provides three-state crash safety
// for the state of its program.
//
// Ideally we would prove the refinement for an arbitrary graph, but if we
// imported the abstract BlockCacheSystem and CrashSafeBlockInterface
// separately then we wouldn't know they were using the same graph.  So for
// now, we just prove the refinement specifically for BetreeGraph.
//

module BlockCacheSystem_Refines_TSJBlockInterface {
  // Okay, this isn't *technically* a refinement: there's no
  // such thing as a TSJBlockInterface.
  // (You can only create a TSJX for an X which is defined
  // with respect to UIOps. BlockInterface is not such an X.)
  // Still, this module contains most of the meat that would
  // be used to define such a refinement if it existed.
  // Really, these lemmas are here to facilitate the proof
  // that BetreeBlockCacheSystem refines TSJPivotBetree.

  import opened G = PivotBetreeGraph
  import BCS = BlockCacheSystem
  import opened AsyncSectorDiskModelTypes

  import opened Maps
  import opened Sequences
  import opened Options
  import opened NativeTypes

  import BC = BlockCache
  import BI = PivotBetreeBlockInterface
  import D = AsyncSectorDisk
  import ThreeState = ThreeStateTypes
  type DiskOp = BC.DiskOp

  function Ik(k: BCS.Constants) : BI.Constants
  {
    BI.Constants()
  }

  function PersistentGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(BCS.PersistentGraph(k, s))
  }

  function EphemeralGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(BCS.EphemeralGraph(k, s))
  }

  function FrozenGraph(k: BCS.Constants, s: BCS.Variables) : imap<Reference, Node>
  requires BCS.Inv(k, s)
  {
    MapToImap(BCS.FrozenGraph(k, s))
  }

  predicate CommitOccurredNotAcked(s: BCS.Variables)
  {
    s.machine.Ready? && s.machine.superblockWrite.Some?
            && s.machine.superblockWrite.value in s.disk.respWrites
  }
  
  function SyncReqState(k: BCS.Constants, s: BCS.Variables, status: BC.SyncReqStatus) : ThreeState.SyncReqStatus
  {
    match status {
      case State1 => ThreeState.State1
      case State2 => (
        // It's possible that the disk has written the superblock but the BlockCache
        // hasn't heard about it yet. In that case, we need to upgrade State2 to State1.
        if CommitOccurredNotAcked(s) then
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

  predicate IsFreezeStep(k: BCS.Constants, s: BCS.Variables, step: BCS.Step)
  {
    && step.MachineStep?
    && (
      || step.machineStep.FreezeStep?
      || (
        && step.machineStep.WriteBackJournalReqStep?
        && s.machine.Ready?
        && s.machine.inMemoryJournalFrozen == []
      )
      || (
        && step.machineStep.WriteBackJournalReqWraparoundStep?
        && s.machine.Ready?
        && s.machine.inMemoryJournalFrozen == []
      )
    )
  }

  predicate IsCrashStep(k: BCS.Constants, s: BCS.Variables, step: BCS.Step)
  {
    && step.CrashStep?
  }

  predicate IsPersistStep(k: BCS.Constants, s: BCS.Variables, step: BCS.Step)
  {
    && step.DiskInternalStep?
    && step.step.ProcessWriteStep?
    && BCS.ProcessWriteIsGraphUpdate(k, s, step.step.id)
  }

  predicate IsAdvanceLogStep(k: BCS.Constants, s: BCS.Variables, step: BCS.Step)
  {
    && step.DiskInternalStep?
    && step.step.ProcessWriteStep?
    && BCS.ProcessWriteIsSuperblockUpdate(k, s, step.step.id)
    && !BCS.ProcessWriteIsGraphUpdate(k, s, step.step.id)
  }

  predicate IsTransactionStep(step: BCS.Step)
  {
    && step.MachineStep?
    && step.machineStep.TransactionStep?
  }

  predicate UpdateAllEq(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')
    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
    && BCS.GammaJournal(s') == BCS.GammaJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s)
  }

  predicate UpdateCrash(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')
    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == PersistentGraph(k, s)
    && EphemeralGraph(k, s') == PersistentGraph(k, s)
    && BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
    && BCS.FrozenJournal(s') == BCS.PersistentJournal(s)
    && BCS.EphemeralJournal(s') == BCS.PersistentJournal(s)
    && BCS.GammaJournal(s') == BCS.PersistentJournal(s)
    && BCS.DeltaJournal(s') == []
  }

  predicate UpdateMove1to2(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')
    && PersistentGraph(k, s') == FrozenGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && BCS.PersistentJournal(s') == BCS.FrozenJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
    && BCS.GammaJournal(s') == BCS.FrozenJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s)
  }

  predicate UpdateMove2to3(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')
    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == EphemeralGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
    && BCS.FrozenJournal(s') == []
    && BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
    && BCS.GammaJournal(s') == BCS.GammaJournal(s) + BCS.DeltaJournal(s)
    && BCS.DeltaJournal(s') == []
  }

  predicate UpdateExtendLog(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')
    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == EphemeralGraph(k, s)
    && BCS.PersistentJournal(s') == BCS.GammaJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
    && BCS.GammaJournal(s') == BCS.GammaJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s)
  }

  predicate UpdateUnalloc(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables,
    step: BCS.Step)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')

    && step.MachineStep?
    && step.machineStep.UnallocStep?

    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && EphemeralGraph(k, s') == IMapRemove1(EphemeralGraph(k, s), step.machineStep.ref)
    && BCS.PersistentJournal(s') == BCS.GammaJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
    && BCS.GammaJournal(s') == BCS.GammaJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s)
  }

  predicate UpdateTransaction(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables,
    step: BCS.Step)
  requires IsTransactionStep(step)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')

    && step.MachineStep?
    && step.machineStep.TransactionStep?
    && step.machineStep.journalStep.JSNew?

    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s)),
            BI.Variables(EphemeralGraph(k, s')),
            step.machineStep.ops)
    && BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.EphemeralJournal(s) == []
    && BCS.EphemeralJournal(s') == []
    && BCS.GammaJournal(s') == BCS.GammaJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s) + step.machineStep.journalStep.entries
  }

  predicate ReplayTransaction(
    k: BCS.Constants,
    s: BCS.Variables,
    s': BCS.Variables,
    step: BCS.Step)
  requires IsTransactionStep(step)
  {
    && BCS.Inv(k, s)
    && BCS.Inv(k, s')

    && step.MachineStep?
    && step.machineStep.TransactionStep?
    && step.machineStep.journalStep.JSReplay?

    && PersistentGraph(k, s') == PersistentGraph(k, s)
    && FrozenGraph(k, s') == FrozenGraph(k, s)
    && BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s)),
            BI.Variables(EphemeralGraph(k, s')),
            step.machineStep.ops)
    && BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
    && BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
    && BCS.GammaJournal(s') == BCS.GammaJournal(s)
    && BCS.DeltaJournal(s') == BCS.DeltaJournal(s)
    && step.machineStep.journalStep.entries + BCS.EphemeralJournal(s')
        == BCS.EphemeralJournal(s)
  }


  lemma OpTransactionUpdate(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, ops: seq<Op>)
  requires BCS.Inv(k, s)
  requires s.disk == s'.disk
  requires BC.OpTransaction(k.machine, s.machine, s'.machine, ops)
  ensures BCS.Inv(k, s')
  ensures PersistentGraph(k, s') == PersistentGraph(k, s)
  ensures FrozenGraph(k, s') == FrozenGraph(k, s)
  ensures BI.OpTransaction(BI.Constants(),
            BI.Variables(EphemeralGraph(k, s)),
            BI.Variables(EphemeralGraph(k, s')),
            ops)
  ensures BCS.PersistentJournal(s') == BCS.PersistentJournal(s)
  ensures BCS.FrozenJournal(s') == BCS.FrozenJournal(s)
  ensures BCS.EphemeralJournal(s') == BCS.EphemeralJournal(s)
  ensures BCS.GammaJournal(s') == BCS.GammaJournal(s)
  ensures BCS.DeltaJournal(s') == BCS.DeltaJournal(s)

  ensures SyncReqs(k, s) == SyncReqs(k, s');
  decreases |ops|
  {
    //reveal_PersistentGraph();
    //reveal_FrozenGraph();
    //reveal_EphemeralGraph();
    if |ops| == 0 {
    } else if |ops| == 1 {
      BCS.OpPreservesInv(k, s, s', ops[0]);
      reveal_SyncReqs();
      match ops[0] {
        case WriteOp(ref, block) => {
          BCS.DirtyStepUpdatesGraph(k, s, s', ref, block);
          BCS.DirtyStepPreservesJournals(k, s, s', ref, block);
          assert s.machine.syncReqs == s'.machine.syncReqs;
          assert BI.Write(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s)),
              BI.Variables(EphemeralGraph(k, s')),
              ref, block);
          assert BI.OpStep(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s)),
              BI.Variables(EphemeralGraph(k, s')),
              ops[0]);
        }
        case AllocOp(ref, block) => {
          BCS.AllocStepUpdatesGraph(k, s, s', ref, block);
          BCS.AllocStepPreservesJournals(k, s, s', ref, block);
          assert s.machine.syncReqs == s'.machine.syncReqs;
          assert BI.OpStep(BI.Constants(),
              BI.Variables(EphemeralGraph(k, s)),
              BI.Variables(EphemeralGraph(k, s')),
              ops[0]);
        }
      }
    } else {
      var ops1, mid, ops2 := BC.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      var smid := AsyncSectorDiskModelVariables(mid, s.disk);
      OpTransactionUpdate(k, s, smid, ops1);
      OpTransactionUpdate(k, smid, s', ops2);
      BI.JoinTransactions(BI.Constants(),
        BI.Variables(EphemeralGraph(k, s)),
        BI.Variables(EphemeralGraph(k, smid)),
        BI.Variables(EphemeralGraph(k, s')),
        ops1, ops2);
    }
  }

  lemma TransactionUpdate(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires s.disk == s'.disk
  requires step.MachineStep?
  requires step.machineStep.TransactionStep?
  requires BC.Transaction(k.machine, s.machine, s'.machine, D.NoDiskOp, step.machineStep.ops, step.machineStep.journalStep)

  ensures BCS.Inv(k, s')
  ensures step.machineStep.journalStep.JSNew? ==>
      UpdateTransaction(k, s, s', step)
  ensures step.machineStep.journalStep.JSReplay? ==>
      ReplayTransaction(k, s, s', step)

  ensures SyncReqs(k, s) == SyncReqs(k, s');
  {
    var s1 := s.(machine := BC.DoJournalStep(s.machine, step.machineStep.journalStep));
    BCS.JournalStepPreservesGraphs(k, s, s1, step.machineStep.journalStep);
    BCS.JournalStepPreservesJournals(k, s, s1, step.machineStep.journalStep);
    OpTransactionUpdate(k, s1, s', step.machineStep.ops);

    assert SyncReqs(k, s) == SyncReqs(k, s1) by { reveal_SyncReqs(); }
  }

  lemma RefinesReads(k: BCS.Constants, s: BCS.Variables, ops: seq<ReadOp>)
  requires BCS.Inv(k, s)
  requires BC.Reads(k.machine, s.machine, ops)
  ensures BI.Reads(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), ops)
  {
    //reveal_EphemeralGraph();
    forall op | op in ops
    ensures BI.ReadStep(BI.Constants, BI.Variables(EphemeralGraph(k, s)), op)
    {
      BCS.EphemeralGraphRead(k, s, op);
      //assert s.machine.cache[op.ref] == op.node;
      //assert op.ref in EphemeralGraph(k, s);
      //assert EphemeralGraph(k, s)[op.ref] == op.node;
    }
  }

  lemma UnallocStepMeetsGCConditions(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables,
      dop: DiskOp, ref: Reference)
  requires BCS.Inv(k, s)
  requires s'.disk == s.disk
  requires BC.Unalloc(k.machine, s.machine, s'.machine, dop, ref)
  ensures BI.CanGCRefs(BI.Constants(), BI.Variables(EphemeralGraph(k, s)), iset{ref})
  {
    BCS.UnallocStepUpdatesGraph(k, s, s', dop, ref);
    //reveal_EphemeralGraph();
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

  ensures IsFreezeStep(k, s, step) ==>
      || UpdateMove2to3(k, s, s')
      || UpdateExtendLog(k, s, s')

  ensures IsCrashStep(k, s, step) ==>
      UpdateCrash(k, s, s')

  ensures IsPersistStep(k, s, step) ==>
      UpdateMove1to2(k, s, s')

  ensures IsAdvanceLogStep(k, s, step) ==>
      UpdateExtendLog(k, s, s')

  ensures IsTransactionStep(step) ==> (
    && (step.machineStep.journalStep.JSNew? ==>
        UpdateTransaction(k, s, s', step))
    && (step.machineStep.journalStep.JSReplay? ==>
        ReplayTransaction(k, s, s', step))
  )

  ensures (
      && !IsTransactionStep(step)
      && !IsFreezeStep(k, s, step)
      && !IsPersistStep(k, s, step)
      && !IsAdvanceLogStep(k, s, step)
      && !IsCrashStep(k, s, step)
    ) ==> (
      || UpdateAllEq(k, s, s')
      || UpdateUnalloc(k, s, s', step)
    )
  {
    BCS.NextStepPreservesInv(k, s, s', step);

    //reveal_PersistentGraph();
    //reveal_FrozenGraph();
    //reveal_EphemeralGraph();

    match step {
      case MachineStep(dop, machineStep) => {
        match machineStep {
          case WriteBackReqStep(ref) => {
            BCS.WriteBackReqStepPreservesGraphs(k, s, s', dop, ref);
            BCS.WriteBackReqStepPreservesJournals(k, s, s', dop, ref);
          }
          case WriteBackRespStep => {
            BCS.WriteBackRespStepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackRespStepPreservesJournals(k, s, s', dop);
          }
          case WriteBackIndirectionTableReqStep => {
            BCS.WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackIndirectionTableReqStepPreservesJournals(k, s, s', dop);
          }
          case WriteBackIndirectionTableRespStep => {
            BCS.WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackIndirectionTableRespStepPreservesJournals(k, s, s', dop);
          }
          case WriteBackJournalReqStep(jr) => {
            BCS.WriteBackJournalReqStepPreservesGraphs(k, s, s', dop, jr);
            BCS.WriteBackJournalReqStepPreservesJournals(k, s, s', dop, jr);
            if IsFreezeStep(k, s, step) {
              assert UpdateExtendLog(k, s, s');
            } else {
              assert UpdateAllEq(k, s, s');
            }
          }
          case WriteBackJournalReqWraparoundStep(jr) => {
            BCS.WriteBackJournalReqWraparoundStepPreservesGraphs(k, s, s', dop, jr);
            BCS.WriteBackJournalReqWraparoundStepPreservesJournals(k, s, s', dop, jr);
          }
          case WriteBackJournalRespStep => {
            BCS.WriteBackJournalRespStepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackJournalRespStepPreservesJournals(k, s, s', dop);
          }
          case WriteBackSuperblockReq_Basic_Step => {
            BCS.WriteBackSuperblockReq_Basic_StepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackSuperblockReq_Basic_StepPreservesJournals(k, s, s', dop);
          }
          case WriteBackSuperblockReq_UpdateIndirectionTable_Step => {
            BCS.WriteBackSuperblockReq_UpdateIndirectionTable_StepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackSuperblockReq_UpdateIndirectionTable_StepPreservesJournals(k, s, s', dop);
          }
          case WriteBackSuperblockRespStep => {
            BCS.WriteBackSuperblockRespStepPreservesGraphs(k, s, s', dop);
            BCS.WriteBackSuperblockRespStepPreservesJournals(k, s, s', dop);
          }
          case UnallocStep(ref: Reference) => {
            BCS.UnallocStepUpdatesGraph(k, s, s', dop, ref);
            BCS.UnallocStepPreservesJournals(k, s, s', dop, ref);
          }
          case PageInReqStep(ref: Reference) => {
            BCS.PageInReqStepPreservesGraphs(k, s, s', dop, ref);
            BCS.PageInReqStepPreservesJournals(k, s, s', dop, ref);
          }
          case PageInRespStep => {
            BCS.PageInRespStepPreservesGraphs(k, s, s', dop);
            BCS.PageInRespStepPreservesJournals(k, s, s', dop);
          }
          case PageInIndirectionTableReqStep => {
            BCS.PageInIndirectionTableReqStepPreservesGraphs(k, s, s', dop);
            BCS.PageInIndirectionTableReqStepPreservesJournals(k, s, s', dop);
          }
          case PageInIndirectionTableRespStep => {
            BCS.PageInIndirectionTableRespStepPreservesGraphs(k, s, s', dop);
            BCS.PageInIndirectionTableRespStepPreservesJournals(k, s, s', dop);
          }
          case PageInJournalReqStep(which) => {
            BCS.PageInJournalReqStepPreservesGraphs(k, s, s', dop, which);
            BCS.PageInJournalReqStepPreservesJournals(k, s, s', dop, which);
          }
          case PageInJournalRespStep(which) => {
            BCS.PageInJournalRespStepPreservesGraphs(k, s, s', dop, which);
            BCS.PageInJournalRespStepPreservesJournals(k, s, s', dop, which);
          }
          case PageInSuperblockReqStep(which) => {
            BCS.PageInSuperblockReqStepPreservesGraphs(k, s, s', dop, which);
            BCS.PageInSuperblockReqStepPreservesJournals(k, s, s', dop, which);
          }
          case PageInSuperblockRespStep(which) => {
            BCS.PageInSuperblockRespStepPreservesGraphs(k, s, s', dop, which);
            BCS.PageInSuperblockRespStepPreservesJournals(k, s, s', dop, which);
          }
          case FinishLoadingSuperblockPhaseStep => {
            BCS.FinishLoadingSuperblockPhaseStepPreservesGraphs(k, s, s', dop);
            BCS.FinishLoadingSuperblockPhaseStepPreservesJournals(k, s, s', dop);
          }
          case FinishLoadingOtherPhaseStep => {
            BCS.FinishLoadingOtherPhaseStepPreservesGraphs(k, s, s', dop);
            BCS.FinishLoadingOtherPhaseStepPreservesJournals(k, s, s', dop);
          }
          case EvictStep(ref: Reference) => {
            BCS.EvictStepPreservesGraphs(k, s, s', dop, ref);
            BCS.EvictStepPreservesJournals(k, s, s', dop, ref);
          }
          case FreezeStep => {
            BCS.FreezeStepPreservesGraphs(k, s, s', dop);
            BCS.FreezeStepPreservesJournals(k, s, s', dop);
            assert UpdateMove2to3(k, s, s');
          }
          case PushSyncReqStep(id) => {
            BCS.PushSyncReqStepPreservesGraphs(k, s, s', dop, id);
            BCS.PushSyncReqStepPreservesJournals(k, s, s', dop, id);
          }
          case PopSyncReqStep(id) => {
            BCS.PopSyncReqStepPreservesGraphs(k, s, s', dop, id);
            BCS.PopSyncReqStepPreservesJournals(k, s, s', dop, id);
          }
          case NoOpStep => {
            BCS.NoOpStepPreservesGraphs(k, s, s', dop);
            BCS.NoOpStepPreservesJournals(k, s, s', dop);
          }
          case TransactionStep(ops, js) => TransactionUpdate(k, s, s', step);
        }
      }
      case DiskInternalStep(disk_step) => {
        match disk_step {
          case ProcessReadStep(id) => {
            BCS.ProcessReadPreservesGraphs(k, s, s', id);
            BCS.ProcessReadPreservesJournals(k, s, s', id);
          }
          case ProcessReadFailureStep(id) => {
            BCS.ProcessReadFailurePreservesGraphs(k, s, s', id);
            BCS.ProcessReadFailurePreservesJournals(k, s, s', id);
          }
          case ProcessWriteStep(id) => {
            BCS.ProcessWritePreservesGraphs(k, s, s', id);
            BCS.ProcessWritePreservesJournals(k, s, s', id);
          }
        }
      }
      case CrashStep => {
        BCS.CrashPreservesGraphs(k, s, s');
        BCS.CrashPreservesJournals(k, s, s');
        assert UpdateCrash(k, s, s');
      }
    }
  }

  lemma StepSyncReqs(k: BCS.Constants, s: BCS.Variables, s': BCS.Variables, step: BCS.Step)
  requires BCS.Inv(k, s)
  requires BCS.NextStep(k, s, s', step)
  ensures BCS.Inv(k, s')

  ensures IsPersistStep(k, s, step) ==> SyncReqs(k, s') == ThreeState.SyncReqs2to1(SyncReqs(k, s))
  ensures IsFreezeStep(k, s, step) ==> SyncReqs(k, s') == ThreeState.SyncReqs3to2(SyncReqs(k, s))
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
    && !IsFreezeStep(k, s, step)
    && !step.CrashStep?
    && !(step.MachineStep? && step.machineStep.PushSyncReqStep?)
    && !(step.MachineStep? && step.machineStep.PopSyncReqStep?)
    ==> SyncReqs(k, s') == SyncReqs(k, s)
  {
    reveal_SyncReqs();
    BCS.NextStepPreservesInv(k, s, s', step);

    if (
      && !IsPersistStep(k, s, step)
      && !IsFreezeStep(k, s, step)
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
            case TransactionStep(ops, js) => {
              TransactionUpdate(k, s, s', step);
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
