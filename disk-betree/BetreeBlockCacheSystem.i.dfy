include "AsyncSectorDiskModel.i.dfy"
include "PivotBetree_Refines_Betree.i.dfy"
include "BlockCache.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "BlockCacheSystem.i.dfy"
include "BetreeBlockCache.i.dfy"
include "BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface.i.dfy"
//
// Instantiate the {PivotBetree, BlockCache} code in a System (model of the environment).
// ("Bottom lettuce")
//

// TODO(jonh): Rename PivotBetreeBlockCacheSystem. [approved by thance]

module BetreeBlockCacheSystem refines AsyncSectorDiskModel {
  import opened Maps
  import opened Sequences

  import opened PivotBetreeSpec`Spec
  import BC = BetreeGraphBlockCache
  import BCS = BetreeGraphBlockCacheSystem
  import BT = PivotBetree
  import BTI = PivotBetreeInvAndRefinement
  import BI = PivotBetreeBlockInterface
  import Ref = BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface

  import M = BetreeBlockCache

  function Ik(k: Constants) : BT.Constants
  {
    BT.Constants(BI.Constants())
  }

  function PersistentBetree(k: Constants, s: Variables) : BT.Variables
  requires BCS.Inv(k, s)
  {
    BT.Variables(BI.Variables(Ref.PersistentGraph(k, s)))
  }

  function FrozenBetree(k: Constants, s: Variables) : BT.Variables
  requires BCS.Inv(k, s)
  {
    BT.Variables(BI.Variables(Ref.FrozenGraph(k, s)))
  }

  function EphemeralBetree(k: Constants, s: Variables) : BT.Variables
  requires BCS.Inv(k, s)
  {
    BT.Variables(BI.Variables(Ref.EphemeralGraph(k, s)))
  }

  predicate Init(k: Constants, s: Variables)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
    && BCS.Init(k, s)
    && BT.Init(Ik(k), PersistentBetree(k, s))
  }

  predicate Inv(k: Constants, s: Variables) {
    && BCS.Inv(k, s)
    && BTI.Inv(Ik(k), PersistentBetree(k, s))
    && BTI.Inv(Ik(k), FrozenBetree(k, s))
    && BTI.Inv(Ik(k), EphemeralBetree(k, s))
  }

  // Proofs

  lemma InitImpliesInv(k: Constants, s: Variables)
    // pre and post conditions are inherited
    //requires Init(k, s)
    //ensures Inv(k, s)
  {
    BCS.InitImpliesInv(k, s);
    BTI.InitImpliesInv(Ik(k), PersistentBetree(k, s));
    Ref.InitImpliesGraphsEq(k, s);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: M.DiskOp, betreeStep: BetreeStep)
    requires Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, uiop, dop, betreeStep)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', BCS.MachineStep(dop, BC.TransactionStep(BetreeStepOps(betreeStep))));
    Ref.RefinesReads(k, s, BetreeStepReads(betreeStep));
    //assert BT.Betree(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, betreeStep);
    assert BT.NextStep(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, BT.BetreeStep(betreeStep));
    BTI.NextPreservesInv(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop);
  }

  lemma BlockCacheMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: M.DiskOp, step: BC.Step)
    requires Inv(k, s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, uiop, dop, step)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(Ik(k).bck, EphemeralBetree(k, s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(k, s, s', dop, step.ref);
      assert step.ref in EphemeralBetree(k, s).bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(Ik(k).bck, EphemeralBetree(k, s).bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(k, s).bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(k, s).bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(k, s).bcv.view, iset{step.ref});
      assert BT.GC(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, iset{step.ref});
      BTI.GCStepRefines(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, iset{step.ref});
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Crash(k, s, s', uiop)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', BCS.CrashStep);
  }

  lemma DiskInternalStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
    requires Inv(k, s)
    requires DiskInternal(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', BCS.DiskInternalStep(step));
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepPreservesInv(k, s, s', uiop, dop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepPreservesInv(k, s, s', uiop, dop, blockCacheStep);
        }
      }
      case DiskInternalStep(step) => DiskInternalStepPreservesInv(k, s, s', uiop, step);
      case CrashStep => CrashStepPreservesInv(k, s, s', uiop);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    // pre and post conditions are inherited
    //requires Inv(k, s)
    //requires Next(k, s, s', uiop)
    //ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInv(k, s, s', uiop, step);
  }
}
