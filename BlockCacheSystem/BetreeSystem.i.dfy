include "BlockDisk.i.dfy"
include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "BlockSystem.i.dfy"
include "BetreeCache.i.dfy"
include "../BlockCacheSystem/BlockSystem_Refines_StatesView.i.dfy"
//
// Instantiate the {PivotBetree, BlockCache} code in a System (model of the environment).
// ("Bottom lettuce")
//

// TODO(jonh): Rename PivotBetreeBlockCacheSystem. [approved by thance]

module BetreeSystem {
  import D = BlockDisk
  import M = BetreeCache
  import AsyncSectorDiskModelTypes
  import opened SectorType
  import opened ViewOp
  import opened DiskLayout
  import opened Maps
  import opened Sequences
  import opened Options

  import opened PivotBetreeSpec`Spec
  import BC = BlockCache
  import BCS = BlockSystem
  import BT = PivotBetree
  import BI = PivotBetreeBlockInterface
  import Ref = BlockSystem_Refines_StatesView

  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>

  datatype Step =
    | MachineStep(dop: D.DiskOp)
    | CrashStep
  
  predicate Machine(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
  {
    && M.Next(s.machine, s'.machine, dop, vop)
    && D.Next(s.disk, s'.disk, dop)
    && (vop.SendPersistentLocOp? ==>
      BCS.Inv(s) ==>
        && vop.loc in Ref.DiskGraphMap(s)
        && BT.Inv(BT.Variables(BI.Variables(Ref.DiskGraphMap(s)[vop.loc])))
    )
  }

  predicate Crash(s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?
    && M.Init(s'.machine)
    && D.Crash(s.disk, s'.disk)
  }

  predicate NextStep(s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(s, s', dop, vop)
      case CrashStep => Crash(s, s', vop)
    }
  }

  predicate Next(s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(s, s', vop, step)
  }

  function BetreeDisk(s: Variables) : imap<Location, BT.Variables>
  requires BCS.Inv(s)
  {
    imap loc | loc in Ref.DiskGraphMap(s) ::
      BT.Variables(BI.Variables(Ref.DiskGraphMap(s)[loc]))
  }

  function FrozenBetree(s: Variables) : Option<BT.Variables>
  requires BCS.Inv(s)
  {
    if Ref.FrozenGraph(s).Some? then
      Some(BT.Variables(BI.Variables(Ref.FrozenGraph(s).value)))
    else
      None
  }

  function EphemeralBetree(s: Variables) : Option<BT.Variables>
  requires BCS.Inv(s)
  {
    if Ref.EphemeralGraph(s).Some? then
      Some(BT.Variables(BI.Variables(Ref.EphemeralGraph(s).value)))
    else
      None
  }

  predicate Init(s: Variables, loc: Location)
  {
    && M.Init(s.machine)
    && D.Init(s.disk)
    && BCS.Init(s, loc)
    && (
      BCS.InitImpliesInv(s, loc);
      && loc in BetreeDisk(s)
      && BT.Init(BetreeDisk(s)[loc])
    )
  }

  predicate Inv(s: Variables) {
    && BCS.Inv(s)
    && (Ref.PersistentLoc(s).Some? ==>
      && Ref.PersistentLoc(s).value in BetreeDisk(s)
      && BT.Inv(BetreeDisk(s)[Ref.PersistentLoc(s).value])
    )
    && (FrozenBetree(s).Some? ==> BT.Inv(FrozenBetree(s).value))
    && (EphemeralBetree(s).Some? ==> BT.Inv(EphemeralBetree(s).value))
    && (Ref.FrozenLoc(s).Some? ==>
      && Ref.FrozenLoc(s).value in BetreeDisk(s)
      && FrozenBetree(s).Some?
      && BetreeDisk(s)[Ref.FrozenLoc(s).value] == FrozenBetree(s).value
    )
  }

  // Proofs

  lemma InitImpliesInv(s: Variables, loc: Location)
    requires Init(s, loc)
    ensures Inv(s)
    ensures loc in BetreeDisk(s)
  {
    BCS.InitImpliesInv(s, loc);
    BT.InitImpliesInv(BetreeDisk(s)[loc]);
    BCS.InitGraphs(s, loc);
  }

  lemma BetreeMoveStepPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
    requires Inv(s)
    requires M.BetreeMove(s.machine, s'.machine, dop, vop, betreeStep)
    requires D.Next(s.disk, s'.disk, dop)
    ensures Inv(s')
  {
    Ref.StepGraphs(s, s', vop, BCS.MachineStep(dop, BC.TransactionStep(BetreeStepOps(betreeStep))));
    Ref.RefinesReads(s, BetreeStepReads(betreeStep));
    //assert BT.Betree(EphemeralBetree(s), EphemeralBetree(s'), uiop, betreeStep);
    assert BT.NextStep(EphemeralBetree(s).value, EphemeralBetree(s').value, vop.uiop, BT.BetreeStep(betreeStep));
    BT.NextPreservesInv(EphemeralBetree(s).value, EphemeralBetree(s').value, vop.uiop);
  }

  lemma BlockCacheMoveStepPreservesInv(s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
    requires Inv(s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(s.machine, s'.machine, dop, vop, step)
    requires D.Next(s.disk, s'.disk, dop)
    requires (vop.SendPersistentLocOp? ==>
      && vop.loc in BetreeDisk(s)
      && BT.Inv(BetreeDisk(s)[vop.loc])
    )
    ensures Inv(s')
  {
    assert BCS.Machine(s, s', dop, vop, step);
    Ref.StepGraphs(s, s', vop, BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(EphemeralBetree(s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(s, s', dop, vop, step.ref);
      assert step.ref in EphemeralBetree(s).value.bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(EphemeralBetree(s).value.bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(s).value.bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(s).value.bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(s).value.bcv.view, iset{step.ref});
      assert BI.GC(EphemeralBetree(s).value.bcv, EphemeralBetree(s').value.bcv, iset{step.ref});
      assert BT.GC(EphemeralBetree(s).value, EphemeralBetree(s').value, UI.NoOp, iset{step.ref});
      BT.GCStepRefines(EphemeralBetree(s).value, EphemeralBetree(s').value, UI.NoOp, iset{step.ref});
    }

    if vop.FreezeOp? {
    }
    else if vop.CrashOp? {
    }
    else if vop.SendPersistentLocOp? {
    }
    else if vop.SendFrozenLocOp? {
    }
    else if vop.CleanUpOp? {
    }
    else if Ref.IsTransactionStep(BCS.MachineStep(dop, step)) {
    }
    else if vop.StatesInternalOp? {
      if Ref.UpdateAllEq(s, s') {
      }
      else if Ref.UpdateDiskChange(s, s') {
      }
      else if Ref.UpdateUnalloc(s, s', BCS.MachineStep(dop, step)) {
      }
      else {
      }
    }
    else if vop.JournalInternalOp? {
      assert Ref.UpdateAllEq(s, s');
    }
    else if vop.PushSyncOp? {
      assert Ref.UpdateAllEq(s, s');
    }
    else if vop.PopSyncOp? {
      assert Ref.UpdateAllEq(s, s');
    }
    else if vop.AdvanceOp? {
    }
    else {
      assert false;
    }
  }

  lemma CrashStepPreservesInv(s: Variables, s': Variables, vop: VOp)
    requires Inv(s)
    requires Crash(s, s', vop)
    ensures Inv(s')
  {
    Ref.StepGraphs(s, s', vop, BCS.CrashStep);
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, vop: VOp, step: Step)
    requires Inv(s)
    requires NextStep(s, s', vop, step)
    ensures Inv(s')
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(s.machine, s'.machine, dop, vop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepPreservesInv(s, s', dop, vop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepPreservesInv(s, s', dop, vop, blockCacheStep);
        }
      }
      case CrashStep => CrashStepPreservesInv(s, s', vop);
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, vop: VOp)
  requires Inv(s)
  requires Next(s, s', vop)
  ensures Inv(s')
  {
    var step :| NextStep(s, s', vop, step);
    NextStepPreservesInv(s, s', vop, step);
  }
}
