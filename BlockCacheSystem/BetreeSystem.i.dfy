include "BlockDisk.i.dfy"
include "../PivotBetree/PivotBetree_Refines_Betree.i.dfy"
include "../lib/Base/Maps.s.dfy"
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

  type Constants = AsyncSectorDiskModelTypes.AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>

  datatype Step =
    | MachineStep(dop: D.DiskOp)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, dop, vop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
    && (vop.SendPersistentLocOp? ==>
      BCS.Inv(k, s) ==>
        && vop.loc in Ref.DiskGraphMap(k, s)
        && BT.Inv(Ik(k), BT.Variables(BI.Variables(Ref.DiskGraphMap(k, s)[vop.loc])))
    )
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', dop, vop)
      case CrashStep => Crash(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }

  function Ik(k: Constants) : BT.Constants
  {
    BT.Constants(BI.Constants())
  }

  function BetreeDisk(k: Constants, s: Variables) : imap<Location, BT.Variables>
  requires BCS.Inv(k, s)
  {
    imap loc | loc in Ref.DiskGraphMap(k, s) ::
      BT.Variables(BI.Variables(Ref.DiskGraphMap(k, s)[loc]))
  }

  function FrozenBetree(k: Constants, s: Variables) : Option<BT.Variables>
  requires BCS.Inv(k, s)
  {
    if Ref.FrozenGraph(k, s).Some? then
      Some(BT.Variables(BI.Variables(Ref.FrozenGraph(k, s).value)))
    else
      None
  }

  function EphemeralBetree(k: Constants, s: Variables) : Option<BT.Variables>
  requires BCS.Inv(k, s)
  {
    if Ref.EphemeralGraph(k, s).Some? then
      Some(BT.Variables(BI.Variables(Ref.EphemeralGraph(k, s).value)))
    else
      None
  }

  predicate Init(k: Constants, s: Variables, loc: Location)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
    && BCS.Init(k, s, loc)
    && (
      BCS.InitImpliesInv(k, s, loc);
      && loc in BetreeDisk(k, s)
      && BT.Init(Ik(k), BetreeDisk(k, s)[loc])
    )
  }

  predicate Inv(k: Constants, s: Variables) {
    && BCS.Inv(k, s)
    && (Ref.PersistentLoc(k, s).Some? ==>
      && Ref.PersistentLoc(k, s).value in BetreeDisk(k, s)
      && BT.Inv(Ik(k), BetreeDisk(k, s)[Ref.PersistentLoc(k, s).value])
    )
    && (FrozenBetree(k, s).Some? ==> BT.Inv(Ik(k), FrozenBetree(k, s).value))
    && (EphemeralBetree(k, s).Some? ==> BT.Inv(Ik(k), EphemeralBetree(k, s).value))
    && (Ref.FrozenLoc(k, s).Some? ==>
      && Ref.FrozenLoc(k, s).value in BetreeDisk(k, s)
      && FrozenBetree(k, s).Some?
      && BetreeDisk(k, s)[Ref.FrozenLoc(k, s).value] == FrozenBetree(k, s).value
    )
  }

  // Proofs

  lemma InitImpliesInv(k: Constants, s: Variables, loc: Location)
    requires Init(k, s, loc)
    ensures Inv(k, s)
    ensures loc in BetreeDisk(k, s)
  {
    BCS.InitImpliesInv(k, s, loc);
    BT.InitImpliesInv(Ik(k), BetreeDisk(k, s)[loc]);
    BCS.InitGraphs(k, s, loc);
  }

  lemma BetreeMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, betreeStep: BetreeStep)
    requires Inv(k, s)
    requires M.BetreeMove(k.machine, s.machine, s'.machine, dop, vop, betreeStep)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', vop, BCS.MachineStep(dop, BC.TransactionStep(BetreeStepOps(betreeStep))));
    Ref.RefinesReads(k, s, BetreeStepReads(betreeStep));
    //assert BT.Betree(Ik(k), EphemeralBetree(k, s), EphemeralBetree(k, s'), uiop, betreeStep);
    assert BT.NextStep(Ik(k), EphemeralBetree(k, s).value, EphemeralBetree(k, s').value, vop.uiop, BT.BetreeStep(betreeStep));
    BT.NextPreservesInv(Ik(k), EphemeralBetree(k, s).value, EphemeralBetree(k, s').value, vop.uiop);
  }

  lemma BlockCacheMoveStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: D.DiskOp, vop: VOp, step: BC.Step)
    requires Inv(k, s)
    requires !step.TransactionStep?
    requires M.BlockCacheMove(k.machine, s.machine, s'.machine, dop, vop, step)
    requires D.Next(k.disk, s.disk, s'.disk, dop)
    requires (vop.SendPersistentLocOp? ==>
      && vop.loc in BetreeDisk(k, s)
      && BT.Inv(Ik(k), BetreeDisk(k, s)[vop.loc])
    )
    ensures Inv(k, s')
  {
    assert BCS.Machine(k, s, s', dop, vop, step);
    Ref.StepGraphs(k, s, s', vop, BCS.MachineStep(dop, step));
    if (step.UnallocStep?) {
      //assert BI.GC(Ik(k).bck, EphemeralBetree(k, s).bcv, s'.bcv, refs)
      Ref.UnallocStepMeetsGCConditions(k, s, s', dop, vop, step.ref);
      assert step.ref in EphemeralBetree(k, s).value.bcv.view;
      assert iset{step.ref} !! BI.LiveReferences(Ik(k).bck, EphemeralBetree(k, s).value.bcv);
      assert BI.ClosedUnderPredecessor(EphemeralBetree(k, s).value.bcv.view, iset{step.ref});
      assert IMapRemove1(EphemeralBetree(k, s).value.bcv.view, step.ref)
          == IMapRemove(EphemeralBetree(k, s).value.bcv.view, iset{step.ref});
      assert BI.GC(Ik(k).bck, EphemeralBetree(k, s).value.bcv, EphemeralBetree(k, s').value.bcv, iset{step.ref});
      assert BT.GC(Ik(k), EphemeralBetree(k, s).value, EphemeralBetree(k, s').value, UI.NoOp, iset{step.ref});
      BT.GCStepRefines(Ik(k), EphemeralBetree(k, s).value, EphemeralBetree(k, s').value, UI.NoOp, iset{step.ref});
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
      if Ref.UpdateAllEq(k, s, s') {
      }
      else if Ref.UpdateDiskChange(k, s, s') {
      }
      else if Ref.UpdateUnalloc(k, s, s', BCS.MachineStep(dop, step)) {
      }
      else {
      }
    }
    else if vop.JournalInternalOp? {
      assert Ref.UpdateAllEq(k, s, s');
    }
    else if vop.PushSyncOp? {
      assert Ref.UpdateAllEq(k, s, s');
    }
    else if vop.PopSyncOp? {
      assert Ref.UpdateAllEq(k, s, s');
    }
    else if vop.AdvanceOp? {
    }
    else {
      assert false;
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
    requires Inv(k, s)
    requires Crash(k, s, s', vop)
    ensures Inv(k, s')
  {
    Ref.StepGraphs(k, s, s', vop, BCS.CrashStep);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', vop, step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop) => {
        var machineStep :| M.NextStep(k.machine, s.machine, s'.machine, dop, vop, machineStep);
        match machineStep {
          case BetreeMoveStep(betreeStep) => BetreeMoveStepPreservesInv(k, s, s', dop, vop, betreeStep);
          case BlockCacheMoveStep(blockCacheStep) => BlockCacheMoveStepPreservesInv(k, s, s', dop, vop, blockCacheStep);
        }
      }
      case CrashStep => CrashStepPreservesInv(k, s, s', vop);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires Inv(k, s)
  requires Next(k, s, s', vop)
  ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', vop, step);
    NextStepPreservesInv(k, s, s', vop, step);
  }
}
