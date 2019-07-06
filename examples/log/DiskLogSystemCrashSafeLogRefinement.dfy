include "CrashSafeLog.dfy"
include "DiskLogSystem.dfy"

module DiskLogSystemCrashSafeLogRefinement {
  import DLS = DiskLogSystemInv
  import CSL = CrashSafeLog

  function Ik(k: DLS.Constants) : CSL.Constants {
    CSL.LS.Constants()
  }

  type Element = DLS.M.LBAType.LogSpec.Element

  function ExtractDiskPrefix(k: DLS.D.Constants, s: DLS.M.DiskVariables, n: int) : (log: CSL.LS.Log)
    requires DiskIsValidLog(k, s)
    requires 0 <= n <= LengthFromSuperblock(k, s)
    ensures n == |log|
    ensures forall i :: 0 <= i < n ==> log[i] == s.blocks[DLS.M.LBAType.indexToLBA(IndexCtor(i))].element
  {
    if n == 0 then
      []
    else
      ExtractDiskPrefix(k, s, n - 1) + [s.blocks[DLS.M.LBAType.indexToLBA(IndexCtor(n - 1))].element]
  }

  function IDisk(k: DLS.D.Constants, s: DLS.M.DiskVariables) : CSL.LS.Variables
  {
    CSL.LS.Variables(
      if DiskIsValidLog(k, s) then
        ExtractDiskPrefix(k, s, s.blocks[DLS.M.SuperblockLBA()].superblock.length)
      else
        [])
  }

  function IEphemeral(k: DLS.Constants, s: DLS.Variables) : CSL.LS.Variables
  {
    if DLS.M.SupersedesDisk(k.machine, s.machine) then
      CSL.LS.Variables(s.machine.log)
    else
      IDisk(k.disk, s.disk)
  }
  
  function I(k: DLS.Constants, s: DLS.Variables) : CSL.Variables
  {
    CSL.Variables(IDisk(k.disk, s.disk), IEphemeral(k, s))
  }

  lemma RefinesMachine(k: DLS.Constants, s: DLS.Variables, s': DLS.Variables, step: DLS.Step)
    requires DLS.NextStep(k, s, s', step)
    requires step.MachineStep?
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
  {
    var mstep :| DLS.M.NextStep(k.machine, s.machine, s'.machine, step.diskOp, mstep);
    match mstep {
      case QueryStep(idx: Index, result: Element) => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FetchSuperblockStep(length: int) => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FetchElementStep(idx: Index, element: Element) => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case AppendStep(element: Element) => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case StageElementStep() => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FlushStep() => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.SyncStep); // witness
      }
      case StutterStep() => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
    }
  }

  lemma RefinesNextStep(k: DLS.Constants, s: DLS.Variables, s':DLS.Variables, step: DLS.Step)
    requires DLS.NextStep(k, s, s', step)
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
  {
    match step {
      case MachineStep(_: DLS.M.DiskOp) => {
        RefinesMachine(k, s, s', step);
      }
      case CrashStep => {
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.CrashStep); // witness
      }
    }
  }
  
  lemma RefinesNext(k: DLS.Constants, s: DLS.Variables, s': DLS.Variables)
    requires DLS.Next(k, s, s')
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
  {
    var step :| DLS.NextStep(k, s, s', step);
    RefinesNextStep(k, s, s', step);
  }

}
