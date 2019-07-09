include "CrashSafeLog.dfy"
include "DiskLogSystemInv.dfy"

module DiskLogSystemCrashSafeLogRefinement {
  import DLSI = DiskLogSystemInv
  import DLS = DLSI.DiskLogSystem
  import CSL = CrashSafeLog

  function Ik(k: DLS.Constants) : CSL.Constants {
    CSL.LS.Constants()
  }

  type Element = DLS.M.LBAType.LogSpec.Element

  function ExtractDiskPrefix(k: DLS.D.Constants, s: DLS.M.DiskVariables, n: int) : (log: CSL.LS.Log)
    requires DLSI.DiskIsValidLog(k, s)
    requires 0 <= n <= DLSI.LengthFromSuperblock(k, s)
    ensures n == |log|
    ensures forall i :: 0 <= i < n ==> log[i] == DLSI.ElementFromDiskLog(k, s, DLSI.IndexCtor(i))
  {
    if n == 0 then
      []
    else
      ExtractDiskPrefix(k, s, n - 1) + [DLSI.ElementFromDiskLog(k, s, DLSI.IndexCtor(n - 1))]
  }

  function IDisk(k: DLS.D.Constants, s: DLS.M.DiskVariables) : CSL.LS.Variables
  {
    CSL.LS.Variables(
      if DLSI.DiskIsValidLog(k, s) then
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
    requires DLSI.Inv(k, s)
    requires DLSI.Inv(k, s')
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
  {
    var mstep :| DLS.M.NextStep(k.machine, s.machine, s'.machine, step.diskOp, mstep);
    var ik := Ik(k);
    var is := I(k, s);
    var is' := I(k, s');
    match mstep {
      case QueryStep(idx: DLSI.Index, result: Element) => {
        assert is.persistent == is'.persistent;
        assert DLS.M.Query(k.machine, s.machine, s'.machine, step.diskOp, idx, result);
        assert step.diskOp == DLS.D.NoDiskOp;
        if DLS.M.SupersedesDisk(k.machine, s.machine) {
          assert s.machine.log == is.ephemeral.log;
          assert 0 <= idx.idx < |is.ephemeral.log|;
          assert result == is.ephemeral.log[idx.idx];
        } else {
          assert DLSI.MemoryMatchesDisk(k, s);
          assert IDisk(k.disk, s.disk).log == is.ephemeral.log;
          assert |s.machine.log| < DLSI.LengthFromSuperblock(k.disk, s.disk);
          assert 0 <= idx.idx < |is.ephemeral.log|;
          assert result == is.ephemeral.log[idx.idx];
        }
        assert CSL.LS.Query(ik, is.ephemeral, is'.ephemeral, idx, result);
        assert CSL.LS.NextStep(ik, is.ephemeral, is'.ephemeral, CSL.LS.QueryStep(idx, result));
        assert CSL.LS.Next(ik, is.ephemeral, is'.ephemeral);
        assert CSL.EphemeralMove(ik, is, is');
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FetchSuperblockStep(length: int) => {
        assert DLS.M.FetchSuperblock(k.machine, s.machine, s'.machine, step.diskOp, length);
        assert DLSI.MemoryMatchesDisk(k, s);
        assert DLSI.MemoryMatchesDisk(k, s');
        assert s.machine.persistent == DLS.M.Unready;
        assert s'.machine.log == s.machine.log;
        assert s'.machine.persistent == DLS.M.Ready(DLS.M.Superblock(length));
        assert !DLS.M.SupersedesDisk(k.machine, s.machine);
        if DLS.M.SupersedesDisk(k.machine, s'.machine) {
          assert s'.machine.persistent.superblock.length <= |s.machine.log|;
          assert IEphemeral(k, s) == IDisk(k.disk, s.disk);
          assert is'.persistent == is.persistent;

          assert DLSI.MemoryMatchesDisk(k, s);
          // assert forall idx : DLSI.Index :: 0 <= idx.idx < |s.machine.log| ==> s.machine.log[idx.idx] == DLSI.ElementFromDiskLog(k.disk, s.disk, idx);
          assert DLSI.DiskIsValidLog(k.disk, s.disk);
          if |s.machine.log| == 0 {
            assert s.machine.log == IDisk(k.disk, s.disk).log;
          } else {
            assert false;
            //assert s.machine.log == ExtractDiskPrefix(k.disk, s.disk, |s.machine.log|);
            //assert s.machine.log == IDisk(k.disk, s.disk).log;
          }

          assert is.ephemeral.log == IDisk(k.disk, s.disk).log;
          assert is'.ephemeral.log == s.machine.log;
          assert is'.ephemeral.log == s'.machine.log;
          assert is'.ephemeral == CSL.LS.Variables(s.machine.log);

          assert is'.ephemeral == is.ephemeral;

          assert is == is';
        } else {
          assert is == is';
        }
        assert CSL.LS.Stutter(ik, is.ephemeral, is'.ephemeral);
        assert CSL.LS.NextStep(ik, is.ephemeral, is'.ephemeral, CSL.LS.StutterStep);
        assert CSL.LS.Next(ik, is.ephemeral, is'.ephemeral);
        assert CSL.EphemeralMove(Ik(k), I(k, s), I(k, s'));
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FetchElementStep(idx: DLSI.Index, element: Element) => {
        /* TODO */ assume CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case AppendStep(element: Element) => {
        /* TODO */ assume CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case StageElementStep() => {
        /* TODO */ assume CSL.EphemeralMove(Ik(k), I(k, s), I(k, s'));
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
      case FlushStep() => {
        /* TODO */ assert CSL.Sync(Ik(k), I(k, s), I(k, s'));
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.SyncStep); // witness
      }
      case StutterStep() => {
        /* TODO */ assume CSL.EphemeralMove(Ik(k), I(k, s), I(k, s'));
        assert CSL.NextStep(Ik(k), I(k, s), I(k, s'), CSL.EphemeralMoveStep); // witness
      }
    }
  }

  lemma RefinesNextStep(k: DLS.Constants, s: DLS.Variables, s':DLS.Variables, step: DLS.Step)
    requires DLS.NextStep(k, s, s', step)
    requires DLSI.Inv(k, s)
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
    ensures DLSI.Inv(k, s')
  {
    DLSI.NextPreservesInv(k, s, s');
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
    requires DLSI.Inv(k, s)
    ensures CSL.Next(Ik(k), I(k, s), I(k, s'))
    ensures DLSI.Inv(k, s')
  {
    var step :| DLS.NextStep(k, s, s', step);
    RefinesNextStep(k, s, s', step);
  }

}
