include "Disk.dfy"
include "MapSpec.dfy"

// Spec for the DiskAccessModel

abstract module DiskAccessMachine {
  import D = Disk
  import UI = UI

  type Variables
  type Constants
  type Sector
  type UIOp

  type DiskOp = D.DiskOp<Sector>

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

abstract module DiskAccessModel {
  import D = Disk
  import M : DiskAccessMachine

  type DiskOp = M.DiskOp
  datatype Constants = Constants(machine: M.Constants, disk: D.Constants)
  datatype Variables = Variables(machine: M.Variables, disk: D.Variables<M.Sector>)
  datatype UIOp = UICrash | UINormal(uiop: M.UIOp)
  
  predicate Init(k: Constants, s: Variables)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
  }

  datatype Step =
    | DamStep(dop: DiskOp)
    | CrashStep

  predicate Dam(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && uiop.UINormal?
    && M.Next(k.machine, s.machine, s'.machine, uiop.uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.UICrash?
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case DamStep(dop) => Dam(k, s, s', uiop, dop)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }
}
