include "Disk.dfy"
include "LogSpec.dfy"

abstract module DAMTypes {
  datatype DAMConstants<M,D> = DAMConstants(machine: M, disk: D)
  datatype DAMVariables<M,D> = DAMVariables(machine: M, disk: D)
}

abstract module DiskAccessMachine {
  import D = Disk

  type Constants
  type Variables
  type LBA(==)
  type Sector

  type DiskOp = D.DiskOp<LBA, Sector>

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, diskOp: DiskOp)
}

abstract module DiskAccessModel {
  import D = Disk
  import M : DiskAccessMachine
  import DAMTypes

  type DiskOp = M.DiskOp
  type Constants = DAMTypes.DAMConstants<M.Constants, D.Constants>
  type Variables = DAMTypes.DAMVariables<M.Variables, D.Variables<M.LBA, M.Sector>>
  
  predicate Init(k: Constants, s: Variables)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
  }

  datatype Step =
    | DamStep(diskOp: DiskOp)
    | CrashStep

  predicate Dam(k: Constants, s: Variables, s': Variables, diskOp: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, diskOp)
    && D.Next(k.disk, s.disk, s'.disk, diskOp)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      case DamStep(diskOp) => Dam(k, s, s', diskOp)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }
}
