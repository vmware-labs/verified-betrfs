include "Disk.dfy"
include "MapSpec.dfy"
include "CrashTypes.dfy"

// Spec for the DiskAccessModel

module DAMTypes {
  datatype DAMConstants<M,D> = DAMConstants(machine: M, disk: D)
  datatype DAMVariables<M,D> = DAMVariables(machine: M, disk: D)
}

abstract module DiskAccessMachine {
  import D = Disk
  import UI

  type Variables
  type Constants
  type LBA(==)
  type Sector
  type UIOp = UI.Op

  type DiskOp = D.DiskOp<LBA, Sector>

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

abstract module DiskAccessModel {
  import D = Disk
  import M : DiskAccessMachine
  import CrashTypes
  import DAMTypes

  type DiskOp = M.DiskOp
  type Constants = DAMTypes.DAMConstants<M.Constants, D.Constants>
  type Variables = DAMTypes.DAMVariables<M.Variables, D.Variables<M.LBA, M.Sector>>
  type CrashableUIOp = CrashTypes.CrashableUIOp<M.UIOp>

  datatype Step =
    | DamStep(dop: DiskOp)
    | CrashStep

  predicate Dam(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, dop: DiskOp)
  {
    && uiop.NormalOp?
    && M.Next(k.machine, s.machine, s'.machine, uiop.uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp)
  {
    && uiop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, step: Step)
  {
    match step {
      case DamStep(dop) => Dam(k, s, s', uiop, dop)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Init(k: Constants, s: Variables)
  predicate Inv(k: Constants, s: Variables)
}
