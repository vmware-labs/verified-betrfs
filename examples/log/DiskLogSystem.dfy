// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "DiskLog.dfy"
include "Disk.dfy"

module DiskLogSystem {
  import M = DiskLog
  import D = Disk

  datatype Constants = Constants(disk: D.Constants, machine: M.Constants)
  datatype Variables = Variables(disk: D.Variables<M.LBAType.LBA, M.Sector>, machine: M.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    && M.Mkfs(k.machine, k.disk, s.disk)
    && M.Init(k.machine, s.machine)
  }

  datatype Step =
    | MachineStep(diskOp: M.DiskOp)
    | CrashStep

  predicate Machine(k: Constants, s: Variables, s': Variables, diskOp: M.DiskOp)
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
      case MachineStep(diskOp) => Machine(k, s, s', diskOp)
      case CrashStep => Crash(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }
  
}
