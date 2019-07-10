include "DiskLog.dfy"
include "Disk.dfy"

module DiskLogSystem {
  import M = DiskLog
  import D = Disk

  state machine k(disk: D.Constants, machine: M.Constants) s(disk: D.Variables<M.LBAType.LBA, M.Sector>, machine: M.Variables) step()

  init
  {
    && M.Mkfs(k.machine, k.disk, s.disk)
    && M.Init(k.machine, s.machine)
  }

  step Machine(diskOp: M.DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, diskOp)
    && D.Next(k.disk, s.disk, s'.disk, diskOp)
  }

  step Crash()
  {
    && M.Init(k.machine, s'.machine)
    && s'.disk == s.disk
  }
}
