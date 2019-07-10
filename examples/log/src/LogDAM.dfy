include "DiskLog.dfy"

include "Main.dfy"

module LogDAM refines Machine {
  import DL = DiskLog

  type Constants = DL.Constants
  type Variables = DL.Variables
  type LBA(==) = DL.LBAType.LBA
  type Sector = DL.Sector

  predicate Init(k: Constants, s: Variables) {
    DL.Init(k, s)
  }
  predicate Next(k: Constants, s: Variables, s': Variables, diskOp: DiskOp) {
    DL.Next(k, s, s', diskOp)
  }
}
