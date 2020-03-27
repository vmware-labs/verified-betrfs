include "BetreeCache.i.dfy"
include "JournalCache.i.dfy"
include "BlockJournalDisk.i.dfy"

module BlockJournalCache {
  import BetreeCache
  import JournalCache
  import D = BlockJournalDisk
  import opened ViewOp
  import UI

  datatype Constants = Constants(
    bc: BetreeCache.Constants,
    jc: JournalCache.Constants)

  datatype Variables = Variables(
    bc: BetreeCache.Variables,
    jc: JournalCache.Variables)

  predicate Init(k: Constants, s: Variables)
  {
    && BetreeCache.Init(k.bc, s.bc)
    && JournalCache.Init(k.jc, s.jc)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp, vop: VOp)
  {
    && VOpAgreesUIOp(vop, uiop)
    && BetreeCache.Next(k.bc, s.bc, s'.bc, dop.bdop, vop)
    && JournalCache.Next(k.jc, s.jc, s'.jc, dop.jdop, vop)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  {
    exists vop :: NextStep(k, s, s', uiop, dop, vop)
  }
}
