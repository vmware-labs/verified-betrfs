include "BlockCache.i.dfy"
include "JournalCache.i.dfy"
include "BlockJournalDisk.i.dfy"

module BlockJournalCache {
  import BlockCache
  import JournalCache
  import D = BlockJournalDisk
  import opened ViewOp
  import UI

  datatype Constants = Constants(
    bc: BlockCache.Constants,
    jc: JournalCache.Constants)

  datatype Variables = Variables(
    bc: BlockCache.Variables,
    jc: JournalCache.Variables)

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp, vop: VOp)
  {
    && VOpAgreesUIOp(vop, uiop)
    && BlockCache.Next(k.bc, s.bc, s'.bc, dop.bdop, vop)
    && JournalCache.Next(k.jc, s.jc, s'.jc, dop.jdop, vop)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: D.DiskOp)
  {
    exists vop :: NextStep(k, s, s', uiop, dop, vop)
  }
}
