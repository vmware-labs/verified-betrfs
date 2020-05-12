include "BlockDisk.i.dfy"
include "JournalDisk.i.dfy"

module BlockJournalDisk {
  import BlockDisk
  import JournalDisk

  datatype Constants = Constants(
    bd: BlockDisk.Constants,
    jd: JournalDisk.Constants)

  datatype Variables = Variables(
    bd: BlockDisk.Variables,
    jd: JournalDisk.Variables)

  datatype DiskOp = DiskOp(
    bdop: BlockDisk.DiskOp,
    jdop: JournalDisk.DiskOp)

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && BlockDisk.Next(k.bd, s.bd, s'.bd, dop.bdop)
    && JournalDisk.Next(k.jd, s.jd, s'.jd, dop.jdop)
  }
}
