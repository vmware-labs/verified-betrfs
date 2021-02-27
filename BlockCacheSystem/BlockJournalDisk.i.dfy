// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "BlockDisk.i.dfy"
include "JournalDisk.i.dfy"

module BlockJournalDisk {
  import BlockDisk
  import JournalDisk

  datatype Variables = Variables(
    bd: BlockDisk.Variables,
    jd: JournalDisk.Variables)

  datatype DiskOp = DiskOp(
    bdop: BlockDisk.DiskOp,
    jdop: JournalDisk.DiskOp)

  predicate Next(s: Variables, s': Variables, dop: DiskOp)
  {
    && BlockDisk.Next(s.bd, s'.bd, dop.bdop)
    && JournalDisk.Next(s.jd, s'.jd, dop.jdop)
  }
}
