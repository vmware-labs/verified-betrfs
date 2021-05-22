// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Spec.s.dfy"
include "AsyncDisk.s.dfy"
include "../lib/Base/MapRemove.s.dfy"
include "../lib/Checksums/CRC32C.s.dfy"

// Disk API Interface to the implementer-supplied program that is getting verified.
abstract module AsyncDiskProgram {
  import D = AsyncDisk  // Importing for the interface, not the entire disk
  import CrashTolerantMapSpecMod

  type Variables
  type UIOp = CrashTolerantMapSpecMod.UIOp

  type DiskOp = D.DiskOp
  type ReqRead = D.ReqRead
  type ReqWrite = D.ReqWrite
  type RespRead = D.RespRead
  type RespWrite = D.RespWrite

  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}
