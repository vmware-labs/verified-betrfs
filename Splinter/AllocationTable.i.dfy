// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"
include "AllocationTableMachine.i.dfy"
include "CacheIfc.i.dfy"
include "MarshalledSnapshot.i.dfy"

module AllocationTableMod {
  import opened Options
  import opened AllocationTableMachineMod

  function I(dv: AllocationMod.DiskView, sb: Superblock) : Option<AllocationTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}
