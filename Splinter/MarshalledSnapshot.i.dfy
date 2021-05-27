// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "Allocation.i.dfy"
include "CacheIfc.i.dfy"

module MarshalledSnapshot {
  import opened Options
  // A snapshot of a data structure, spread across a linked list of CUs on the disk.
  // This module almost certainly shares a bunch of DNA with Journal; TODO refactor.
  import opened AllocationMod
  import opened NativeTypes

  datatype SnapshotSuperblock = SnapshotSuperblock(firstCU: Option<CU>)

  datatype Block = Block()
  type Snapshot = seq<Block>

  predicate ValidSnapshot(dv: DiskView, snapshot: Snapshot) {
    false // TODO
  }

  function IBytes(dv: DiskView, sb: SnapshotSuperblock) : seq<byte> {
    if (exists snapshot :: ValidSnapshot(dv, snapshot))
    then
      // TODO decode all the blocks
      []
    else
      []
  }
}
