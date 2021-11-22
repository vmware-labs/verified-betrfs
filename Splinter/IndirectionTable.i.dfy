// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"
include "CacheIfc.i.dfy"
include "MarshalledSnapshot.i.dfy"

module IndirectionTableMod refines MarshalledSnapshot {
  import CacheIfc

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  function EmptySuperblock() : Superblock
  {
    Superblock(SnapshotSuperblock(None))
  }

  type IndirectionTable = map<nat, CU>

  function parse(b: seq<byte>) : Option<IndirectionTable>

  function I(dv: DiskView, sb: Superblock) : Option<IndirectionTable> {
    parse(IBytes(dv, sb.snapshot))
  }

  function Empty() : IndirectionTable
  {
    map[]
  }

  predicate DurableAt(itbl: IndirectionTable, cache: CacheIfc.Variables, sb: Superblock)
  {
    // TODO kind of dirty peeking into the entire cache here
    // ValidSnapshot(cache.dv, sb.snapshot)
    true
  }
}
