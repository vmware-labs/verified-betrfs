// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"
include "CacheIfc.i.dfy"

module MarshalledSnapshot {
  // A snapshot of a data structure, spread across a linked list of CUs on the disk.
  // This module almost certainly shares a bunch of DNA with Journal; TODO refactor.
  import opened AllocationMod
  import opened NativeTypes

  datatype SnapshotSuperblock = SnapshotSuperblock(firstCU: CU)

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

// It's funky that the allocation table is going to reserve its own
// blocks, but it's actually okay: we reserve them in the in-memory
// representation, then emit them once we've frozen a given view.

// Does this really need to be a "machine"? IndirectionTable is happy just
// being a little data structure.

module AllocationTableMachineMod refines MarshalledSnapshot {
  import opened Options
  import CacheIfc

  // At this layer we're just going to allocate at CU granularity.
  //
  // Down lower, the real data structure will track only AUs, with an "open AU"
  // in the in-memory data structure that can give out CUs sequentially.
  // TODO this may be a challenge because we're going to want to show
  // allocations are "tight" (so we don't leak), but CUs are going to look
  // "looser" once we're tracking AUs.
  type AllocationTable = multiset<CU>

  datatype Variables = Variables(
    table: AllocationTable 
  )
  {
    // Standard interface for coordinating disjointness among allocations of
    // different subsystems.
    function Allocated() : multiset<CU> { table }
  }

  datatype Step =
    | AddRefStep(cu: CU)
    | DropRefStep(cu: CU)

  predicate IsFree(s:Variables, cu: CU) {
    cu !in s.table
  }

  predicate AddRef(s: Variables, s': Variables, cu: CU) {
    s'.table == s.table + multiset{cu}
  }

  predicate DropRef(s: Variables, s': Variables, cu: CU) {
    && !IsFree(s, cu)
    && s'.table == s.table - multiset{cu}
  }

  predicate NextStep(s: Variables, s': Variables, step: Step) {
    match step {
      case AddRefStep(cu) => AddRef(s, s', cu)
      case DropRefStep(cu) => DropRef(s, s', cu)
    }
  }

  predicate Next(s: Variables, s': Variables) {
    exists step :: && NextStep(s, s', step)
  }

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  predicate DurableAt(s: Variables, cache: CacheIfc.Variables, sb: Superblock)
  {
    // TODO kind of dirty peeking into the entire cache here
    // ValidSnapshot(cache.dv, sb.snapshot)
    true
  }

  function parse(b: seq<byte>) : Option<AllocationTable>
    // TODO

  predicate Disjoint(s1: Variables, s2: Variables)
  {
    s1.table !! s2.table
  }

  function Alloc(s: Variables) : set<CU> {
    {} // TODO
  }
}

module AllocationTableMod {
  import opened Options
  import opened AllocationTableMachineMod

  function I(dv: AllocationMod.DiskView, sb: Superblock) : Option<AllocationTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}

module IndirectionTableMod refines MarshalledSnapshot {
  import opened Options
  import CacheIfc

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  type IndirectionTable = map<nat, CU>

  function parse(b: seq<byte>) : Option<IndirectionTable>

  function I(dv: DiskView, sb: Superblock) : Option<IndirectionTable> {
    parse(IBytes(dv, sb.snapshot))
  }

  predicate DurableAt(itbl: IndirectionTable, cache: CacheIfc.Variables, sb: Superblock)
  {
    // TODO kind of dirty peeking into the entire cache here
    // ValidSnapshot(cache.dv, sb.snapshot)
    true
  }
}

