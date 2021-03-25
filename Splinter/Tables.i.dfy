include "Allocation.i.dfy"
include "../lib/Base/Option.s.dfy"

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

module AllocationTableMachineMod refines MarshalledSnapshot {
  type AllocationTable = multiset<AU>

  datatype Variables = Variables(
    table: AllocationTable 
  )

  datatype Step =
    | AddRefStep(au: AU)
    | DropRefStep(au: AU)

  predicate IsFree(s:Variables, au: AU) {
    au !in s.table
  }

  predicate AddRef(s: Variables, s': Variables, au: AU) {
    s'.table == s.table + multiset{au}
  }

  predicate DropRef(s: Variables, s': Variables, au: AU) {
    && !IsFree(s, au)
    && s'.table == s.table - multiset{au}
  }

  predicate NextStep(s: Variables, s': Variables, step: Step) {
    match step {
      case AddRefStep(au) => AddRef(s, s', au)
      case DropRefStep(au) => DropRef(s, s', au)
    }
  }

  predicate Next(s: Variables, s': Variables) {
    exists step :: && NextStep(s, s', step)
  }
}

module AllocationTableMod refines MarshalledSnapshot {
  import opened Options
  import AllocationTableMachineMod

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  function parse(b: seq<byte>) : Option<AllocationTableMachineMod.AllocationTable>
    // TODO

  function I(dv: DiskView, sb: Superblock) : Option<AllocationTableMachineMod.AllocationTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}

module IndirectionTableMod refines MarshalledSnapshot {
  import opened Options

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  type IndirectionTable = map<nat, AU>

  function parse(b: seq<byte>) : Option<IndirectionTable>

  function I(dv: DiskView, sb: Superblock) : Option<IndirectionTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}

