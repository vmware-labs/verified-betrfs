include "LogSpec.dfy"
include "Disk.dfy"
include "DiskAccessModel.dfy"

module DiskTypes {
  type LBA = int
  type SimpleSector = (bool, int)
}

abstract module Machine refines DiskAccessMachine {
  import DiskTypes

  type Constants
  type Variables
}

abstract module Main {
  import M : Machine
  import D = Disk

  import LS = LogSpec
  import DiskTypes

  type Constants // impl defined
  type HeapState // impl defined (heap state)
  function HeapSet(hs: HeapState) : set<object>

  predicate Inv(k: Constants, hs: HeapState)
    reads HeapSet(hs)
  function Ik(k: Constants): M.Constants
  function I(k: Constants, hs: HeapState): M.Variables
    reads HeapSet(hs)
  function ILBA(lba: LBA) : M.LBA

  predicate ValidSector(sector: Sector)

  function ISector(sector: Sector) : M.Sector
    requires ValidSector(sector)

  method InitState() returns (k: Constants, hs: HeapState)
    ensures Inv(k, hs)

  // DiskInterface

  type LBA = DiskTypes.LBA
  type Sector = DiskTypes.SimpleSector
  type DiskOp = D.DiskOp<LBA, Sector>

  predicate ValidDiskOp(dop: DiskOp)
  {
    match dop {
      case ReadOp(lba, sector) => ValidSector(sector)
      case WriteOp(lba, sector) => ValidSector(sector)
      case NoDiskOp => true
    }
  }

  class DiskIOHandler {
    method {:axiom} write(lba: LBA, sector: (bool, int))
    modifies this;
    requires diskOp() == D.NoDiskOp;
    requires ValidSector(sector)
    ensures diskOp() == D.WriteOp(lba, sector);

    method {:axiom} read(lba: LBA) returns (sector: (bool, int))
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReadOp(lba, sector)
    ensures ValidSector(sector)

    function {:axiom} diskOp() : DiskOp
    reads this
    ensures ValidDiskOp(diskOp())

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }

  function IDiskOp(diskOp: DiskOp) : M.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case WriteOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case ReadOp(lba, sector) => D.ReadOp(ILBA(lba), ISector(sector))
      case NoDiskOp => D.NoDiskOp
    }
  }

  // Implementation of the state transitions

  // method handleSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  // returns (success: bool)
  // requires io.initialized()
  // requires Inv(k, hs)
  // modifies HeapSet(hs)
  // modifies io
  // ensures Inv(k, hs)
  // ensures ValidDiskOp(io.diskOp())
  // ensures M.Next(Ik(k), old(I(k, hs)), I(k, hs), IDiskOp(io.diskOp()))
  // // impl defined

  // method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: LS.Key)
  // returns (v: Option<LS.Value>)
  // requires io.initialized()
  // requires Inv(k, hs)
  // modifies HeapSet(hs)
  // modifies io
  // ensures Inv(k, hs)
  // ensures ValidDiskOp(io.diskOp())
  // ensures M.Next(Ik(k), old(I(k, hs)), I(k, hs), IDiskOp(io.diskOp()))
  // // impl defined

  // method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: LS.Key, value: LS.Value)
  // returns (success: bool)
  // requires io.initialized()
  // requires Inv(k, hs)
  // modifies HeapSet(hs)
  // modifies io
  // ensures Inv(k, hs)
  // ensures ValidDiskOp(io.diskOp())
  // ensures M.Next(Ik(k), old(I(k, hs)), I(k, hs), IDiskOp(io.diskOp()))
  // impl defined


  // TODO add proof obligation that the InitState together with the initial disk state
  // from mkfs together refine to the initial state of the BlockCacheSystem.
}
