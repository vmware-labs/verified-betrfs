include "MapSpec.dfy"
include "Disk.dfy"
include "DiskAccessModel.dfy"
include "../lib/NativeTypes.dfy"

module DiskTypes {
  import opened NativeTypes
  type LBA = uint64
  type ByteSector = seq<byte>
}

// Implementation has to instantiate this
// and refine it to the BetreeBlockCache
// either than or BetreeBlockCache itself will be the instantiation of this module?

// TODO how to create all the contracts without a dependency on the .i file that instantiates
// the machine? Sounds like it would require parameterized modules?
// IDEALLY we would be able to say: define a machine type M and also give me a proof
// that MachineSystem<M> refines CrashSafeMap

abstract module Machine refines DiskAccessMachine {
  import UI = UI
  import DiskTypes

  type Constants
  type Variables

  type UIOp = UI.Op

  // TODO create a proof obligation for the refinement
  //lemma Refines(k: Constants, s: Variables, s': Variables, uiop, dop)
  //requires Next(k, s, s', uiop, dop)
  //ensures Next(Ik(k), I(k, s), I(k, s'), uiop, dop)
}

abstract module Main {
  import M : Machine
  import D = Disk

  import opened NativeTypes
  import DiskTypes
  import UI

  type UIOp = M.UIOp

  // impl defined stuff

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

  function method BlockSize() : uint64 { 1024*1024 }

  type LBA = DiskTypes.LBA
  type Sector = DiskTypes.ByteSector
  type DiskOp = D.DiskOp<LBA, Sector>

  predicate ValidDiskOp(dop: DiskOp)
  {
    match dop {
      case ReadOp(lba, sector) => ValidSector(sector)
      case WriteOp(lba, sector) => ValidSector(sector)
      case NoDiskOp => true
    }
  }

  trait DiskIOHandler {
    // TODO make these take byte arrays instead for faster imperative code
    method write(lba: LBA, sector: array<byte>)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    requires sector.Length <= BlockSize() as int
    requires ValidSector(sector[..])
    ensures diskOp() == D.WriteOp(lba, sector[..]);

    method read(lba: LBA) returns (sector: array<byte>)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReadOp(lba, sector[..])
    ensures sector.Length == BlockSize() as int
    ensures ValidSector(sector[..])

    function diskOp() : DiskOp

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }

  // State transitions

  function IDiskOp(diskOp: DiskOp) : M.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case WriteOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case ReadOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case NoDiskOp => D.NoDiskOp
    }
  }

  method handle(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.initialized()
  requires Inv(k, hs)

  modifies HeapSet(hs)
  modifies io

  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, IDiskOp(io.diskOp()))
  // impl defined

  // TODO add proof obligation that the InitState together with the initial disk state
  // from mkfs together refine to the initial state of the BlockCacheSystem.
}
