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
  type Variables // impl defined (heap state)

  predicate Inv(k: Constants, s: Variables)
  function Ik(k: Constants): M.Constants
  function I(k: Constants, s: Variables): M.Variables
  function ILBA(lba: LBA) : M.LBA

  predicate ValidSector(sector: Sector)

  function ISector(sector: Sector) : M.Sector
  requires ValidSector(sector)

  function method InitConstants() : Constants
  function method InitVariables() : Variables

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
    ghost var dop: DiskOp;

    // TODO make these take byte arrays instead for faster imperative code
    method write(lba: LBA, sector: array<byte>)
    modifies this;
    requires dop == D.NoDiskOp;
    requires sector.Length <= BlockSize() as int
    requires ValidSector(sector[..])
    ensures dop == D.WriteOp(lba, sector[..]);

    method read(lba: LBA) returns (sector: array<byte>)
    modifies this
    requires dop == D.NoDiskOp
    ensures dop == D.ReadOp(lba, sector[..])
    ensures sector.Length == BlockSize() as int
    ensures ValidSector(sector[..])

    predicate initialized()
    reads this
    {
      dop == D.NoDiskOp
    }
  }

  // State transitions

  datatype FWorld = FWorld(s: M.Variables, dop: DiskOp)

  class World {
    var diskIOHandler : DiskIOHandler
    var s : Variables

    function interp(k: Constants) : FWorld
    reads this
    reads diskIOHandler
    {
      FWorld(I(k, s), diskIOHandler.dop)
    }

    constructor ()
  }

  function IDiskOp(diskOp: DiskOp) : M.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case WriteOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case ReadOp(lba, sector) => D.WriteOp(ILBA(lba), ISector(sector))
      case NoDiskOp => D.NoDiskOp
    }
  }

  predicate Next(k: Constants, fw: FWorld, fw': FWorld, uiop: UIOp)
  requires ValidDiskOp(fw'.dop)
  {
    M.Next(Ik(k), fw.s, fw'.s, uiop, IDiskOp(fw'.dop))
  }

  method handle(k: Constants, world: World)
  modifies world
  requires world.diskIOHandler.initialized()
  requires Inv(k, world.s)
  ensures Inv(k, world.s)
  ensures ValidDiskOp(world.diskIOHandler.dop)
  ensures Next(k, old(world.interp(k)), world.interp(k), UI.NoOp)
  // impl defined
}
