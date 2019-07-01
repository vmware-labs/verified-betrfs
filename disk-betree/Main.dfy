include "MapSpec.dfy"
include "Disk.dfy"
include "DiskAccessModel.dfy"
include "../lib/NativeTypes.dfy"

module DiskTypes {
  import opened NativeTypes
  type LBA = uint32
  type ByteSector = seq<byte>
}

module {:extern} DiskInterface {
  import DT = DiskTypes
  import D = Disk

  type LBA = DT.LBA
  type Sector = DT.ByteSector
  type DiskOp = D.DiskOp<LBA, Sector>

  const BLOCK_SIZE: int := 1024*1024

  trait DiskIOHandler {
    ghost var dop: DiskOp;

    // TODO make these take byte arrays instead for faster imperative code
    method write(lba: LBA, sector: Sector)
    modifies this;
    requires dop == D.NoDiskOp;
    requires |sector| == BLOCK_SIZE
    ensures dop == D.WriteOp(lba, sector);

    method read(lba: LBA) returns (sector: Sector)
    modifies this
    requires dop == D.NoDiskOp
    ensures dop == D.ReadOp(lba, sector)
    ensures |sector| == BLOCK_SIZE

    predicate initialized()
    reads this
    {
      dop == D.NoDiskOp
    }
  }
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

  import Disk
  import DiskInterface
  import UI

  type Constants // impl defined
  type Variables // impl defined (heap state)

  type UIOp = M.UIOp

  // impl defined stuff
  predicate Inv(k: Constants, s: Variables)
  function Ik(k: Constants): M.Constants
  function I(k: Constants, s: Variables): M.Variables
  function Constants() : M.Constants
  function ILBA(lba: DiskInterface.LBA) : M.LBA
  function ISector(sector: DiskInterface.Sector) : M.Sector
  function method InitConstants() : Constants
  function method InitVariables() : Variables

  datatype FWorld = FWorld(s: M.Variables, dop: DiskInterface.DiskOp)

  class World {
    var diskIOHandler : DiskInterface.DiskIOHandler
    var s : Variables

    function interp(k: Constants) : FWorld
    reads this
    reads diskIOHandler
    {
      FWorld(I(k, s), diskIOHandler.dop)
    }

    constructor ()
  }

  function IDiskOp(diskOp: DiskInterface.DiskOp) : M.DiskOp {
    match diskOp {
      case WriteOp(lba, sector) => Disk.WriteOp(ILBA(lba), ISector(sector))
      case ReadOp(lba, sector) => Disk.WriteOp(ILBA(lba), ISector(sector))
      case NoDiskOp => Disk.NoDiskOp
    }
  }

  predicate Next(k: Constants, fw: FWorld, fw': FWorld, uiop: UIOp)
  {
    M.Next(Ik(k), fw.s, fw'.s, uiop, IDiskOp(fw'.dop))
  }

  method handle(k: Constants, world: World)
  modifies world
  requires world.diskIOHandler.initialized()
  requires Inv(k, world.s)
  ensures Inv(k, world.s)
  ensures Next(k, old(world.interp(k)), world.interp(k), UI.NoOp)
  // impl defined
}
