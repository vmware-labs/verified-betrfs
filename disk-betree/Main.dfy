include "MapSpec.dfy"
include "Disk.dfy"

include "BetreeBlockCache.dfy"

module RealDisk refines Disk {
  newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
  type LBA = uint32
}

module DiskInterface {
  import D = RealDisk

  newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100

  method f() returns (b : byte) {
    return 5;
  }

  type LBA = D.LBA
  type ByteSector = seq<byte>
  type DiskOp = D.DiskOp<ByteSector>

  const BLOCK_SIZE: int := 1024*1024

  trait DiskIOHandler {
    ghost var dop: DiskOp;

    // TODO make these take byte arrays instead for faster imperative code
    method write(lba: LBA, sector: ByteSector)
    modifies this;
    requires dop == D.NoDiskOp;
    requires |sector| == BLOCK_SIZE
    ensures dop == D.WriteOp(lba, sector);

    method read(lba: LBA) returns (sector: ByteSector)
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

// TODO make an abstract MachineSystem that can take any machine

// TODO how to create all the contracts without a dependency on the .i file that instantiates
// the machine? Sounds like it would require parameterized modules?
// IDEALLY we would be able to say: define a machine type M and also give me a proof
// that MachineSystem<M> refines CrashSafeMap

abstract module Machine {
  import opened DiskInterface
  import UI = UI

  type Constants
  type Variables

  predicate Inv(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: DiskOp)

  // TODO create a proof obligation for the refinement
  //lemma Refines(k: Constants, s: Variables, s': Variables, uiop, dop)
  //requires Next(k, s, s', uiop, dop)
  //ensures Next(Ik(k), I(k, s), I(k, s'), uiop, dop)
}

abstract module Main {
  import UI = UI
  import M : Machine

  import opened DiskInterface

  type Value = int

  type Constants // impl defined
  type Variables // impl defined (heap state)

  type UIOp = UI.Op<Value>

  // impl defined stuff
  predicate Inv(k: Constants, s: Variables)
  function Ik(k: Constants): M.Constants
  function I(k: Constants, s: Variables): M.Variables
  function Constants() : M.Constants

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

  predicate Next(k: Constants, fw: FWorld, fw': FWorld, uiop: UIOp)
  {
    M.Next(Ik(k), fw.s, fw'.s, uiop, fw'.dop)
  }

  method handle(k: Constants, world: World)
  modifies world
  requires world.diskIOHandler.initialized()
  requires Inv(k, world.s)
  ensures Inv(k, world.s)
  ensures Next(k, old(world.interp(k)), world.interp(k), UI.NoOp)
  // impl defined

  lemma StateRefinesInv(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures M.Inv(Ik(k), I(k, s))
  // proved by impl
}
