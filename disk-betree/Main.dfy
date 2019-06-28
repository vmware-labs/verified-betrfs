include "MapSpec.dfy"
include "Disk.dfy"

include "BetreeBlockCache.dfy"

module RealDisk refines Disk {
  newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
  type LBA = int32
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

  trait DiskIOHandler {
    ghost var dop: DiskOp;

    method write(lba: LBA, sector: ByteSector)
    modifies this;
    requires dop == D.NoDiskOp;
    ensures dop == D.WriteOp(lba, sector);

    method read(lba: LBA) returns (sector: ByteSector)
    modifies this
    requires dop == D.NoDiskOp
    ensures dop == D.ReadOp(lba, sector)

    predicate initialized()
    reads this
    {
      dop == D.NoDiskOp
    }
  }
}

// Implementation has to instantiate this
// and refine it to the BetreeBlockCacheSystem (or something...)
// TODO create a proof obligation for said refinement
abstract module Machine {
  import opened DiskInterface
  import UI = UI

  type Constants
  type Variables

  predicate Inv(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op, dop: DiskOp)
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
