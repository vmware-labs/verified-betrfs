include "MapSpec.dfy"
include "Disk.dfy"

include "BetreeBlockCache.dfy"

abstract module Main {
  import MS = MapSpec // spec
  import M = BetreeBlockCache // impl
  import D = Disk

  type Value = M.G.Value // FIXME
  type LBA = D.LBA
  type ByteSector = M.BC.Sector // FIXME
  type DiskOp = D.DiskOp<ByteSector>

  class DiskIOHandler {
    ghost var dop: DiskOp;

    method write(lba: LBA, sector: ByteSector)
    modifies this;
    requires dop == D.NoDiskOp;
    ensures dop == D.WriteOp(lba, sector);
    {
      dop := D.WriteOp(lba, sector);
      // TODO call out to some API
    }

    method read(lba: LBA) returns (sector: ByteSector)
    modifies this
    requires dop == D.NoDiskOp
    ensures dop == D.ReadOp(lba, sector)
    {
      assume false;
      // TODO call out to some API
    }

    predicate initialized()
    reads this
    {
      dop == D.NoDiskOp
    }

    constructor ()
    ensures dop == D.NoDiskOp
  }

  type Constants // impl defined
  type Variables // impl defined (heap state)

  type UIOp = MS.UI.Op<Value>

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
  ensures Next(k, old(world.interp(k)), world.interp(k), MS.UI.NoOp)
  // impl defined

  lemma StateRefinesInv(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures M.Inv(Ik(k), I(k, s))
  // proved by impl
}
