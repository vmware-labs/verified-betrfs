include "Main.dfy"
include "BetreeBlockCache.dfy"

module Impl refines Main {
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import D = Disk

  type Variables = M.Variables
  type Constants = M.Constants

  function method InitConstants() : Constants { BC.Constants() }
  function method InitVariables() : Variables { BC.Unready }

  method ReadSector(io: DiskInterface.DiskIOHandler, lba: M.LBA)
  returns (sector: M.Sector)
  requires io.initialized()
  ensures IDiskOp(io.dop) == D.ReadOp(lba, sector)
  {
    assume false;
  }

  method PageInSuperblock(k: Constants, s: Variables, io: DiskInterface.DiskIOHandler)
  returns (s': Variables)
  requires io.initialized();
  requires s.Unready?
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.dop))
  {
    var sector := ReadSector(io, BC.SuperblockLBA(k));
    if (sector.SectorSuperblock?) {
      s' := BC.Ready(sector.superblock, sector.superblock, map[]);
    }
  }

  method doStuff(k: Constants, s: Variables, io: DiskInterface.DiskIOHandler)
  returns (s': Variables)
  requires io.initialized()
  ensures M.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp, IDiskOp(io.dop))
  {
    if (s.Unready?) {
      s' := PageInSuperblock(k, s, io);
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.dop), M.BlockCacheMoveStep(BC.PageInSuperblockStep));
    } else {
      assume false;
    }
  }

  method handle(k: Constants, world: World)
  {
    var s := world.s;
    var io := world.diskIOHandler;
    var s' := doStuff(k, s, io);
    world.s := s';
  }
}
