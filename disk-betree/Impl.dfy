include "Main.dfy"
include "BetreeBlockCache.dfy"
include "ByteBetree.dfy"

module {:extern} Impl refines Main {
  import BC = BetreeGraphBlockCache
  import BetreeBC = BetreeBlockCache
  import BT = PivotBetreeSpec
  import M = BetreeBlockCache
  import Marshalling

  type Variables = M.Variables
  type Constants = M.Constants

  class ImplHeapState {
    var s: Variables
    constructor() {
      s := BC.Unready;
    }
  }
  type HeapState = ImplHeapState
  function HeapSet(hs: HeapState) : set<object> { {hs} }

  function Ik(k: Constants) : M.Constants { k }
  function I(k: Constants, hs: HeapState) : M.Variables { hs.s }

  predicate ValidSector(sector: Sector)
  {
    && Marshalling.parseSector(sector).Some?
  }

  function ISector(sector: Sector) : M.Sector
  {
    Marshalling.parseSector(sector).value
  }

  predicate Inv(k: Constants, hs: HeapState)
  {
    BetreeBC.Inv(k, hs.s)
  }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    hs := new ImplHeapState();
  }

  predicate WFSector(sector: M.Sector)
  {
    match sector {
      case SectorSuperblock(superblock) => BC.WFPersistentSuperblock(superblock)
      case SectorBlock(node) => BT.WFNode(node)
    }
  }

  method ReadSector(io: DiskIOHandler, lba: M.LBA)
  returns (sector: M.Sector)
  requires io.initialized()
  modifies io
  ensures IDiskOp(io.diskOp()) == D.ReadOp(lba, sector)
  ensures WFSector(sector)
  {
    var bytes := io.read(lba);
    var sectorOpt := Marshalling.ParseSector(bytes);
    sector := sectorOpt.value;
  }

  method PageInSuperblock(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    var sector := ReadSector(io, BC.SuperblockLBA());
    if (sector.SectorSuperblock?) {
      s' := BC.Ready(sector.superblock, sector.superblock, map[]);
    }
  }

  method doStuff(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    if (s.Unready?) {
      s' := PageInSuperblock(k, s, io);
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.PageInSuperblockStep));
    } else {
      assume false;
    }
  }

  method handle(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    var s' := doStuff(k, s, io);
    hs.s := s';
  }
}
