include "../ByteBlockCacheSystem/ByteSystem.i.dfy"
include "../BlockCacheSystem/BetreeSystem.i.dfy"
include "../BlockCacheSystem/BetreeJournalSystem_Refines_CompositeView.i.dfy"

module MkfsModel {
  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes
  import opened BucketsLib
  import opened Bounds
  import opened SectorType
  import opened InterpretationDiskOps
  import opened InterpretationDisk
  import opened InterpretationDiskContents
  import BT = PivotBetree
  import ADM = ByteSystem
  import opened DiskLayout
  import BC = BlockCache
  import Marshalling
  import BBCS = BetreeSystem
  import BCS = BlockSystem
  import BI = PivotBetreeBlockInterface
  import Ref = BetreeJournalSystem_Refines_CompositeView
  import BlockSystem
  import BetreeSystem
  import JournalSystem
  import BetreeJournalSystem
  import ByteSystem
  import AsyncSectorDiskModelTypes
  import StatesViewMap
  import JournalView
  import PivotBetree_Refines_Map

  predicate InitDiskContents(diskContents: map<uint64, seq<byte>>)
  {
    && var s1addr := Superblock1Location().addr;
    && var s2addr := Superblock2Location().addr;
    && var indirectionTableAddr := IndirectionTable1Addr();
    && var nodeAddr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();
    && diskContents.Keys ==
        {s1addr, s2addr, indirectionTableAddr, nodeAddr}
    && var bSuperblock := diskContents[s1addr];
    && bSuperblock == diskContents[s2addr]
    && var bIndirectionTable := diskContents[indirectionTableAddr];
    && var bNode := diskContents[nodeAddr];
    && |bIndirectionTable| <= IndirectionTableBlockSize() as int
    && |bNode| <= NodeBlockSize() as int
    && |bSuperblock| == 4096
    && var indirectionTableLoc := Location(indirectionTableAddr, |bIndirectionTable| as uint64);
    && var nodeLoc := Location(nodeAddr, |bNode| as uint64);
    && Marshalling.parseCheckedSector(bIndirectionTable)
      == Some(SectorIndirectionTable(IndirectionTable(
        map[BT.G.Root() := nodeLoc],
        map[BT.G.Root() := []],
        0
      )))
    && Marshalling.parseCheckedSector(bNode)
      == Some(SectorNode(BT.EmptyNode()))
    && Marshalling.parseCheckedSector(bSuperblock)
      == Some(SectorSuperblock(Superblock(0, 0, 0, indirectionTableLoc)))
  }

  lemma InitialStateSatisfiesSystemInit(
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  requires ADM.M.Init(s.machine)
  requires ADM.D.Init(s.disk)
  requires InitDiskContents(diskContents)
  requires ADM.BlocksWrittenInByteSeq(diskContents, s.disk.contents)
  ensures ADM.Init(s)
  {
    Marshalling.reveal_parseCheckedSector();

    var s1addr := Superblock1Location().addr;
    var s2addr := Superblock1Location().addr;
    var indirectionTableAddr := IndirectionTable1Addr();
    var nodeAddr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();

    var bSuperblock := diskContents[s1addr];
    var bIndirectionTable := diskContents[indirectionTableAddr];
    var bNode := diskContents[nodeAddr];

    var indirectionTableLoc := Location(indirectionTableAddr, |bIndirectionTable| as uint64);
    var nodeLoc := Location(nodeAddr, |bNode| as uint64);

    assert ValidNodeLocation(nodeLoc)
      by {
        ValidNodeAddrMul(MinNodeBlockIndexUint64());
      }
    assert ValidIndirectionTableLocation(indirectionTableLoc);

    assert ValidNodeBytes(bNode)
        && NodeOfBytes(bNode) == BT.EmptyNode()
      by {
        reveal_SectorOfBytes();
        reveal_ValidCheckedBytes();
        reveal_Parse();
        D.reveal_ChecksumChecksOut();
      }

    assert ValidSuperblockBytes(bSuperblock)
        && SuperblockOfBytes(bSuperblock)
        == Superblock(0, 0, 0, indirectionTableLoc)
      by {
        reveal_SectorOfBytes();
        reveal_ValidCheckedBytes();
        reveal_Parse();
        D.reveal_ChecksumChecksOut();
      }

    assert ValidIndirectionTableBytes(bIndirectionTable)
        && IndirectionTableOfBytes(bIndirectionTable)
          == IndirectionTable(
              map[BT.G.Root() := nodeLoc],
              map[BT.G.Root() := []],
              0
            )
      by {
        reveal_SectorOfBytes();
        reveal_ValidCheckedBytes();
        reveal_Parse();
        D.reveal_ChecksumChecksOut();
      }

    assert atLoc(Superblock1Location(), s.disk.contents) == bSuperblock
      by { reveal_atLoc(); }

    assert atLoc(Superblock2Location(), s.disk.contents) == bSuperblock
      by { reveal_atLoc(); }

    assert atLocWithWrites(nodeLoc, s.disk.contents, s.disk.reqWrites) == bNode
      by {
        reveal_atLoc();
        withEmptyWrites(s.disk.contents, nodeLoc);
      }

    assert atLocWithWrites(indirectionTableLoc, s.disk.contents, s.disk.reqWrites) == bIndirectionTable
      by {
        reveal_atLoc();
        withEmptyWrites(s.disk.contents, indirectionTableLoc);
      }

    var blockDisk := IBlockDisk(s.disk);
    var journalDisk := IJournalDisk(s.disk);

    var betreeCache := s.machine.bc;
    var journalCache := s.machine.jc;

    var betreeSystem :=
        AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables(
            betreeCache, blockDisk);

    var journalSystem :=
        AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables(
            journalCache, journalDisk);

    var betreeJournalSystem := BetreeJournalSystem.Variables(betreeSystem, journalSystem);

    assert BlockSystem.Init(betreeSystem, indirectionTableLoc);
    BlockSystem.InitGraphsValue(betreeSystem, indirectionTableLoc);

    JournalSystem.InitJournals(journalSystem, indirectionTableLoc);

    assert BetreeSystem.Init(betreeSystem, indirectionTableLoc);
    assert JournalSystem.Init(journalSystem, indirectionTableLoc);

    JournalSystem.InitImpliesInv(journalSystem, indirectionTableLoc);
    BetreeSystem.InitImpliesInv(betreeSystem, indirectionTableLoc);

    var pivotBt := BT.Variables(BI.Variables(
          imap[BT.G.Root() := BT.EmptyNode()]));
    BT.InitImpliesInv(pivotBt);
    PivotBetree_Refines_Map.RefinesInit(pivotBt);

    assert BetreeSystem.BetreeDisk(betreeSystem)[indirectionTableLoc]
        == pivotBt;

    var cview := BetreeJournalSystem.I(betreeJournalSystem);

    assert StatesViewMap.Init(cview.tsm, indirectionTableLoc);
    assert JournalView.Init(cview.jc, indirectionTableLoc);

    assert BetreeJournalSystem.InitWithLoc(betreeJournalSystem, indirectionTableLoc);
    assert BetreeJournalSystem.Init(betreeJournalSystem);

    /*assert BCS.Init(ADM.ADM.I(s));
    assert BT.Init(
        BBCS.PersistentBetree(ADM.ADM.I(s)));

    assert BBCS.Init(ADM.ADM.I(s));*/
  }
}
