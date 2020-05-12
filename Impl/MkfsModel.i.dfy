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
        map[BT.G.Root() := []]
      )))
    && Marshalling.parseCheckedSector(bNode)
      == Some(SectorNode(BT.G.Node([], None, [B(map[])])))
    && Marshalling.parseCheckedSector(bSuperblock)
      == Some(SectorSuperblock(Superblock(0, 0, 0, indirectionTableLoc)))
  }

  lemma InitialStateSatisfiesSystemInit(
      k: ADM.Constants, 
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  requires ADM.M.Init(k.machine, s.machine)
  requires ADM.D.Init(k.disk, s.disk)
  requires InitDiskContents(diskContents)
  requires ADM.BlocksWrittenInByteSeq(diskContents, s.disk.contents)
  ensures ADM.Init(k, s)
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
        && NodeOfBytes(bNode) == BT.G.Node([], None, [B(map[])])
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
              map[BT.G.Root() := []]
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

    var betreeK := ByteSystem.Ik(k).bs;
    var journalK := ByteSystem.Ik(k).js;

    var betreeJournalK := BetreeJournalSystem.Constants(betreeK, journalK);
    var betreeJournalSystem := BetreeJournalSystem.Variables(betreeSystem, journalSystem);

    assert BlockSystem.Init(betreeK, betreeSystem, indirectionTableLoc);
    BlockSystem.InitGraphsValue(betreeK, betreeSystem, indirectionTableLoc);

    JournalSystem.InitJournals(journalK, journalSystem, indirectionTableLoc);

    assert BetreeSystem.Init(betreeK, betreeSystem, indirectionTableLoc);
    assert JournalSystem.Init(journalK, journalSystem, indirectionTableLoc);

    JournalSystem.InitImpliesInv(journalK, journalSystem, indirectionTableLoc);
    BetreeSystem.InitImpliesInv(betreeK, betreeSystem, indirectionTableLoc);

    var pivotBt := BT.Variables(BI.Variables(
          imap[BT.G.Root() := BT.G.Node([], None, [B(map[])])]));
    BT.InitImpliesInv(BT.Constants(BI.Constants()), pivotBt);
    PivotBetree_Refines_Map.RefinesInit(
        BT.Constants(BI.Constants()), pivotBt);

    assert BetreeSystem.BetreeDisk(betreeK, betreeSystem)[indirectionTableLoc]
        == pivotBt;

    var ck := BetreeJournalSystem.Ik(betreeJournalK);
    var cview := BetreeJournalSystem.I(betreeJournalK, betreeJournalSystem);

    assert StatesViewMap.Init(ck.tsm, cview.tsm, indirectionTableLoc);
    assert JournalView.Init(ck.jc, cview.jc, indirectionTableLoc);

    assert BetreeJournalSystem.InitWithLoc(betreeJournalK, betreeJournalSystem, indirectionTableLoc);
    assert BetreeJournalSystem.Init(betreeJournalK, betreeJournalSystem);

    /*assert BCS.Init(ADM.Ik(k), ADM.I(k, s));
    assert BT.Init(
        BBCS.Ik(ADM.Ik(k)),
        BBCS.PersistentBetree(ADM.Ik(k), ADM.I(k, s)));

    assert BBCS.Init(ADM.Ik(k), ADM.I(k, s));*/
  }
}
