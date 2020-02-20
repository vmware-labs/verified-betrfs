include "../ByteBlockCacheSystem/ByteBetreeBlockCacheSystem.i.dfy"

module MkfsModel {
  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes
  import opened BucketsLib
  import opened Bounds
  import BT = PivotBetree
  import ADM = ByteBetreeBlockCacheSystem
  import LBAType
  import BC = BetreeGraphBlockCache
  import Marshalling
  import BBCS = BetreeBlockCacheSystem
  import BCS = BetreeGraphBlockCacheSystem
  import BI = PivotBetreeBlockInterface
  import Ref = BlockCacheSystem_Refines_ThreeStateVersionedBlockInterface

  predicate InitDiskContents(diskContents: map<uint64, seq<byte>>)
  {
    && var addr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();
    && diskContents.Keys == {0, addr}
    && var b0 := diskContents[0];
    && var b1 := diskContents[addr];
    && |b0| == IndirectionTableBlockSize() as int
    && |b1| <= NodeBlockSize() as int
    && Marshalling.parseCheckedSector(b0)
      == Some(BC.SectorIndirectionTable(BC.IndirectionTable(
        map[BT.G.Root() := LBAType.Location(addr, |b1| as uint64)],
        map[BT.G.Root() := []]
      )))
    && Marshalling.parseCheckedSector(b1)
      == Some(BC.SectorBlock(BT.G.Node([], None, [B(map[])])))
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
    // TODO(travis) this could probably be cleaned up?

    //assert BCS.Init(k, s);
    //assert BT.Init(Ik(k), PersistentBetree(k, s));
    Marshalling.reveal_parseCheckedSector();
    ADM.M.reveal_Parse();
    ADM.M.reveal_ValidCheckedBytes();
    ADM.M.reveal_IBytes();
    ADM.D.reveal_ChecksumChecksOut();

    var addr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();
    var b0 := diskContents[0];
    var b1 := diskContents[addr];

    assert ADM.M.ValidBytes(b0);
    assert ADM.M.ValidBytes(b1);

    var loc0 := LBAType.IndirectionTableLocation();
    var loc1 := LBAType.Location(addr, |b1| as uint64);

    assert loc0.addr as int + loc0.len as int <= |s.disk.contents|;
    assert s.disk.contents[0 .. |b0|] == b0;
    assert loc0.addr == 0;
    assert loc0.len as int == |b0|;
    assert s.disk.contents[loc0.addr .. loc0.addr as int + loc0.len as int] == b0;
    assert ADM.M.ValidBytes(s.disk.contents[loc0.addr .. loc0.addr as int + loc0.len as int]);
    LBAType.ValidAddr0();
    assert LBAType.ValidLocation(loc0);
    assert LBAType.ValidAddr(loc0.addr);
    assert loc0 in ADM.IContents(s.disk.contents);
    assert ADM.IContents(s.disk.contents)[loc0] == BC.SectorIndirectionTable(BC.IndirectionTable(
        map[BT.G.Root() := loc1],
        map[BT.G.Root() := []]
      ));

    LBAType.ValidAddrMul(MinNodeBlockIndexUint64());
    assert loc1 in ADM.IContents(s.disk.contents);
    assert ADM.IContents(s.disk.contents)[loc1] == 
      BC.SectorBlock(BT.G.Node([], None, [B(map[])]));

    Ref.reveal_PersistentGraph();
    assert BBCS.PersistentBetree(ADM.Ik(k), ADM.I(k, s))
        == BT.Variables(BI.Variables(
          imap[BT.G.Root() := BT.G.Node([], None, [B(map[])])]));

    assert BCS.Init(ADM.Ik(k), ADM.I(k, s));
    assert BT.Init(
        BBCS.Ik(ADM.Ik(k)),
        BBCS.PersistentBetree(ADM.Ik(k), ADM.I(k, s)));

    assert BBCS.Init(ADM.Ik(k), ADM.I(k, s));
  }
}
