include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "StateImpl.i.dfy"
include "MarshallingImpl.i.dfy"
include "MkfsModel.i.dfy"

//
// TODO implement this so that it matches the spec of Mkfs
// provided in Main.s.dfy.
//

module {:compileName "MkfsImpl"} MkfsImpl {
  import MarshallingImpl
  import IMM = MarshallingModel
  import opened Options
  import opened NativeTypes
  import opened BucketWeights
  import SM = StateModel
  import opened BucketImpl
  import opened NodeImpl
  import KVList
  import IndirectionTableModel
  import IndirectionTableImpl
  import Marshalling
  import MkfsModel

  import BT = PivotBetreeSpec
  import BC = BetreeGraphBlockCache
  import ReferenceType`Internal
  import opened LBAType
  import opened Bounds
  import ValueType`Internal
  import SI = StateImpl
  import D = AsyncDisk

  import ADM = ByteBetreeBlockCacheSystem

  method Mkfs() returns (diskContents :  map<Addr, seq<byte>>)
  ensures MkfsModel.InitDiskContents(diskContents)
  ensures ADM.BlocksDontIntersect(diskContents)
  {
    WeightBucketEmpty();
    var empty := new MutBucket(KVList.Kvl([], []));
    MutBucket.ReprSeqDisjointOfLen1([empty]);
    var node := new Node([], None, [empty]);

    WeightBucketListOneEmpty();
    assert node.I().buckets == [empty.I()];    // OBSERVE (trigger)
    ghost var sector:SI.Sector := SI.SectorBlock(node);
    ghost var is:SM.Sector := SI.ISector(sector);

    var b1_array := MarshallingImpl.MarshallCheckedSector(SI.SectorBlock(node));
    var b1 := b1_array[..];

    var addr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();
    var loc := Location(addr, |b1| as uint64);
    var sectorIndirectionTable := new IndirectionTableImpl.IndirectionTable.RootOnly(loc);

    assert SM.IIndirectionTable(SI.IIndirectionTable(sectorIndirectionTable)) == BC.IndirectionTable(
      map[0 := LBAType.Location(addr, |b1| as uint64)],
      map[0 := []]
    );

    LBAType.ValidAddrMul(MinNodeBlockIndexUint64());
    assert ValidLocation(Location(addr, |b1| as uint64));
    assert BC.WFCompleteIndirectionTable(SM.IIndirectionTable(SI.IIndirectionTable(sectorIndirectionTable)));
    assert SM.WFSector(SI.ISector(SI.SectorIndirectionTable(sectorIndirectionTable)));
    var b0_array := MarshallingImpl.MarshallCheckedSector(SI.SectorIndirectionTable(sectorIndirectionTable));

    assert b0_array != null;

    var b0 := b0_array[..];

    diskContents := map[
      // Map ref 0 to lba 1
      0 := b0,
      // Put the root at lba 1
      addr := b1
    ];
  }
}
