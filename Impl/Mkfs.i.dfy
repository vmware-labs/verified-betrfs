include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "StateImpl.i.dfy"
include "MarshallingImpl.i.dfy"
include "../lib/Marshalling/Math.i.dfy"

//
// TODO implement this so that it matches the spec of Mkfs
// provided in Main.s.dfy.
//

module {:extern} MkfsImpl {
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

  import BT = PivotBetreeSpec
  import BC = BetreeGraphBlockCache
  import ReferenceType`Internal
  import LBAType
  import ValueWithDefault`Internal
  import SI = StateImpl
  import D = AsyncDisk

  type LBA = LBAType.LBA
  import Math

  lemma LemmaValidAddrBlockSize()
  ensures LBAType.ValidAddr(LBAType.BlockSize())
  {
    LBAType.reveal_ValidAddr();
    Math.lemma_mod_multiples_basic(1, LBAType.BlockSize() as int);
  }

  method InitDiskBytes() returns (m :  map<LBA, array<byte>>)
  {
    WeightBucketEmpty();
    var empty := new MutBucket(KVList.Kvl([], []));
    MutBucket.ReprSeqDisjointOfLen1([empty]);
    var node := new Node([], None, [empty]);

    WeightBucketListOneEmpty();
    assert node.I().buckets == [empty.I()];    // OBSERVE (trigger)
    ghost var sector:SI.Sector := SI.SectorBlock(node);
    ghost var is:SM.Sector := SI.ISector(sector);
    var b1 := MarshallingImpl.MarshallCheckedSector(SI.SectorBlock(node));

    var loc := LBAType.Location(LBAType.BlockSize(), b1.Length as uint64);
    var sectorIndirectionTable := new IndirectionTableImpl.IndirectionTable.RootOnly(loc);

    assert SM.IIndirectionTable(SI.IIndirectionTable(sectorIndirectionTable)) == BC.IndirectionTable(
      map[0 := LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)],
      map[0 := []]
    );

    LemmaValidAddrBlockSize();
    assert LBAType.ValidLocation(LBAType.Location(LBAType.BlockSize(), b1.Length as uint64));
    assert BC.WFCompleteIndirectionTable(SM.IIndirectionTable(SI.IIndirectionTable(sectorIndirectionTable)));
    assert SM.WFSector(SI.ISector(SI.SectorIndirectionTable(sectorIndirectionTable)));
    var b0 := MarshallingImpl.MarshallCheckedSector(SI.SectorIndirectionTable(sectorIndirectionTable));

    // TODO(jonh): MarshallCheckedSector owes us a promise that it can marshall
    // SectorIndirectionTables successfully. It can't make that promise right
    // now, since it only bounds the marshalled size of an indirection table to a gazillion.
    assume b0 != null;

    m := map[
      // Map ref 0 to lba 1
      0 := b0,
      // Put the root at lba 1
      LBAType.BlockSize() := b1
    ];

  }
}
