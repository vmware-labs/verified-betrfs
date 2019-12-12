include "Marshalling.i.dfy"
include "StateImpl.i.dfy"
include "MarshallingImpl.i.dfy"

// TODO make separate spec abstract module
module {:extern} MkfsImpl {
  import MarshallingImpl
  import IMM = MarshallingModel
  import opened Options
  import opened NativeTypes
  import opened BucketWeights
  import SM = StateModel
  import opened BucketImpl`Internal
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

  // TODO spec out that the data returned by this function
  // satisfies the initial conditions
  // TODO prove that this always returns an answer (that is, marshalling always succeeds)
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

    var sectorIndirectionTable := new IndirectionTableImpl.IndirectionTable.Empty();
    sectorIndirectionTable.InvForMkfs();
    sectorIndirectionTable.t.Insert(0, IndirectionTableModel.Entry(Some(LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)), [], 1));

    // TODO(jonh): We're reaching right into sectorIndirectionTable.t above to
    // wangle it. No reason that should preserve sectorIndirectionTable.Inv!
    // Need to improve the contract between sectorIndirectionTable and here.
    assume sectorIndirectionTable.Inv();

    assume SM.IIndirectionTable(SI.IIndirectionTable(sectorIndirectionTable)) == BC.IndirectionTable(
      map[0 := LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)],
      map[0 := []]
    );

    //assert SI.WFSector(SI.SectorIndirectionTable(sectorIndirectionTable));
    assume SM.WFSector(SI.ISector(SI.SectorIndirectionTable(sectorIndirectionTable)));
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
