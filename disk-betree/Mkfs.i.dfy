include "Marshalling.i.dfy"
include "Impl.i.dfy"
include "ImplState.i.dfy"
include "ImplMarshalling.i.dfy"

// TODO make separate spec abstract module
module {:extern} MkfsImpl {
  import ImplMarshalling
  import IMM = ImplMarshallingModel
  import opened Options
  import opened NativeTypes
  import opened Impl
  import opened BucketWeights
  import IM = ImplModel
  import opened MutableBucket
  import opened ImplNode
  import KVList

  import BT = PivotBetreeSpec
  import BC = BetreeGraphBlockCache
  import ReferenceType`Internal
  import LBAType
  import ValueWithDefault`Internal
  import IS = ImplState
  import D = AsyncDisk

  type LBA = LBAType.LBA

  // TODO spec out that the data returned by this function
  // satisfies the initial conditions
  // TODO prove that this always returns an answer (that is, marshalling always succeeds)
  method InitDiskBytes() returns (m :  map<LBA, array<byte>>)
  {
    assume WeightBucket(KVList.I(KVList.Kvl([],[]))) < 0x1_0000_0000_0000_0000;
    var empty := new MutBucket(KVList.Kvl([], []));
    MutBucket.ReprSeqDisjointOfLen1([empty]);
    var node := new Node([], None, [empty]);
    assume node.Inv();
    assume IM.WFNode(node.I());
    var b1 := ImplMarshalling.MarshallCheckedSector(IS.SectorBlock(node));

    var sectorIndirectionTable := new IS.MutIndirectionTable(1024); // TODO magic number
    assume sectorIndirectionTable.Count == 0;
    var _ := sectorIndirectionTable.Insert(0, (Some(LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)), []));
    assert IM.IIndirectionTable(IS.IIndirectionTable(sectorIndirectionTable)) == BC.IndirectionTable(
      map[0 := LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)],
      map[0 := []]
    );

    assume IS.WFSector(IS.SectorIndirectionTable(sectorIndirectionTable));
    assume IM.WFSector(IS.ISector(IS.SectorIndirectionTable(sectorIndirectionTable)));
    var b0 := ImplMarshalling.MarshallCheckedSector(IS.SectorIndirectionTable(sectorIndirectionTable));
    assume b0 != null;

    m := map[
      // Map ref 0 to lba 1
      0 := b0,
      // Put the root at lba 1
      LBAType.BlockSize() := b1
    ];

  }
}
