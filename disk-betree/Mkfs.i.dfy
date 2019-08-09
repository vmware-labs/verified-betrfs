include "Marshalling.i.dfy"
include "Impl.i.dfy"

// TODO make separate spec abstract module
module {:extern} MkfsImpl {
  import Marshalling
  import opened Options
  import opened NativeTypes
  import opened Impl

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
    assume Marshalling.CappedNode(IS.SectorBlock(IS.Node([], None, [KMTable.Empty()])).block);
    var b1 := Marshalling.MarshallCheckedSector(IS.SectorBlock(IS.Node([], None, [KMTable.Empty()])));

    var sectorIndirectionTable := new IS.MutIndirectionTable(1024); // TODO magic number
    assume sectorIndirectionTable.Count == 0;
    var _ := sectorIndirectionTable.Insert(0, (Some(LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)), []));
    assert IS.IIndirectionTable(sectorIndirectionTable) == BC.IndirectionTable(
      map[0 := LBAType.Location(LBAType.BlockSize(), b1.Length as uint64)],
      map[0 := []]
    );

    assume IS.WFSector(IS.SectorIndirectionTable(sectorIndirectionTable));
    var b0 := Marshalling.MarshallCheckedSector(IS.SectorIndirectionTable(sectorIndirectionTable));
    assume b0 != null;

    m := map[
      // Map ref 0 to lba 1
      0 := b0,
      // Put the root at lba 1
      LBAType.BlockSize() := b1
    ];

  }
}
