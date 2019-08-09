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
  import LBAType`Internal
  import ValueWithDefault`Internal
  import IS = ImplState

  type LBA = LBAType.LBA

  method InitDisk() returns (result: map<LBA, IS.Sector>)
  ensures forall k | k in result :: IS.WFSector(result[k])
  ensures forall l | l in result :: result[l].SectorBlock? ==> BT.WFNode(IS.INode(result[l].block))
  ensures forall l | l in result :: result[l].SectorBlock? ==> Marshalling.CappedNode(result[l].block)
  ensures 0 in result && result[0].SectorIndirectionTable?
  ensures LBAType.BlockSize() in result && result[LBAType.BlockSize()].SectorBlock?
  {
    var sectorIndirectionTable := new IS.MutIndirectionTable(1024); // TODO magic number
    var _ := sectorIndirectionTable.Insert(0, (Some(LBAType.BlockSize()), []));
    assert IS.IIndirectionTable(sectorIndirectionTable) == BC.IndirectionTable(map[0 := LBAType.BlockSize()], map[0 := []]);
    result := map[
      // Map ref 0 to lba 1
      0 := IS.SectorIndirectionTable(sectorIndirectionTable),
      // Put the root at lba 1
      LBAType.BlockSize() := IS.SectorBlock(IS.Node([], None, [KMTable.Empty()]))
    ];
    assume forall k | k in result :: IS.WFSector(result[k]);
  }

  // TODO spec out that the data returned by this function
  // satisfies the initial conditions
  // TODO prove that this always returns an answer (that is, marshalling always succeeds)
  method InitDiskBytes() returns (m :  map<LBA, array<byte>>)
  //ensures forall lba | lba in m :: ValidSector(m[lba][..])
  {
    var d := InitDisk();

    LBAType.reveal_ValidAddr();
    assert d[0].SectorIndirectionTable?;
    var b0 := Marshalling.MarshallCheckedSector(d[0]);
    if (b0 == null) { return map[]; }

    assert d[LBAType.BlockSize()].SectorBlock?;
    var b1 := Marshalling.MarshallCheckedSector(d[LBAType.BlockSize()]);
    if (b1 == null) { return map[]; }

    m := map[0 := b0, LBAType.BlockSize() := b1];
  }
}
