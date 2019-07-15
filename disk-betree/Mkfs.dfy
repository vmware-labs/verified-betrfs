include "Marshalling.dfy"
include "Impl.dfy"

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

  function method InitDisk() : map<LBA, BC.Sector> {
    map[
      // Map ref 0 to lba 1
      0 := BC.SectorSuperblock(BC.Superblock(map[0 := 1], map[0 := []])),
      // Put the root at lba 1
      1 := BC.SectorBlock(BT.G.Node([], None, [map[]]))
    ]
  }

  // TODO spec out that the data returned by this function
  // satisfies the initial conditions
  // TODO prove that this always returns an answer (that is, marshalling always succeeds)
  method InitDiskBytes() returns (m :  map<LBA, array<byte>>)
  ensures forall lba | lba in m :: ValidSector(m[lba][..])
  {
    var d := InitDisk();

    var b0 := Marshalling.MarshallSector(d[0]);
    if (b0 == null) { return map[]; }

    var b1 := Marshalling.MarshallSector(d[1]);
    if (b1 == null) { return map[]; }

    return map[0 := b0, 1 := b1];
  }
}
