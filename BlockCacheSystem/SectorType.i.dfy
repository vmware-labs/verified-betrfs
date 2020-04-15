include "JournalRange.i.dfy"
include "DiskLayout.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

module SectorType {
  import opened NativeTypes
  import opened Journal
  import opened JournalRanges
  import opened DiskLayout
  import opened PivotBetreeGraph

  datatype Superblock = Superblock(
      counter: uint64,
      journalStart: uint64,
      journalLen: uint64,
      indirectionTableLoc: Location)

  // TODO make indirectionTable take up more than one block
  datatype IndirectionTable = IndirectionTable(
      locs: map<Reference, Location>,
      graph: map<Reference, seq<Reference>>)

  datatype Sector =
    | SectorSuperblock(superblock: Superblock)
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)
}
