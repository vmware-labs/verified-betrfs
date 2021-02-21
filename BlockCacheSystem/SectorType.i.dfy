include "JournalRange.i.dfy"
include "DiskLayout.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

module SectorType {
  import opened NativeTypes
  import opened Journal
  import opened JournalRanges
  import opened DiskLayout
  import opened PivotBetreeGraph
  import opened Bounds

  import opened ReferenceType`Internal

  datatype Superblock = Superblock(
      counter: uint64,
      journalStart: uint64,
      journalLen: uint64,
      indirectionTableLoc: Location)

  // TODO make indirectionTable take up more than one block
  datatype IndirectionTable = IndirectionTable(
    locs: map<ReferenceType.Reference, Location>,
    graph: map<ReferenceType.Reference, seq<ReferenceType.Reference>>,
    refUpperBound: uint64)
  {
    predicate hasEmptyLoc(ref: ReferenceType.Reference)
    {
      && ref in graph
      && ref !in locs
    }

    predicate IsLocAllocIndirectionTable(i: int)
    {
      // Can't use the lower values, so they're always marked "allocated"
      || 0 <= i < MinNodeBlockIndex()
      || (!(
        forall ref | ref in locs ::
          locs[ref].addr as int != i * NodeBlockSize() as int
      ))
    }
  }

  // predicate test(indirectionTable: IndirectionTable)
  // {
  //   && (forall ref | ref in indirectionTable.graph :: ref <= indirectionTable.refUpperBound)
  // }

  datatype Sector =
    | SectorSuperblock(superblock: Superblock)
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)
}
