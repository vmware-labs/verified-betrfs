include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "IndirectionTableModel.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"
include "../BlockCacheSystem/JournalCache.i.dfy"

module StateSectorModel {
  import BT = PivotBetreeSpec`Internal
  import IndirectionTableModel
  import SectorType
  import BC = BlockCache
  import JC = JournalCache

  type Node = BT.G.Node  

  datatype Sector =
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTableModel.IndirectionTable)
    | SectorSuperblock(superblock: SectorType.Superblock)

  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorNode(node) => BT.WFNode(node)
      case SectorIndirectionTable(indirectionTable) => (
        && IndirectionTableModel.Inv(indirectionTable)
        && BC.WFCompleteIndirectionTable(IndirectionTableModel.I(indirectionTable))
      )
      case SectorSuperblock(superblock) =>
        JC.WFSuperblock(superblock)
    }
  }

  function ISector(sector: Sector) : SectorType.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorNode(node) => SectorType.SectorNode(BT.G.Node(node.pivotTable, node.children, node.buckets))
      case SectorIndirectionTable(indirectionTable) =>
        SectorType.SectorIndirectionTable(IndirectionTableModel.I(indirectionTable))
      case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
    }
  }
}