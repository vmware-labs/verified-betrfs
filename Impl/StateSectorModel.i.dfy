include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "IndirectionTableModel.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"

module StateSectorModel {
  import BT = PivotBetreeSpec`Internal
  import IndirectionTableModel
  import SectorType
  import BC = BlockCache
  import JC = JournalCache

  type Node = BT.G.Node  
  type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Sector =
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)
    | SectorSuperblock(superblock: SectorType.Superblock)

  predicate WFNode(node: Node)
  {
    BT.WFNode(node)
  }
  
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorNode(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => (
        && IndirectionTableModel.Inv(indirectionTable)
        && BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
      )
      case SectorSuperblock(superblock) =>
        JC.WFSuperblock(superblock)
    }
  }

  function IIndirectionTable(table: IndirectionTable) : (result: SectorType.IndirectionTable)
  {
    IndirectionTableModel.I(table)
  }
}