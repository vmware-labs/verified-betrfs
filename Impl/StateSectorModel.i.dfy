include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "IndirectionTableModel.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"

module StateSectorModel {
  import BT = PivotBetreeSpec`Internal
  import IndirectionTableModel
  import SectorType

  type Node = BT.G.Node  
  type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Sector =
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)
    | SectorSuperblock(superblock: SectorType.Superblock)
}