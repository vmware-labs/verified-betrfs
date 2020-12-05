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
}