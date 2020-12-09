include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "IndirectionTableModel.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"
include "../lib/Base/Option.s.dfy"

module StateSectorModel {
  import opened Options

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

  function IIndirectionTableOpt(table: Option<IndirectionTable>) : (result: Option<SectorType.IndirectionTable>)
  {
    if table.Some? then
      Some(IIndirectionTable(table.value))
    else
      None
  }

  function INode(node: Node) : (result: BT.G.Node)
  {
    BT.G.Node(node.pivotTable, node.children, node.buckets)
  }

  function ISector(sector: Sector) : SectorType.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorNode(node) => SectorType.SectorNode(INode(node))
      case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(IIndirectionTable(indirectionTable))
      case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
    }
  }
}