include "NodeImpl.i.dfy"
include "IndirectionTable.i.dfy"
include "StateSectorModel.i.dfy"

module StateSectorImpl {
  import opened Options
  import opened NodeImpl
  import IndirectionTable
  import JC = JournalCache

  import SectorType
  import SSM = StateSectorModel

  type MutIndirectionTable = IndirectionTable.BoxedIndirectionTable
  type MutIndirectionTableNullable = IndirectionTable.BoxedIndirectionTable?

  linear datatype Sector =
    | SectorNode(linear node: Node)
    | SectorSuperblock(superblock: SectorType.Superblock)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)
  {
    linear method Free()
    requires this.SectorNode? ==> node.Inv()
    {
      linear match this {
        case SectorNode(node) => {
          var _ := FreeNode(node);
        }
        case SectorSuperblock(_) => {}
        case SectorIndirectionTable(_) => {}
      }
    }
  }

  function SectorObjectSet(sector: Sector) : set<object>
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable}
      case SectorNode(block) => {}
      case SectorSuperblock(superblock) => {}
    }
  }

  function SectorRepr(sector: Sector) : set<object>
  reads SectorObjectSet(sector)
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable} + indirectionTable.Repr
      case SectorNode(block) => {}
      case SectorSuperblock(superblock) => {}
    }
  }
 
  predicate WFSector(sector: Sector)
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorNode? ==> sector.node.Inv())
    && (sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock))
  }

  function ISector(sector: Sector) : SSM.Sector
  requires WFSector(sector)
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    match sector {
      case SectorSuperblock(superblock) => SSM.SectorSuperblock(superblock)
      case SectorNode(node) => SSM.SectorNode(node.I())
      case SectorIndirectionTable(indirectionTable) => SSM.SectorIndirectionTable(indirectionTable.ReadWithInv())
    }
  }
}
