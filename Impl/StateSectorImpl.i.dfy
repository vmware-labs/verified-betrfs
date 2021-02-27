// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "NodeImpl.i.dfy"
include "IndirectionTable.i.dfy"
include "StateSectorModel.i.dfy"

module StateSectorImpl {
  import opened Options
  import opened NodeImpl
  import IT = IndirectionTable
  import JC = JournalCache

  import SectorType
  import SSM = StateSectorModel

  // type MutIndirectionTableNullable = IndirectionTable.BoxedIndirectionTable?

  linear datatype Sector =
    | SectorNode(linear node: Node)
    | SectorSuperblock(superblock: SectorType.Superblock)
    | SectorIndirectionTable(linear indirectionTable: IT.IndirectionTable)
  {
    linear method Free()
    requires this.SectorNode? ==> node.Inv()
    {
      linear match this {
        case SectorNode(node) => {
          var _ := FreeNode(node);
        }
        case SectorSuperblock(_) => {}
        case SectorIndirectionTable(indirectionTable) => {
          indirectionTable.Free();
        }
      }
    }
  }

  predicate WFSector(sector: Sector)
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorNode? ==> sector.node.Inv())
    && (sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock))
  }

  function ISector(sector: Sector) : SSM.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorSuperblock(superblock) => SSM.SectorSuperblock(superblock)
      case SectorNode(node) => SSM.SectorNode(node.I())
      case SectorIndirectionTable(indirectionTable) => SSM.SectorIndirectionTable(indirectionTable)
    }
  }
}
