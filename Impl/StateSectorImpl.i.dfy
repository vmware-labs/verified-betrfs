// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "NodeImpl.i.dfy"
include "IndirectionTable.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"

module StateSectorImpl {
  import opened Options
  import opened NodeImpl
  import IT = IndirectionTable
  import JC = JournalCache
  import BC = BlockCache

  import SectorType

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
    && (sector.SectorNode? ==> sector.node.Inv())
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock))
  }

  predicate Inv(sector: Sector)
  {
    && WFSector(sector)
    && (sector.SectorNode? ==> BT.WFNode(sector.node.I()))
    && (sector.SectorIndirectionTable? ==> BC.WFCompleteIndirectionTable(sector.indirectionTable.I()))
    && (sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock))
  }

  function ISector(sector: Sector) : SectorType.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorNode(node) => SectorType.SectorNode(node.I())
      case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
      case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(indirectionTable.I())
    }
  }
}
