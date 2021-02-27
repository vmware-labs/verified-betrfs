// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "IndirectionTable.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"
include "../lib/Base/Option.s.dfy"

module StateSectorModel {
  import opened Options

  import BT = PivotBetreeSpec`Internal
  import SectorType
  import BC = BlockCache
  import JC = JournalCache
  import IT = IndirectionTable

  type Node = BT.G.Node  
  type IndirectionTable = IT.IndirectionTable

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
        && indirectionTable.Inv()
        && BC.WFCompleteIndirectionTable(indirectionTable.I())
      )
      case SectorSuperblock(superblock) =>
        JC.WFSuperblock(superblock)
    }
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
      case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(indirectionTable.I())
      case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
    }
  }
}
