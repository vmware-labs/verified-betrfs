// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "StateSectorImpl.i.dfy"
include "MarshallingImpl.i.dfy"
include "MkfsModel.i.dfy"

module MkfsImpl {
  import MarshallingImpl
  import IMM = MarshallingModel
  import opened Options
  import opened NativeTypes
  import opened BucketWeights
  import SSM = StateSectorModel
  import opened BucketImpl
  import opened NodeImpl
  import opened BoundedPivotsLib
  import Marshalling
  import MkfsModel
  import opened LinearSequence_s
  import opened LinearSequence_i

  import BT = PivotBetreeSpec
  import BC = BlockCache
  import opened SectorType
  import ReferenceType`Internal
  import opened DiskLayout
  import opened Bounds
  import ValueType`Internal
  import SSI = StateSectorImpl
  import D = AsyncDisk
  import IT = IndirectionTable

  import ADM = ByteSystem

  method Mkfs() returns (diskContents :  map<Addr, seq<byte>>)
  ensures MkfsModel.InitDiskContents(diskContents)
  ensures ADM.BlocksDontIntersect(diskContents)
  {
    var s1addr := Superblock1Location().addr;
    var s2addr := Superblock2Location().addr;
    var indirectionTableAddr := IndirectionTable1Addr();
    var nodeAddr := NodeBlockSizeUint64() * MinNodeBlockIndexUint64();

    linear var node := Node.EmptyNode();
    ghost var i:SSM.Sector := SSI.ISector(SSI.SectorNode(node));
    assert SSM.WFNode(i.node) by {
      reveal_WeightBucketList();
    }

    linear var sector := SSI.SectorNode(node);
    var bNode_array := MarshallingImpl.MarshallCheckedSector(sector);

    var bNode := bNode_array[..];
    sector.Free();

    var nodeLoc := Location(nodeAddr, |bNode| as uint64);
    assert ValidNodeLocation(nodeLoc) by {
        ValidNodeAddrMul(MinNodeBlockIndexUint64());
      }

    linear var sectorIndirectionTable := IT.IndirectionTable.Alloc(nodeLoc);

    assert sectorIndirectionTable.I() == IndirectionTable(
      map[0 := nodeLoc],
      map[0 := []]
    );

    assert BC.WFCompleteIndirectionTable(sectorIndirectionTable.I());
    assert SSM.WFSector(SSI.ISector(SSI.SectorIndirectionTable(sectorIndirectionTable)));

    linear var sectorIndirect := SSI.SectorIndirectionTable(sectorIndirectionTable);
    var bIndirectionTable_array := MarshallingImpl.MarshallCheckedSector(sectorIndirect);
    assert bIndirectionTable_array != null;
    var bIndirectionTable := bIndirectionTable_array[..];
    sectorIndirect.Free();

    var indirectionTableLoc := Location(indirectionTableAddr, |bIndirectionTable| as uint64);
    assert ValidIndirectionTableLocation(indirectionTableLoc);

    linear var sectorSuperblock := SSI.SectorSuperblock(Superblock(0, 0, 0, indirectionTableLoc));
    var bSuperblock_array := MarshallingImpl.MarshallCheckedSector(sectorSuperblock);
    var bSuperblock := bSuperblock_array[..];
    sectorSuperblock.Free();

    ghost var ghosty := true;
    if ghosty {
      if overlap(Superblock1Location(), nodeLoc) {
        overlappingLocsSameType(Superblock1Location(), nodeLoc);
      }
      if overlap(Superblock2Location(), nodeLoc) {
        overlappingLocsSameType(Superblock2Location(), nodeLoc);
      }
      if overlap(indirectionTableLoc, nodeLoc) {
        overlappingLocsSameType(indirectionTableLoc, nodeLoc);
      }
    }

    diskContents := map[
      // Map ref 0 to lba 1
      s1addr := bSuperblock,
      s2addr := bSuperblock,
      indirectionTableAddr := bIndirectionTable,
      nodeAddr := bNode
    ];
  }
}
