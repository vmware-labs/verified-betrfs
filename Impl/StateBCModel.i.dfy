// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "StateSectorModel.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "../BlockCacheSystem/BlockJournalDisk.i.dfy"
include "../BlockCacheSystem/BetreeCache.i.dfy"
include "../lib/DataStructures/LruModel.i.dfy"

module StateBCModel {
  import DiskLayout
  import BitmapModel
  import BlockAllocatorModel

  import BC = BlockCache
  import BBC = BetreeCache
  import LruModel
  import BT = PivotBetreeSpec`Internal
  import BJD = BlockJournalDisk

  import opened Options
  import opened Bounds
  import opened StateSectorModel

  import Pivots = BoundedPivotsLib
  import Messages = ValueMessage`Internal

  type Reference = BT.G.Reference
  type DiskOp = BJD.DiskOp

  datatype BCVariables =
    | Ready(
        persistentIndirectionTable: IndirectionTable, // this lets us keep track of available LBAs
                                                         // TODO replace with something that only tracks LBAs
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,
        persistentIndirectionTableLoc: DiskLayout.Location,
        frozenIndirectionTableLoc: Option<DiskLayout.Location>,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<BC.ReqId, BC.OutstandingRead>,
        cache: map<Reference, Node>,
        lru: LruModel.LruQueue,
        blockAllocator: BlockAllocatorModel.BlockAllocatorModel
      )
    | LoadingIndirectionTable(
        indirectionTableLoc: DiskLayout.Location,
        indirectionTableRead: Option<BC.ReqId>)
    | Unready

  function ICache(cache: map<Reference, Node>): map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INode(cache[ref])
  }

  function IBlockCache(vars: BCVariables) : BBC.Variables
  requires WFBCVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, cache, lru, locBitmap) =>
        BC.Ready(persistentIndirectionTable.I(), MapOption(frozenIndirectionTable, (x: IndirectionTable) => x.I()), ephemeralIndirectionTable.I(),  persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, ICache(cache))
      case LoadingIndirectionTable(loc, read) =>
        BC.LoadingIndirectionTable(loc, read)
      case Unready => BC.Unready
    }
  }

  predicate BCInv(s: BCVariables)
  {
    && WFBCVars(s)
    && BBC.Inv(IBlockCache(s))
  }

  predicate WFCache(cache: map<Reference, Node>)
  {
    forall ref | ref in cache :: WFNode(cache[ref])
  }

  function TotalCacheSize(s: BCVariables) : int
  requires s.Ready?
  {
    |s.cache| + |s.outstandingBlockReads|
  }

  predicate IsLocAllocOutstanding(outstanding: map<BC.ReqId, BC.OutstandingWrite>, i: int)
  {
    !(forall id | id in outstanding :: outstanding[id].loc.addr as int != i * NodeBlockSize() as int)
  }

  predicate {:opaque} ConsistentBitmap(
      ephemeralIndirectionTable: SectorType.IndirectionTable,
      frozenIndirectionTable: Option<SectorType.IndirectionTable>,
      persistentIndirectionTable: SectorType.IndirectionTable,
      outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
      blockAllocator: BlockAllocatorModel.BlockAllocatorModel)
  {
    && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(ephemeralIndirectionTable, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.ephemeral, i))
    && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(persistentIndirectionTable, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.persistent, i))
    && (frozenIndirectionTable.Some? <==> blockAllocator.frozen.Some?)
    && (frozenIndirectionTable.Some? ==>
      (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(frozenIndirectionTable.value, i)
        <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.frozen.value, i)))
    && (forall i: int :: IsLocAllocOutstanding(outstandingBlockWrites, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.outstanding, i))
  }

  predicate WFVarsReady(s: BCVariables)
  requires s.Ready?
  {
    var Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, outstandingBlockWrites, _, cache, lru, locBitmap) := s;
    && WFCache(cache)
    && LruModel.WF(lru)
    && LruModel.I(lru) == cache.Keys
    && TotalCacheSize(s) <= MaxCacheSize()
    && ephemeralIndirectionTable.Inv()
    && ephemeralIndirectionTable.TrackingGarbage()
    && persistentIndirectionTable.Inv()
    && (frozenIndirectionTable.Some? ==> frozenIndirectionTable.value.Inv())
    && BlockAllocatorModel.Inv(s.blockAllocator)
    && ConsistentBitmap(s.ephemeralIndirectionTable.I(), MapOption(s.frozenIndirectionTable, (x: IndirectionTable) => x.I()),
        s.persistentIndirectionTable.I(), s.outstandingBlockWrites, s.blockAllocator)
  }

  predicate WFBCVars(vars: BCVariables)
  {
    && (vars.Ready? ==> WFVarsReady(vars))
  }
}
