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
        BC.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable),  persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, ICache(cache))
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

  predicate IsLocAllocIndirectionTable(indirectionTable: IndirectionTable, i: int)
  {
    IndirectionTableModel.IsLocAllocIndirectionTable(indirectionTable, i)
  }

  predicate IsLocAllocOutstanding(outstanding: map<BC.ReqId, BC.OutstandingWrite>, i: int)
  {
    !(forall id | id in outstanding :: outstanding[id].loc.addr as int != i * NodeBlockSize() as int)
  }

  predicate IsLocAllocBitmap(bm: BitmapModel.BitmapModelT, i: int)
  {
    IndirectionTableModel.IsLocAllocBitmap(bm, i)
  }

  predicate {:opaque} ConsistentBitmap(
      ephemeralIndirectionTable: IndirectionTable,
      frozenIndirectionTable: Option<IndirectionTable>,
      persistentIndirectionTable: IndirectionTable,
      outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
      blockAllocator: BlockAllocatorModel.BlockAllocatorModel)
  {
    && (forall i: int :: IsLocAllocIndirectionTable(ephemeralIndirectionTable, i)
      <==> IsLocAllocBitmap(blockAllocator.ephemeral, i))
    && (forall i: int :: IsLocAllocIndirectionTable(persistentIndirectionTable, i)
      <==> IsLocAllocBitmap(blockAllocator.persistent, i))
    && (frozenIndirectionTable.Some? <==> blockAllocator.frozen.Some?)
    && (frozenIndirectionTable.Some? ==>
      (forall i: int :: IsLocAllocIndirectionTable(frozenIndirectionTable.value, i)
        <==> IsLocAllocBitmap(blockAllocator.frozen.value, i)))
    && (forall i: int :: IsLocAllocOutstanding(outstandingBlockWrites, i)
      <==> IsLocAllocBitmap(blockAllocator.outstanding, i))
  }

  predicate WFVarsReady(s: BCVariables)
  requires s.Ready?
  {
    var Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, cache, lru, locBitmap) := s;
    && WFCache(cache)
    && LruModel.WF(lru)
    && LruModel.I(lru) == cache.Keys
    && TotalCacheSize(s) <= MaxCacheSize()
    && IndirectionTableModel.Inv(ephemeralIndirectionTable)
    && IndirectionTableModel.TrackingGarbage(ephemeralIndirectionTable)
    && IndirectionTableModel.Inv(persistentIndirectionTable)
    && (frozenIndirectionTable.Some? ==> IndirectionTableModel.Inv(frozenIndirectionTable.value))
    && BlockAllocatorModel.Inv(s.blockAllocator)
    && ConsistentBitmap(s.ephemeralIndirectionTable, s.frozenIndirectionTable,
        s.persistentIndirectionTable, s.outstandingBlockWrites, s.blockAllocator)
  }

  predicate WFBCVars(vars: BCVariables)
  {
    && (vars.Ready? ==> WFVarsReady(vars))
  }
}