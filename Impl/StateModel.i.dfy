include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../BlockCacheSystem/BetreeCache.i.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/DataStructures/LruModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"
include "../lib/DataStructures/BitmapModel.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "IndirectionTableModel.i.dfy"
include "CommitterModel.i.dfy"
include "../BlockCacheSystem/BlockJournalDisk.i.dfy"
include "../BlockCacheSystem/BlockJournalCache.i.dfy"
include "../ByteBlockCacheSystem/ByteCache.i.dfy"
include "DiskOpModel.i.dfy"
//
// This file represents immutability's last stand.
// It is the highest-fidelity representation of the implementation
// that can be represented with immutable datatypes.
//
// For example, it has a model of the root bucket which does not exist in
// BlockCache.  It also represents indirection table as a map to pairs, rather
// than two maps, because real, mutable implementation uses a map to pairs.
//

module StateModel {
  import opened Options
  import opened Sequences
  import opened NativeTypes

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BlockCache
  import JC = JournalCache
  import BBC = BetreeCache
  import BJD = BlockJournalDisk
  import BJC = BlockJournalCache
  import D = AsyncDisk
  import M = ByteCache
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import LruModel
  import BitmapModel
  import UI
  import MutableMapModel
  import BlockAllocatorModel
  import IndirectionTableModel
  import SectorType
  import DiskLayout
  import CommitterModel
  import opened DiskOpModel

  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type DiskOp = BJD.DiskOp
  
  type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<Bucket>
    )
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

  datatype Variables = Variables(
    bc: BCVariables,
    jc: CommitterModel.CM)

  datatype Sector =
    | SectorNode(node: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)
    | SectorSuperblock(superblock: SectorType.Superblock)

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

  predicate WFNode(node: Node)
  {
    && WFBucketList(node.buckets, node.pivotTable)
    && (node.children.Some? ==> |node.buckets| == |node.children.value|)
    && |node.buckets| <= MaxNumChildren()
    && WeightBucketList(node.buckets) <= MaxTotalBucketWeight()
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

  function INode(node: Node) : (result: BT.G.Node)
  {
    BT.G.Node(node.pivotTable, node.children, node.buckets)
  }
  function ICache(cache: map<Reference, Node>): map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INode(cache[ref])
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
  function ISector(sector: Sector) : SectorType.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorNode(node) => SectorType.SectorNode(INode(node))
      case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(IIndirectionTable(indirectionTable))
      case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
    }
  }

  predicate WFVars(s: Variables)
  {
    && WFBCVars(s.bc)
    && CommitterModel.WF(s.jc)
  }

  function IVars(vars: Variables) : BJC.Variables
  requires WFVars(vars)
  {
    BJC.Variables(IBlockCache(vars.bc), CommitterModel.I(vars.jc))
  }

  function I(k: Constants, s: Variables) : BJC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate BCInv(k: Constants, s: BCVariables)
  {
    && WFBCVars(s)
    && BBC.Inv(Ik(k).bc, IBlockCache(s))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && WFVars(s)
    && BCInv(k, s.bc)
    && CommitterModel.Inv(s.jc)
    && BJC.Inv(Ik(k), I(k, s))
  }
}
