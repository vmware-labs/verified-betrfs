include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../BlockCacheSystem/BetreeCache.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/DataStructures/LruModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"
include "../lib/DataStructures/BitmapModel.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "IndirectionTable.i.dfy"
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
  import Pivots = BoundedPivotsLib
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
  import IT = IndirectionTable
  import SectorType
  import DiskLayout
  import CommitterModel
  import opened DiskOpModel

  import ReferenceType`Internal

  type Node = BT.G.Node  
  type Reference = BT.G.Reference
  type DiskOp = BJD.DiskOp
  
  type IndirectionTable = IT.IndirectionTable

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

  predicate WFNode(node: Node)
  {
    BT.WFNode(node)
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
  function ICache(cache: map<Reference, Node>): map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INode(cache[ref])
  }
  function IIndirectionTableOpt(table: Option<IndirectionTable>) : (result: Option<SectorType.IndirectionTable>)
  {
    if table.Some? then
      Some(table.value.I())
    else
      None
  }
  function IBlockCache(vars: BCVariables) : BBC.Variables
  requires WFBCVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, cache, lru, locBitmap) =>
        BC.Ready(persistentIndirectionTable.I(), IIndirectionTableOpt(frozenIndirectionTable), ephemeralIndirectionTable.I(),  persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, ICache(cache))
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
      case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(indirectionTable.I())
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

  function I(s: Variables) : BJC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate BCInv(s: BCVariables)
  {
    && WFBCVars(s)
    && BBC.Inv(IBlockCache(s))
  }

  predicate Inv(s: Variables)
  {
    && WFVars(s)
    && BCInv(s.bc)
    && CommitterModel.Inv(s.jc)
    && BJC.Inv(I(s))
  }
}
