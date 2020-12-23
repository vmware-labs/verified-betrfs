// include "../PivotBetree/PivotBetreeSpec.i.dfy"
// include "../lib/Base/Message.i.dfy"
// include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
// include "../lib/Base/Option.s.dfy"
// include "../BlockCacheSystem/BetreeCache.i.dfy"
// include "../lib/Lang/NativeTypes.s.dfy"
// include "../lib/DataStructures/LruModel.i.dfy"
// include "../lib/DataStructures/MutableMapModel.i.dfy"
// include "../lib/DataStructures/BitmapModel.i.dfy"
// include "BlockAllocatorModel.i.dfy"
// include "IndirectionTableModel.i.dfy"
// include "CommitterModel.i.dfy"
// include "../BlockCacheSystem/BlockJournalDisk.i.dfy"
include "../BlockCacheSystem/BlockJournalCache.i.dfy"
// include "../ByteBlockCacheSystem/ByteCache.i.dfy"
// include "DiskOpModel.i.dfy"
include "CommitterImpl.i.dfy"
include "StateBCModel.i.dfy"
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
  // import opened Options
  // import opened Sequences
  // import opened NativeTypes

  // // import BT = PivotBetreeSpec`Internal
  // import Messages = ValueMessage
  // import MS = MapSpec
  // import Pivots = BoundedPivotsLib
  // // import BC = BlockCache
  // import JC = JournalCache
  // // import BBC = BetreeCache
  // // import BJD = BlockJournalDisk
  import BJC = BlockJournalCache

  // PREV import D = AsyncDisk
  // PREV import M = ByteCache
  // PREV import opened BucketsLib
  // PREV import opened BucketWeights
  // PREV import opened Bounds
  // PREV import LruModel
  // PREV import BitmapModel
  // PREV import UI
  // PREV import MutableMapModel
  // PREV import BlockAllocatorModel
  // PREV import IT = IndirectionTable
  // PREV import SectorType
  // PREV import DiskLayout
  // PREV import CommitterModel
  // PREV import opened DiskOpModel

  // PREV import ReferenceType`Internal

  // PREV type Node = BT.G.Node  
  // PREV type Reference = BT.G.Reference
  // PREV type DiskOp = BJD.DiskOp
  // PREV 
  // PREV type IndirectionTable = IT.IndirectionTable

  // PREV datatype BCVariables =
  // PREV   | Ready(
  // PREV       persistentIndirectionTable: IndirectionTable, // this lets us keep track of available LBAs
  // PREV                                                        // TODO replace with something that only tracks LBAs
  // PREV       frozenIndirectionTable: Option<IndirectionTable>,
  // PREV       ephemeralIndirectionTable: IndirectionTable,
  // PREV       persistentIndirectionTableLoc: DiskLayout.Location,
  // PREV       frozenIndirectionTableLoc: Option<DiskLayout.Location>,
  // PREV       outstandingIndirectionTableWrite: Option<BC.ReqId>,
  // PREV       outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
  // PREV       outstandingBlockReads: map<BC.ReqId, BC.OutstandingRead>,
  // PREV       cache: map<Reference, Node>,
  // PREV       lru: LruModel.LruQueue,
  // PREV       blockAllocator: BlockAllocatorModel.BlockAllocatorModel
  // PREV     )
  // PREV   | LoadingIndirectionTable(
  // PREV       indirectionTableLoc: DiskLayout.Location,
  // PREV       indirectionTableRead: Option<BC.ReqId>)
  // PREV   | Unready

  // PREV datatype Variables = Variables(
  // PREV   bc: BCVariables,
  // PREV   jc: CommitterModel.CM)

  // PREV datatype Sector =
  // PREV   | SectorNode(node: Node)
  // PREV   | SectorIndirectionTable(indirectionTable: IndirectionTable)
  // PREV   | SectorSuperblock(superblock: SectorType.Superblock)

  // PREV predicate IsLocAllocOutstanding(outstanding: map<BC.ReqId, BC.OutstandingWrite>, i: int)
  // PREV {
  // PREV   !(forall id | id in outstanding :: outstanding[id].loc.addr as int != i * NodeBlockSize() as int)
  // PREV }

  // PREV predicate {:opaque} ConsistentBitmap(
  // PREV     ephemeralIndirectionTable: SectorType.IndirectionTable,
  // PREV     frozenIndirectionTable: Option<SectorType.IndirectionTable>,
  // PREV     persistentIndirectionTable: SectorType.IndirectionTable,
  // PREV     outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
  // PREV     blockAllocator: BlockAllocatorModel.BlockAllocatorModel)
  // PREV {
  // PREV   && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(ephemeralIndirectionTable, i)
  // PREV     <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.ephemeral, i))
  // PREV   && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(persistentIndirectionTable, i)
  // PREV     <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.persistent, i))
  // PREV   && (frozenIndirectionTable.Some? <==> blockAllocator.frozen.Some?)
  // PREV   && (frozenIndirectionTable.Some? ==>
  // PREV     (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(frozenIndirectionTable.value, i)
  // PREV       <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.frozen.value, i)))
  // PREV   && (forall i: int :: IsLocAllocOutstanding(outstandingBlockWrites, i)
  // PREV     <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.outstanding, i))
  // PREV }

  // PREV predicate WFNode(node: Node)
  // PREV {
  // PREV   BT.WFNode(node)
  // PREV }

  // PREV predicate WFCache(cache: map<Reference, Node>)
  // PREV {
  // PREV   forall ref | ref in cache :: WFNode(cache[ref])
  // PREV }

  // PREV function TotalCacheSize(s: BCVariables) : int
  // PREV requires s.Ready?
  // PREV {
  // PREV   |s.cache| + |s.outstandingBlockReads|
  // PREV }

  // PREV predicate WFVarsReady(s: BCVariables)
  // PREV requires s.Ready?
  // PREV {
  // PREV   var Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, cache, lru, locBitmap) := s;
  // PREV   && WFCache(cache)
  // PREV   && LruModel.WF(lru)
  // PREV   && LruModel.I(lru) == cache.Keys
  // PREV   && TotalCacheSize(s) <= MaxCacheSize()
  // PREV   && ephemeralIndirectionTable.Inv()
  // PREV   && ephemeralIndirectionTable.TrackingGarbage()
  // PREV   && persistentIndirectionTable.Inv()
  // PREV   && (frozenIndirectionTable.Some? ==> frozenIndirectionTable.value.Inv())
  // PREV   && BlockAllocatorModel.Inv(s.blockAllocator)
  // PREV   && ConsistentBitmap(s.ephemeralIndirectionTable.I(), MapOption(s.frozenIndirectionTable, (x: IndirectionTable) => x.I()),
  // PREV       s.persistentIndirectionTable.I(), s.outstandingBlockWrites, s.blockAllocator)
  // PREV }
  // PREV predicate WFBCVars(vars: BCVariables)
  // PREV {
  // PREV   && (vars.Ready? ==> WFVarsReady(vars))
  // PREV }
  // PREV predicate WFSector(sector: Sector)
  // PREV {
  // PREV   match sector {
  // PREV     case SectorNode(node) => WFNode(node)
  // PREV     case SectorIndirectionTable(indirectionTable) => (
  // PREV       && indirectionTable.Inv()
  // PREV       && BC.WFCompleteIndirectionTable(indirectionTable.I())
  // PREV     )
  // PREV     case SectorSuperblock(superblock) =>
  // PREV       JC.WFSuperblock(superblock)
  // PREV   }
  // PREV }

  // PREV function INode(node: Node) : (result: BT.G.Node)
  // PREV {
  // PREV   BT.G.Node(node.pivotTable, node.children, node.buckets)
  // PREV }
  // PREV function ICache(cache: map<Reference, Node>): map<Reference, BT.G.Node>
  // PREV requires WFCache(cache)
  // PREV {
  // PREV   map ref | ref in cache :: INode(cache[ref])
  // PREV }
  // PREV function IIndirectionTableOpt(table: Option<IndirectionTable>) : (result: Option<SectorType.IndirectionTable>)
  // PREV {
  // PREV   if table.Some? then
  // PREV     Some(table.value.I())
  // PREV   else
  // PREV     None
  // PREV }
  // PREV function IBlockCache(vars: BCVariables) : BBC.Variables
  // PREV requires WFBCVars(vars)
  // PREV {
  // PREV   match vars {
  // PREV     case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, cache, lru, locBitmap) =>
  // PREV       BC.Ready(persistentIndirectionTable.I(), IIndirectionTableOpt(frozenIndirectionTable), ephemeralIndirectionTable.I(),  persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, ICache(cache))
  // PREV     case LoadingIndirectionTable(loc, read) =>
  // PREV       BC.LoadingIndirectionTable(loc, read)
  // PREV     case Unready => BC.Unready
  // PREV   }
  // PREV }
  // PREV function ISector(sector: Sector) : SectorType.Sector
  // PREV requires WFSector(sector)
  // PREV {
  // PREV   match sector {
  // PREV     case SectorNode(node) => SectorType.SectorNode(INode(node))
  // PREV     case SectorIndirectionTable(indirectionTable) => SectorType.SectorIndirectionTable(indirectionTable.I())
  // PREV     case SectorSuperblock(superblock) => SectorType.SectorSuperblock(superblock)
  // PREV   }
  // PREV }

  // import D = AsyncDisk
  // import M = ByteCache
  // import opened BucketsLib
  // import opened BucketWeights
  // import opened Bounds
  // // import LruModel
  // // import BitmapModel
  // import UI
  // import MutableMapModel
  // // import BlockAllocatorModel
  // // import IndirectionTableModel
  // import SectorType
  // // import DiskLayout
  // import CommitterModel
  // import opened DiskOpModel

  // import ReferenceType`Internal

  import opened CommitterImpl
  import opened StateBCModel

  // type Node = BT.G.Node  
  // type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Variables = Variables(
    bc: BCVariables,
    jc: Committer)

  predicate WFVars(s: Variables)
  {
    && WFBCVars(s.bc)
    && s.jc.WF()
  }

  function IVars(vars: Variables) : BJC.Variables
  requires WFVars(vars)
  {
    BJC.Variables(IBlockCache(vars.bc), vars.jc.I())
  }

  function I(s: Variables) : BJC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate Inv(s: Variables)
  {
    && WFVars(s)
    && BCInv(s.bc)
    && s.jc.Inv()
    && BJC.Inv(I(s))
  }
}
