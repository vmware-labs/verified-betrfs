include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Base/Message.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../BlockCacheSystem/BetreeBlockCache.i.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/DataStructures/LruModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"
include "../lib/DataStructures/BitmapModel.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "IndirectionTableModel.i.dfy"
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
  import BC = BetreeGraphBlockCache
  import BBC = BetreeBlockCache
  import SD = AsyncSectorDisk
  import D = AsyncDisk
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import LruModel
  import BitmapModel
  import UI
  import MutableMapModel
  import BlockAllocatorModel
  import IndirectionTableModel

  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type DiskOp = BBC.DiskOp
  
  type IndirectionTable = IndirectionTableModel.IndirectionTable

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<Bucket>
    )
  datatype Constants = Constants()
  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable, // this lets us keep track of available LBAs
                                                         // TODO replace with something that only tracks LBAs
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<SD.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<SD.ReqId, BC.OutstandingRead>,
        syncReqs: MutableMapModel.LinearHashMap<BC.SyncReqStatus>,
        cache: map<Reference, Node>,
        lru: LruModel.LruQueue,
        blockAllocator: BlockAllocatorModel.BlockAllocatorModel
      )
    | Unready(outstandingIndirectionTableRead: Option<SD.ReqId>, syncReqs: MutableMapModel.LinearHashMap<BC.SyncReqStatus>)
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)

  predicate IsLocAllocIndirectionTable(indirectionTable: IndirectionTable, i: int)
  {
    IndirectionTableModel.IsLocAllocIndirectionTable(indirectionTable, i)
  }

  predicate IsLocAllocOutstanding(outstanding: map<SD.ReqId, BC.OutstandingWrite>, i: int)
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
      outstandingBlockWrites: map<SD.ReqId, BC.OutstandingWrite>,
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

  function TotalCacheSize(s: Variables) : int
  requires s.Ready?
  {
    |s.cache| + |s.outstandingBlockReads|
  }

  predicate WFVarsReady(s: Variables)
  requires s.Ready?
  {
    var Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, lru, locBitmap) := s;
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
  predicate WFVars(vars: Variables)
  {
    && (vars.Ready? ==> WFVarsReady(vars))
    && MutableMapModel.Inv(vars.syncReqs)
  }
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => (
        && IndirectionTableModel.Inv(indirectionTable)
        && BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
      )
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
  function IIndirectionTable(table: IndirectionTable) : (result: BC.IndirectionTable)
  {
    IndirectionTableModel.I(table)
  }
  function IIndirectionTableOpt(table: Option<IndirectionTable>) : (result: Option<BC.IndirectionTable>)
  {
    if table.Some? then
      Some(IIndirectionTable(table.value))
    else
      None
  }
  function IVars(vars: Variables) : BBC.Variables
  requires WFVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, lru, locBitmap) =>
        BC.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs.contents, ICache(cache))
      case Unready(outstandingIndirectionTableRead, syncReqs) => BC.Unready(outstandingIndirectionTableRead, syncReqs.contents)
    }
  }
  function ISector(sector: Sector) : BC.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorBlock(node) => BC.SectorBlock(INode(node))
      case SectorIndirectionTable(indirectionTable) => BC.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  function Ik(k: Constants) : BBC.Constants
  {
    BC.Constants()
  }

  function I(k: Constants, s: Variables) : BBC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && WFVars(s)
    && BBC.Inv(Ik(k), IVars(s))
  }

  // Functional model of the DiskIOHandler

  datatype IO =
    | IOInit(id: uint64)
    | IOReqRead(id: uint64, reqRead: D.ReqRead)
    | IOReqWrite(id: uint64, reqWrite: D.ReqWrite)
    | IORespRead(id: uint64, respRead: D.RespRead)
    | IORespWrite(id: uint64, respWrite: D.RespWrite)

  function diskOp(io: IO) : D.DiskOp {
    match io {
      case IOInit(id) => D.NoDiskOp
      case IOReqRead(id, reqRead) => D.ReqReadOp(id, reqRead)
      case IOReqWrite(id, reqWrite) => D.ReqWriteOp(id, reqWrite)
      case IORespRead(id, respRead) => D.RespReadOp(id, respRead)
      case IORespWrite(id, respWrite) => D.RespWriteOp(id, respWrite)
    }
  }
}
