include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "../lib/DataStructures/LruImpl.i.dfy"
include "StateModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "BucketImpl.i.dfy"
include "ImplNodes.i.dfy"
include "IndirectionTableImpl.i.dfy"
include "BlockAllocatorImpl.i.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import TTT = TwoThreeTree
  import SM = StateModel
  import opened ImplNode
  import opened ImplMutCache
  import BlockAllocatorImpl
  import BitmapImpl
  import IndirectionTableImpl
  import IndirectionTableModel
  import MutableMap
  import MutableMapModel

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import D = AsyncSectorDisk
  import MainDiskIOHandler
  import LruModel
  import LruImpl
  import MutableBucket
  import opened Bounds
  import opened BucketsLib

  import MM = MutableMap
  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type TreeMap = TTT.Tree<Message>

  type MutIndirectionTable = IndirectionTableImpl.IndirectionTable
  type MutIndirectionTableNullable = IndirectionTableImpl.IndirectionTable?

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)

  function SectorObjectSet(sector: Sector) : set<object>
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable}
      case SectorBlock(block) => {block}
    }
  }

  function SectorRepr(sector: Sector) : set<object>
  reads if sector.SectorIndirectionTable? then {sector.indirectionTable} else {sector.block}
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable} + indirectionTable.Repr
      case SectorBlock(block) => block.Repr
    }
  }
 
  predicate WFSector(sector: Sector)
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorBlock? ==> sector.block.Inv())
  }

  // TODO remove this and just replace with .I() because it's easier
  function IIndirectionTable(table: MutIndirectionTable) : (result: IndirectionTableModel.IndirectionTable)
  reads table, table.Repr
  requires table.Inv()
  {
    table.I()
  }
 
  function IIndirectionTableOpt(table: MutIndirectionTableNullable) : (result: Option<SM.IndirectionTable>)
  reads if table != null then {table} + table.Repr else {}
  requires table != null ==> table.Inv()
  {
    if table != null then
      Some(IIndirectionTable(table))
    else
      None
  }
 
  function ISector(sector: Sector) : SM.Sector
  requires WFSector(sector)
  reads if sector.SectorIndirectionTable? then {sector.indirectionTable} else {sector.block}
  reads SectorRepr(sector)
  {
    match sector {
      case SectorBlock(node) => SM.SectorBlock(node.I())
      case SectorIndirectionTable(indirectionTable) => SM.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  class Variables {
    var ready: bool;

    var syncReqs: MutableMap.ResizingHashMap<BC.SyncReqStatus>

    // Ready
    var persistentIndirectionTable: MutIndirectionTable;
    var frozenIndirectionTable: MutIndirectionTableNullable;
    var ephemeralIndirectionTable: MutIndirectionTable;
    var outstandingIndirectionTableWrite: Option<BC.ReqId>;
    var outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>;
    var outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>;
    var cache: MutCache;
    var lru: LruImpl.LruImplQueue;
    var blockAllocator: BlockAllocatorImpl.BlockAllocator;

    // Unready
    var outstandingIndirectionTableRead: Option<D.ReqId>;

    function Repr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator, syncReqs
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr +
      cache.Repr +
      blockAllocator.Repr +
      syncReqs.Repr
    }

    predicate ReprInv()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator, syncReqs
    reads Repr()
    {
        // NOALIAS statically enforced no-aliasing would probably help here
        && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr !! lru.Repr !! cache.Repr !! blockAllocator.Repr !! syncReqs.Repr
        && (frozenIndirectionTable != null ==>
            && frozenIndirectionTable.Repr !! persistentIndirectionTable.Repr
            && frozenIndirectionTable.Repr !! ephemeralIndirectionTable.Repr
            && frozenIndirectionTable.Repr !! lru.Repr
            && frozenIndirectionTable.Repr !! cache.Repr
            && frozenIndirectionTable.Repr !! blockAllocator.Repr
            && frozenIndirectionTable.Repr !! syncReqs.Repr
        )

        && this !in ephemeralIndirectionTable.Repr
        && this !in persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> this !in frozenIndirectionTable.Repr)
        && this !in lru.Repr
        && this !in cache.Repr
        && this !in blockAllocator.Repr
        && this !in syncReqs.Repr
    }

    predicate W()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator, syncReqs
    reads Repr()
    {
      && ReprInv()
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable != null ==> frozenIndirectionTable.Inv())
      && ephemeralIndirectionTable.Inv()
      && lru.Inv()
      && cache.Inv()
      && blockAllocator.Inv()
      && syncReqs.Inv()
    }

    function I() : SM.Variables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator, syncReqs
    reads Repr()
    requires W()
    {
      if ready then (
        SM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, syncReqs.I(), cache.I(), lru.Queue, blockAllocator.I())
      ) else (
        SM.Unready(outstandingIndirectionTableRead, syncReqs.I())
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator, syncReqs
    reads Repr()
    {
      && W()
      && SM.WFVars(I())
    }

    constructor()
    ensures !ready
    ensures syncReqs.Inv()
    ensures syncReqs.I() == MutableMapModel.Constructor(128)
    ensures outstandingIndirectionTableRead == None
    ensures WF()
    {
      ready := false;
      syncReqs := new MutableMap.ResizingHashMap(128);
      outstandingIndirectionTableRead := None;

      // Unused for the `ready = false` state but we need to initialize them.
      // (could make them nullable instead).
      lru := new LruImpl.LruImplQueue();
      ephemeralIndirectionTable := new IndirectionTableImpl.IndirectionTable.Empty();
      persistentIndirectionTable := new IndirectionTableImpl.IndirectionTable.Empty();
      frozenIndirectionTable := null;
      cache := new MutCache();

      var bm := new BitmapImpl.Bitmap(NumBlocksUint64());
      blockAllocator := new BlockAllocatorImpl.BlockAllocator(bm);
    }
  }

  predicate Inv(k: M.Constants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
        s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator, s.syncReqs
  reads s.Repr()
  {
    && s.W()
    && SM.Inv(Ic(k), s.I())
  }

  function Ic(k: M.Constants) : SM.Constants
  {
    SM.Constants()
  }

  function IIO(io: MainDiskIOHandler.DiskIOHandler) : SM.IO
  reads io
  {
    match io.diskOp() {
      case NoDiskOp => SM.IOInit(io.reservedId())
      case ReqReadOp(id, reqRead) => SM.IOReqRead(id, reqRead)
      case ReqWriteOp(id, reqWrite) => SM.IOReqWrite(id, reqWrite)
      case RespReadOp(id, respRead) => SM.IORespRead(id, respRead)
      case RespWriteOp(id, respWrite) => SM.IORespWrite(id, respWrite)
    }
  }

  twostate predicate WellUpdated(s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
      s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator, s.syncReqs
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }
}
