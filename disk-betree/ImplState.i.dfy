include "../lib/MutableMapImpl.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"
include "ImplNodes.i.dfy"
include "IndirectionTableImpl.i.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import TTT = TwoThreeTree
  import IM = ImplModel
  import opened ImplNode
  import opened ImplMutCache
  import ImplBlockAllocator
  import Bitmap
  import IndirectionTableImpl
  import IndirectionTableModel

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import D = AsyncSectorDisk
  import MainDiskIOHandler
  import LruModel
  import MutableLru
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
 
  function IIndirectionTableOpt(table: MutIndirectionTableNullable) : (result: Option<IM.IndirectionTable>)
  reads if table != null then {table} + table.Repr else {}
  requires table != null ==> table.Inv()
  {
    if table != null then
      Some(IIndirectionTable(table))
    else
      None
  }
 
  function ISector(sector: Sector) : IM.Sector
  requires WFSector(sector)
  reads if sector.SectorIndirectionTable? then {sector.indirectionTable} else {sector.block}
  reads SectorRepr(sector)
  {
    match sector {
      case SectorBlock(node) => IM.SectorBlock(node.I())
      case SectorIndirectionTable(indirectionTable) => IM.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  class Variables {
    var ready: bool;

    var syncReqs: map<uint64, BC.SyncReqStatus>;

    // Ready
    var persistentIndirectionTable: MutIndirectionTable;
    var frozenIndirectionTable: MutIndirectionTableNullable;
    var ephemeralIndirectionTable: MutIndirectionTable;
    var outstandingIndirectionTableWrite: Option<BC.ReqId>;
    var outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>;
    var outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>;
    var cache: MutCache;
    var lru: MutableLru.MutableLruQueue;
    var blockAllocator: ImplBlockAllocator.BlockAllocator;

    // Unready
    var outstandingIndirectionTableRead: Option<D.ReqId>;

    function Repr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr +
      cache.Repr +
      blockAllocator.Repr
    }

    predicate ReprInv()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    {
        // NOALIAS statically enforced no-aliasing would probably help here

        && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> persistentIndirectionTable.Repr !! frozenIndirectionTable.Repr)
        && (frozenIndirectionTable != null ==> ephemeralIndirectionTable.Repr !! frozenIndirectionTable.Repr)
        && persistentIndirectionTable.Repr !! lru.Repr
        && ephemeralIndirectionTable.Repr !! lru.Repr
        && (frozenIndirectionTable != null ==> frozenIndirectionTable.Repr !! lru.Repr)
        && cache.Repr !! ephemeralIndirectionTable.Repr
        && cache.Repr !! persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> cache.Repr !! frozenIndirectionTable.Repr)
        && cache.Repr !! lru.Repr
        && blockAllocator.Repr !! ephemeralIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> blockAllocator.Repr !! frozenIndirectionTable.Repr)
        && blockAllocator.Repr !! persistentIndirectionTable.Repr
        && blockAllocator.Repr !! lru.Repr
        && blockAllocator.Repr !! cache.Repr

        && this !in ephemeralIndirectionTable.Repr
        && this !in persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> this !in frozenIndirectionTable.Repr)
        && this !in lru.Repr
        && this !in cache.Repr
        && this !in blockAllocator.Repr
    }

    predicate W()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    {
      && ReprInv()
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable != null ==> frozenIndirectionTable.Inv())
      && ephemeralIndirectionTable.Inv()
      && lru.Inv()
      && cache.Inv()
      && blockAllocator.Inv()
    }

    function I() : IM.Variables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    requires W()
    {
      if ready then (
        IM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, syncReqs, cache.I(), lru.Queue, blockAllocator.I())
      ) else (
        IM.Unready(outstandingIndirectionTableRead, syncReqs)
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    {
      && W()
      && IM.WFVars(I())
    }

    constructor()
    ensures !ready
    ensures syncReqs == map[]
    ensures outstandingIndirectionTableRead == None
    ensures WF()
    {
      ready := false;
      syncReqs := map[];
      outstandingIndirectionTableRead := None;

      // Unused for the `ready = false` state but we need to initialize them.
      // (could make them nullable instead).
      lru := new MutableLru.MutableLruQueue();
      ephemeralIndirectionTable := new IndirectionTableImpl.IndirectionTable.Empty();
      persistentIndirectionTable := new IndirectionTableImpl.IndirectionTable.Empty();
      frozenIndirectionTable := null;
      cache := new MutCache();

      var bm := new Bitmap.Bitmap(NumBlocksUint64());
      blockAllocator := new ImplBlockAllocator.BlockAllocator(bm);
    }
  }

  predicate Inv(k: M.Constants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
        s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator
  reads s.Repr()
  {
    && s.W()
    && IM.Inv(Ic(k), s.I())
  }

  function Ic(k: M.Constants) : IM.Constants
  {
    IM.Constants()
  }

  function IIO(io: MainDiskIOHandler.DiskIOHandler) : IM.IO
  reads io
  {
    match io.diskOp() {
      case NoDiskOp => IM.IOInit(io.reservedId())
      case ReqReadOp(id, reqRead) => IM.IOReqRead(id, reqRead)
      case ReqWriteOp(id, reqWrite) => IM.IOReqWrite(id, reqWrite)
      case RespReadOp(id, respRead) => IM.IORespRead(id, respRead)
      case RespWriteOp(id, respWrite) => IM.IORespWrite(id, respWrite)
    }
  }

  twostate predicate WellUpdated(s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
      s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }
}
