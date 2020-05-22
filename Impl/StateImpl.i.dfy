include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "../lib/DataStructures/LruImpl.i.dfy"
include "StateModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "CacheImpl.i.dfy"
include "IndirectionTableImpl.i.dfy"
include "BlockAllocatorImpl.i.dfy"
include "DiskOpImpl.i.dfy"

module StateImpl {
  import DebugAccumulator
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import SM = StateModel
  import opened NodeImpl
  import opened CacheImpl
  import BlockAllocatorImpl
  import BitmapImpl
  import IndirectionTableImpl
  import IndirectionTableModel
  import MutableMap
  import MutableMapModel

  import BT = PivotBetreeSpec`Internal
  import BC = BlockCache
  import JC = JournalCache
  import M = BetreeCache
  import D = AsyncDisk
  import MainDiskIOHandler
  import LruImpl
  import BucketImpl
  import opened Bounds
  import opened BucketsLib
  import DiskLayout
  import SectorType
  import opened DiskOpImpl

  import MM = MutableMap
  import ReferenceType`Internal

  type ImplVariables = Variables

  type Reference = BT.G.Reference

  type MutIndirectionTable = IndirectionTableImpl.IndirectionTable
  type MutIndirectionTableNullable = IndirectionTableImpl.IndirectionTable?

  datatype Sector =
    | SectorNode(node: Node)
    | SectorSuperblock(superblock: SectorType.Superblock)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)

  function SectorObjectSet(sector: Sector) : set<object>
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable}
      case SectorNode(block) => {block}
      case SectorSuperblock(superblock) => {}
    }
  }

  function SectorRepr(sector: Sector) : set<object>
  reads SectorObjectSet(sector)
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable} + indirectionTable.Repr
      case SectorNode(block) => block.Repr
      case SectorSuperblock(superblock) => {}
    }
  }
 
  predicate WFSector(sector: Sector)
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorNode? ==> sector.node.Inv())
    && (sector.SectorSuperblock? ==> JC.WFSuperblock(sector.superblock))
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
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    match sector {
      case SectorSuperblock(superblock) => SM.SectorSuperblock(superblock)
      case SectorNode(node) => SM.SectorNode(node.I())
      case SectorIndirectionTable(indirectionTable) => SM.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  // TODO rename to like... BlockCache variables or smthn
  class Variables {
    var loading: bool;
    var ready: bool;

    // Ready
    var persistentIndirectionTable: MutIndirectionTable;
    var frozenIndirectionTable: MutIndirectionTableNullable;
    var ephemeralIndirectionTable: MutIndirectionTable;
    var persistentIndirectionTableLoc: DiskLayout.Location;
    var frozenIndirectionTableLoc: Option<DiskLayout.Location>;
    var outstandingIndirectionTableWrite: Option<BC.ReqId>;
    var outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>;
    var outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>;
    var cache: MutCache;
    var lru: LruImpl.LruImplQueue;
    var blockAllocator: BlockAllocatorImpl.BlockAllocator;

    // Loading
    var indirectionTableLoc: DiskLayout.Location;
    var indirectionTableRead: Option<BC.ReqId>;

    // Unready
    // no fields

    method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      //var r := new DebugAccumulator.AccRec(syncReqs.Count, "SyncReqStatus");
      //acc := DebugAccumulator.AccPut(acc, "syncReqs", r);
      var i := DebugAccumulator.EmptyAccumulator();
      if persistentIndirectionTable != null {
        i := persistentIndirectionTable.DebugAccumulate();
      }
      var a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "persistentIndirectionTable", a);
      i := DebugAccumulator.EmptyAccumulator();
      if frozenIndirectionTable != null {
        i := frozenIndirectionTable.DebugAccumulate();
      }
      a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "frozenIndirectionTable", a);
      i := DebugAccumulator.EmptyAccumulator();
      if ephemeralIndirectionTable != null {
        i := ephemeralIndirectionTable.DebugAccumulate();
      }
      a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "ephemeralIndirectionTable", a);
      //r := new DebugAccumulator.AccRec(if outstandingIndirectionTableWrite.Some? then 1 else 0, "ReqId");
      //acc := DebugAccumulator.AccPut(acc, "outstandingIndirectionTableWrite", r);
      //r := new DebugAccumulator.AccRec(|outstandingBlockWrites| as uint64, "OutstandingWrites");
      //acc := DebugAccumulator.AccPut(acc, "outstandingBlockWrites", r);
      //r := new DebugAccumulator.AccRec(|outstandingBlockReads| as uint64, "OutstandingReads");
      //acc := DebugAccumulator.AccPut(acc, "outstandingBlockReads", r);
      i := cache.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "cache", a);
      i := lru.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "lru", a);
      i := blockAllocator.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(i);
      acc := DebugAccumulator.AccPut(acc, "blockAllocator", a);
    }

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
        && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr !! lru.Repr !! cache.Repr !! blockAllocator.Repr
        && (frozenIndirectionTable != null ==>
            && frozenIndirectionTable.Repr !! persistentIndirectionTable.Repr
            && frozenIndirectionTable.Repr !! ephemeralIndirectionTable.Repr
            && frozenIndirectionTable.Repr !! lru.Repr
            && frozenIndirectionTable.Repr !! cache.Repr
            && frozenIndirectionTable.Repr !! blockAllocator.Repr
        )

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

    function I() : SM.BCVariables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    requires W()
    {
      if ready then (
        SM.Ready(
          IIndirectionTable(persistentIndirectionTable),
          IIndirectionTableOpt(frozenIndirectionTable),
          IIndirectionTable(ephemeralIndirectionTable),
          persistentIndirectionTableLoc,
          frozenIndirectionTableLoc,
          outstandingIndirectionTableWrite,
          outstandingBlockWrites,
          outstandingBlockReads,
          cache.I(),
          lru.Queue,
          blockAllocator.I())
      ) else if loading then (
        SM.LoadingIndirectionTable(
          indirectionTableLoc,
          indirectionTableRead)
      ) else (
        SM.Unready
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, blockAllocator
    reads Repr()
    {
      && W()
      && SM.WFBCVars(I())
    }

    constructor()
    ensures !ready
    ensures !loading
    ensures WF()
    ensures fresh(Repr())
    {
      ready := false;
      loading := false;

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

  predicate Inv(k: ImplConstants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
        s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator
  reads s.Repr()
  {
    && s.W()
    && SM.BCInv(Ic(k), s.I())
  }

  twostate predicate WellUpdated(s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
      s.frozenIndirectionTable, s.lru, s.cache, s.blockAllocator
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }

  function method TotalCacheSize(s: ImplVariables) : (res : uint64)
  reads s, s.cache, s.cache.Repr
  requires s.cache.Inv()
  requires |s.cache.I()| + |s.outstandingBlockReads| < 0x1_0000_0000_0000_0000
  {
    s.cache.Count() + (|s.outstandingBlockReads| as uint64)
  }
}
