include "../lib/MutableMap.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "MutableBucket.i.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import TTT = TwoThreeTree
  import IM = ImplModel

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
  import opened BucketsLib

  import MM = MutableMap
  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type TreeMap = TTT.Tree<Message>

  type MutIndirectionTable = MM.ResizingHashMap<(Option<BC.Location>, seq<Reference>)>
  type MutIndirectionTableNullable = MM.ResizingHashMap?<(Option<BC.Location>, seq<Reference>)>

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<MutableBucket.MutBucket>
    )

  type MutCache = MM.ResizingHashMap<Node>

  function BucketListObjectSet(s: seq<MutableBucket.MutBucket>) : set<object>
  {
    set i | 0 <= i < |s| :: s[i]
  }

  function BucketListRepr(s: seq<MutableBucket.MutBucket>) : set<object>
  reads BucketListObjectSet(s)
  {
    set i, o | 0 <= i < |s| && o in s[i].Repr :: o
  }

  predicate BucketListReprInv(buckets: seq<MutableBucket.MutBucket>)
  reads BucketListObjectSet(buckets)
  {
    forall i, j | 0 <= i < |buckets| && 0 <= j < |buckets| && i != j ::
        buckets[i].Repr !! buckets[j].Repr
  }

  function NodeObjectSet(node: Node) : set<object>
  {
    set i | 0 <= i < |node.buckets| :: node.buckets[i]
  }

  function NodeRepr(node: Node) : set<object>
  reads NodeObjectSet(node)
  {
    set i, o | 0 <= i < |node.buckets| && o in node.buckets[i].Repr :: o
  }

  function CacheObjectSet(cache: map<BT.G.Reference, Node>) : set<object>
  {
    set ref, i | ref in cache && 0 <= i < |cache[ref].buckets| :: cache[ref].buckets[i]
  }

  function CacheRepr(cache: map<BT.G.Reference, Node>) : set<object>
  reads CacheObjectSet(cache)
  {
    set ref, i, o | ref in cache && 0 <= i < |cache[ref].buckets| && o in cache[ref].buckets[i].Repr :: o
  }

  predicate WFNode(node: Node)
  reads set i | 0 <= i < |node.buckets| :: node.buckets[i]
  reads set i, o | 0 <= i < |node.buckets| && o in node.buckets[i].Repr :: o
  {
    forall i | 0 <= i < |node.buckets| :: node.buckets[i].Inv()
  }

  function INode(node: Node) : IM.Node
  reads set i | 0 <= i < |node.buckets| :: node.buckets[i]
  reads set i, o | 0 <= i < |node.buckets| && o in node.buckets[i].Repr :: o
  {
    IM.Node(node.pivotTable, node.children,
      MutableBucket.MutBucket.ISeq(node.buckets))
  }

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)

  function SectorObjectSet(sector: Sector) : set<object>
  {
    if sector.SectorIndirectionTable? then {sector.indirectionTable} else NodeObjectSet(sector.block)
  }

  function SectorRepr(sector: Sector) : set<object>
  reads SectorObjectSet(sector)
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => {indirectionTable} + indirectionTable.Repr
      case SectorBlock(block) => NodeRepr(block)
    }
  }
 
  predicate WFSector(sector: Sector)
  reads SectorObjectSet(sector)
  reads SectorRepr(sector)
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
    && (sector.SectorBlock? ==>
      && WFNode(sector.block)
      && BucketListReprInv(sector.block.buckets)
    )
  }

  function IIndirectionTable(table: MutIndirectionTable) : (result: IM.IndirectionTable)
  reads table, table.Repr
  {
    table.Contents
  }
 
  function ICache(table: MutCache) : (result: map<BT.G.Reference, IM.Node>)
  reads table, table.Repr
  reads set ref, i | ref in table.Contents && 0 <= i < |table.Contents[ref].buckets| :: table.Contents[ref].buckets[i]
  reads set ref, i, o | ref in table.Contents && 0 <= i < |table.Contents[ref].buckets| && o in table.Contents[ref].buckets[i].Repr :: o
  {
    map ref | ref in table.Contents :: INode(table.Contents[ref])
  }

 
  function IIndirectionTableOpt(table: MutIndirectionTableNullable) : (result: Option<IM.IndirectionTable>)
  reads if table != null then {table} + table.Repr else {}
  {
    if table != null then
      Some(IIndirectionTable(table))
    else
      None
  }
 
  function ISector(sector: Sector) : IM.Sector
  requires WFSector(sector)
  reads if sector.SectorIndirectionTable? then sector.indirectionTable.Repr else {}
  reads if sector.SectorBlock?
      then set i | 0 <= i < |sector.block.buckets| :: sector.block.buckets[i]
      else {}
  reads if sector.SectorBlock?
      then set i, o | 0 <= i < |sector.block.buckets| && o in sector.block.buckets[i].Repr :: o
      else {}
  {
    match sector {
      case SectorBlock(node) => IM.SectorBlock(INode(node))
      case SectorIndirectionTable(indirectionTable) => IM.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  class Variables {
    var ready: bool;

    var syncReqs: map<int, BC.SyncReqStatus>;

    // Ready
    var persistentIndirectionTable: MutIndirectionTable;
    var frozenIndirectionTable: MutIndirectionTableNullable;
    var ephemeralIndirectionTable: MutIndirectionTable;
    var outstandingIndirectionTableWrite: Option<BC.ReqId>;
    var outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>;
    var outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>;
    var cache: MutCache;
    var lru: MutableLru.MutableLruQueue;

    // Unready
    var outstandingIndirectionTableRead: Option<D.ReqId>;

    predicate CacheReprInv() 
    reads this, cache, CacheObjectSet(cache.Contents)
    {
      && (forall ref1, i1, ref2, i2 | ref1 in cache.Contents && ref2 in cache.Contents
          && 0 <= i1 < |cache.Contents[ref1].buckets|
          && 0 <= i2 < |cache.Contents[ref2].buckets|
          && (ref1 != ref2 || i1 != i2) ::
          cache.Contents[ref1].buckets[i1].Repr !! cache.Contents[ref2].buckets[i2].Repr)
    }

    function Repr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, CacheObjectSet(cache.Contents)
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr +
      cache.Repr +
      CacheRepr(cache.Contents)
    }

    predicate ReprInv()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, CacheObjectSet(cache.Contents)
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

        && persistentIndirectionTable.Repr !! CacheRepr(cache.Contents)
        && (frozenIndirectionTable != null ==> frozenIndirectionTable.Repr !! CacheRepr(cache.Contents))
        && persistentIndirectionTable.Repr !! CacheRepr(cache.Contents)
        && cache.Repr !! CacheRepr(cache.Contents)
        && lru.Repr !! CacheRepr(cache.Contents)
        && CacheReprInv()

        && this !in ephemeralIndirectionTable.Repr
        && this !in persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> this !in frozenIndirectionTable.Repr)
        && this !in lru.Repr
        && this !in cache.Repr
        && this !in CacheRepr(cache.Contents)
    }

    predicate W()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, CacheObjectSet(cache.Contents)
    reads Repr()
    {
      && ReprInv()
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable != null ==> frozenIndirectionTable.Inv())
      && ephemeralIndirectionTable.Inv()
      && lru.Inv()
      && cache.Inv()
      && (forall ref, i | ref in cache.Contents && 0 <= i < |cache.Contents[ref].buckets| ::
          && cache.Contents[ref].buckets[i].Inv())
    }

    function I() : IM.Variables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, CacheObjectSet(cache.Contents)
    reads Repr()
    requires W()
    {
      if ready then (
        IM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, syncReqs, ICache(cache), lru.Queue)
      ) else (
        IM.Unready(outstandingIndirectionTableRead, syncReqs)
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, CacheObjectSet(cache.Contents)
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
      ephemeralIndirectionTable := new MM.ResizingHashMap(128);
      persistentIndirectionTable := new MM.ResizingHashMap(128);
      frozenIndirectionTable := null;
      cache := new MM.ResizingHashMap(128);
    }
  }

  predicate Inv(k: M.Constants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
        s.frozenIndirectionTable, s.lru, s.cache, CacheObjectSet(s.cache.Contents)
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
      s.frozenIndirectionTable, s.lru, s.cache, CacheObjectSet(s.cache.Contents)
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }
}
