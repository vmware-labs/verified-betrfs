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
  import opened Bounds
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

  predicate {:opaque} BucketListReprInv(buckets: seq<MutableBucket.MutBucket>)
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

  function {:opaque} CacheRepr(cache: map<BT.G.Reference, Node>) : set<object>
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
 
  /*function ICache(table: MutCache) : (result: map<BT.G.Reference, IM.Node>)
  reads table, table.Repr
  reads set ref, i | ref in table.Contents && 0 <= i < |table.Contents[ref].buckets| :: table.Contents[ref].buckets[i]
  reads set ref, i, o | ref in table.Contents && 0 <= i < |table.Contents[ref].buckets| && o in table.Contents[ref].buckets[i].Repr :: o
  {
      map ref | ref in table.Contents :: INode(table.Contents[ref])
  }*/
 
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

  // These functions are all pulled out so that we can avoid having `reads this` on them.

  predicate {:opaque} BucketsInv_(contents: map<BT.G.Reference, Node>, BucketObjects: set<object>, BucketRepr: set<object>)
  reads BucketObjects, BucketRepr
  requires BucketObjects == CacheObjectSet(contents)
  requires BucketRepr == CacheRepr(contents)
  {
    reveal_CacheRepr();
    (forall ref, i | ref in contents && 0 <= i < |contents[ref].buckets| ::
      && contents[ref].buckets[i].Inv())
  }

  function {:opaque} Cache_(cache: MutCache, BucketObjects: set<object>, BucketRepr: set<object>) : map<BT.G.Reference, IM.Node>
  reads cache, BucketObjects, BucketRepr
  requires BucketObjects == CacheObjectSet(cache.Contents)
  requires BucketRepr == CacheRepr(cache.Contents)
  ensures forall ref | ref in cache.Contents :: ref in Cache_(cache, BucketObjects, BucketRepr)
  ensures forall ref | ref in cache.Contents :: 
      Cache_(cache, BucketObjects, BucketRepr)[ref] == INode(cache.Contents[ref])
  {
    reveal_CacheRepr();
    map ref | ref in cache.Contents :: INode(cache.Contents[ref])
  }

  predicate {:opaque} CacheReprInv_(contents: map<BT.G.Reference, Node>, BucketObjects: set<object>) 
  reads BucketObjects
  requires BucketObjects == CacheObjectSet(contents)
  {
    && (forall ref1, i1, ref2, i2 | ref1 in contents && ref2 in contents
        && 0 <= i1 < |contents[ref1].buckets|
        && 0 <= i2 < |contents[ref2].buckets|
        && (ref1 != ref2 || i1 != i2) ::
        contents[ref1].buckets[i1].Repr !! contents[ref2].buckets[i2].Repr)
  }


  class Variables {
    ghost var BucketObjects: set<object>;
    ghost var BucketRepr: set<object>;

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
    reads this, cache, BucketObjects
    requires BucketObjects == CacheObjectSet(cache.Contents)
    {
      CacheReprInv_(cache.Contents, BucketObjects)
    }

    function NonBucketsRepr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr +
      cache.Repr
    }

    function Repr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, BucketObjects
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr +
      cache.Repr +
      BucketRepr
    }

    predicate ReprInv()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, BucketObjects
    reads Repr()
    {
        // NOALIAS statically enforced no-aliasing would probably help here
        && BucketObjects == CacheObjectSet(cache.Contents)
        && BucketRepr == CacheRepr(cache.Contents)
        && BucketObjects <= BucketRepr

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

        && persistentIndirectionTable.Repr !! BucketRepr
        && (frozenIndirectionTable != null ==> frozenIndirectionTable.Repr !! BucketObjects)
        && ephemeralIndirectionTable.Repr !! BucketObjects
        && cache.Repr !! BucketObjects
        && lru.Repr !! BucketObjects
        && CacheReprInv()

        && this !in ephemeralIndirectionTable.Repr
        && this !in persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> this !in frozenIndirectionTable.Repr)
        && this !in lru.Repr
        && this !in cache.Repr
        && this !in BucketRepr
    }

    predicate BucketsInv()
    reads this, cache
    reads BucketObjects, BucketRepr
    requires BucketObjects == CacheObjectSet(cache.Contents)
    requires BucketRepr == CacheRepr(cache.Contents)
    {
      BucketsInv_(cache.Contents, BucketObjects, BucketRepr)
    }

    predicate W()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, BucketObjects
    reads Repr()
    {
      && ReprInv()
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable != null ==> frozenIndirectionTable.Inv())
      && ephemeralIndirectionTable.Inv()
      && lru.Inv()
      && cache.Inv()
      && BucketsInv()
    }

    function Cache() : map<BT.G.Reference, IM.Node>
    reads this, cache
    reads BucketObjects, BucketRepr
    requires BucketObjects == CacheObjectSet(cache.Contents)
    requires BucketRepr == CacheRepr(cache.Contents)
    {
      Cache_(cache, BucketObjects, BucketRepr)
    }

    function I() : IM.Variables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, BucketObjects
    reads Repr()
    requires W()
    {
      if ready then (
        IM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, syncReqs, Cache(), lru.Queue)
      ) else (
        IM.Unready(outstandingIndirectionTableRead, syncReqs)
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru, cache, BucketObjects
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

      new;

      BucketObjects := CacheObjectSet(cache.Contents);
      BucketRepr := CacheRepr(cache.Contents);

      reveal_CacheRepr();
      reveal_CacheReprInv_();
    }
  }

  predicate Inv(k: M.Constants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
        s.frozenIndirectionTable, s.lru, s.cache, s.BucketObjects
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
      s.frozenIndirectionTable, s.lru, s.cache, s.BucketObjects
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }

  // Some helpful lemmas

  lemma LemmaCacheObjectSetLeRepr(cache: map<BT.G.Reference, Node>)
  requires BucketsInv_(cache, CacheObjectSet(cache), CacheRepr(cache))
  ensures CacheObjectSet(cache) <= CacheRepr(cache)
  {
    reveal_BucketsInv_();
    reveal_Cache_();
    reveal_CacheRepr();
  }

  lemma LemmaReprCacheInsert(cache: map<BT.G.Reference, Node>, ref: BT.G.Reference, node: Node, s: Variables)
  requires s.cache.Contents == cache[ref := node]
  requires CacheRepr(cache) !! NodeRepr(node)
  requires CacheRepr(cache) !! s.NonBucketsRepr()
  requires NodeRepr(node) !! s.NonBucketsRepr()
  requires CacheReprInv_(cache, CacheObjectSet(cache))
  requires BucketListReprInv(node.buckets)
  ensures CacheRepr(s.cache.Contents) !! s.NonBucketsRepr()
  ensures CacheReprInv_(s.cache.Contents, CacheObjectSet(s.cache.Contents))
  ensures BucketsInv_(s.cache.Contents, CacheObjectSet(s.cache.Contents), CacheRepr(s.cache.Contents))

  method CacheInsert(k: M.Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.W()
  requires s.ready
  requires NodeRepr(node) !! s.Repr()
  requires |s.cache.Contents| <= MaxCacheSize();
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == old(s.I()).(cache := old(s.I()).cache[ref := INode(node)])
  {
    var _ := s.cache.Insert(ref, node);

    s.BucketObjects := CacheObjectSet(s.cache.Contents);
    s.BucketRepr := CacheRepr(s.cache.Contents);

    reveal_BucketListReprInv();
    reveal_CacheRepr();
    reveal_Cache_();
    reveal_CacheReprInv_();
  }
}
