include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/DataStructures/LinearLru.i.dfy"
include "IndirectionTable.i.dfy"
include "StateBCModel.i.dfy"
include "StateSectorImpl.i.dfy"
include "BlockAllocatorImpl.i.dfy"
include "CacheImpl.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
// include "StateBCModel.i.dfy"

module StateBCImpl {
  import opened Options
  import opened NativeTypes
  import opened StateSectorImpl
  import opened CacheImpl
  import IT = IndirectionTable
  import opened Bounds
  import opened LinearOption

  import BitmapImpl
  import DebugAccumulator
  import DiskLayout
  import BT = PivotBetreeSpec`Internal
  import BC = BlockCache
  import LinearLru
  import BlockAllocatorImpl
  import D = AsyncDisk
  import SBCM = StateBCModel
  import BlockAllocatorModel
  import LruModel

  import opened StateSectorModel
  import BBC = BetreeCache

  type ImplVariables = Variables
  type Reference = BT.G.Reference

  predicate WFCache(cache: map<Reference, Node>)
  {
    forall ref | ref in cache :: WFNode(cache[ref])
  }

  function ICache(cache: map<Reference, Node>): map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INode(cache[ref])
  }

  predicate IsLocAllocOutstanding(outstanding: map<BC.ReqId, BC.OutstandingWrite>, i: int)
  {
    !(forall id | id in outstanding :: outstanding[id].loc.addr as int != i * NodeBlockSize() as int)
  }

  predicate {:opaque} ConsistentBitmap(
      ephemeralIndirectionTable: SectorType.IndirectionTable,
      frozenIndirectionTable: lOption<SectorType.IndirectionTable>,
      persistentIndirectionTable: SectorType.IndirectionTable,
      outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
      blockAllocator: BlockAllocatorModel.BlockAllocatorModel)
  {
    && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(ephemeralIndirectionTable, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.ephemeral, i))
    && (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(persistentIndirectionTable, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.persistent, i))
    && (frozenIndirectionTable.lSome? <==> blockAllocator.frozen.Some?)
    && (frozenIndirectionTable.lSome? ==>
      (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(frozenIndirectionTable.value, i)
        <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.frozen.value, i)))
    && (forall i: int :: IsLocAllocOutstanding(outstandingBlockWrites, i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(blockAllocator.outstanding, i))
  }

  // TODO rename to like... BlockCache variables or smthn
  linear datatype Variables = 
    | Ready(
        linear persistentIndirectionTable: IT.IndirectionTable, 
        linear frozenIndirectionTable: lOption<IT.IndirectionTable>,
        linear ephemeralIndirectionTable: IT.IndirectionTable,
        persistentIndirectionTableLoc: DiskLayout.Location,
        frozenIndirectionTableLoc: Option<DiskLayout.Location>,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<BC.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<BC.ReqId, BC.OutstandingRead>,
        linear cache: LMutCache,
        linear lru: LinearLru.LinearLru,
        linear blockAllocator: BlockAllocatorImpl.BlockAllocator
      )
    | Loading(
        indirectionTableLoc: DiskLayout.Location,
        indirectionTableRead: Option<BC.ReqId>)
    | Unready
  {
    method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      // acc := DebugAccumulator.EmptyAccumulator();
      // //var r := new DebugAccumulator.AccRec(syncReqs.Count, "SyncReqStatus");
      // //acc := DebugAccumulator.AccPut(acc, "syncReqs", r);
      // var i := DebugAccumulator.EmptyAccumulator();
      // if persistentIndirectionTable != null {
      //   i := persistentIndirectionTable.DebugAccumulate();
      // }
      // var a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "persistentIndirectionTable", a);
      // i := DebugAccumulator.EmptyAccumulator();
      // if frozenIndirectionTable != null {
      //   i := frozenIndirectionTable.DebugAccumulate();
      // }
      // a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "frozenIndirectionTable", a);
      // i := DebugAccumulator.EmptyAccumulator();
      // if ephemeralIndirectionTable != null {
      //   i := ephemeralIndirectionTable.DebugAccumulate();
      // }
      // a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "ephemeralIndirectionTable", a);
      // //r := new DebugAccumulator.AccRec(if outstandingIndirectionTableWrite.Some? then 1 else 0, "ReqId");
      // //acc := DebugAccumulator.AccPut(acc, "outstandingIndirectionTableWrite", r);
      // //r := new DebugAccumulator.AccRec(|outstandingBlockWrites| as uint64, "OutstandingWrites");
      // //acc := DebugAccumulator.AccPut(acc, "outstandingBlockWrites", r);
      // //r := new DebugAccumulator.AccRec(|outstandingBlockReads| as uint64, "OutstandingReads");
      // //acc := DebugAccumulator.AccPut(acc, "outstandingBlockReads", r);
      // i := cache.DebugAccumulate();
      // a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "cache", a);
      // i := lru.DebugAccumulate();
      // a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "lru", a);
      // i := blockAllocator.DebugAccumulate();
      // a := new DebugAccumulator.AccRec.Index(i);
      // acc := DebugAccumulator.AccPut(acc, "blockAllocator", a);
    }

    shared function method TotalCacheSize() : (res : uint64)
    requires Ready?
    requires cache.Inv()
    requires |cache.I()| + |outstandingBlockReads| < 0x1_0000_0000_0000_0000
    ensures res as int == totalCacheSize()
    {
      CacheImpl.CacheCount(cache) + (|outstandingBlockReads| as uint64)
    }

    // TODO reuse the definition in BlockCache?
    function totalCacheSize() : int
    requires Ready?
    requires cache.Inv()
    {
      |cache.I()| + |outstandingBlockReads|
    }

    predicate W()
    {
      Ready? ==> (
        && persistentIndirectionTable.Inv()
        && (frozenIndirectionTable.lSome? ==> frozenIndirectionTable.value.Inv())
        && ephemeralIndirectionTable.Inv()
        && lru.Inv()
        && cache.Inv()
        && blockAllocator.Inv()
      )
    }

    predicate WFVarsReady()
    requires Ready?
    requires W()
    {
      && WFCache(cache.I())
      && LruModel.WF(lru.Queue())
      && LruModel.I(lru.Queue()) == cache.I().Keys
      && totalCacheSize() <= MaxCacheSize()
      && ephemeralIndirectionTable.TrackingGarbage()
      && BlockAllocatorModel.Inv(blockAllocator.I())
      && ConsistentBitmap(ephemeralIndirectionTable.I(), frozenIndirectionTable. Map((x: IndirectionTable) => x.I()),
          persistentIndirectionTable.I(), outstandingBlockWrites, blockAllocator.I())
    }

    predicate WFBCVars()
    {
      && W()
      && (Ready? ==> WFVarsReady())
    }

    function IBlockCache() : BBC.Variables
    requires WFBCVars()
    {
      if Ready? then (
          BC.Ready(persistentIndirectionTable.I(), 
          if frozenIndirectionTable.lSome? then Some(frozenIndirectionTable.value.I()) else None, ephemeralIndirectionTable.I(),  persistentIndirectionTableLoc, frozenIndirectionTableLoc, outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, ICache(cache.I()))
      ) else if Loading? then (
          BC.LoadingIndirectionTable(indirectionTableLoc, indirectionTableRead)
      ) else (
        BC.Unready
      )
    }

    predicate BCInv()
    {
      && WFBCVars()
      && BBC.Inv(IBlockCache())
    }

    static method Constructor() returns (linear v: Variables)
    ensures v.Unready?
    ensures v.WFBCVars()
    {
      v := Unready;
    }
  }
}
