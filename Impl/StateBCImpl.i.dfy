include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/DataStructures/LinearLru.i.dfy"
include "IndirectionTable.i.dfy"
include "StateBCModel.i.dfy"
include "StateSectorImpl.i.dfy"
include "BlockAllocatorImpl.i.dfy"
include "CacheImpl.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "StateBCModel.i.dfy"

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


  type ImplVariables = Variables
  type Reference = BT.G.Reference

  // TODO rename to like... BlockCache variables or smthn
  linear datatype Variables = Variables(
    loading: bool,
    ready: bool,

    // Ready
    linear persistentIndirectionTable: IT.IndirectionTable,
    linear frozenIndirectionTable: lOption<IT.IndirectionTable>,
    linear ephemeralIndirectionTable: IT.IndirectionTable,
    persistentIndirectionTableLoc: DiskLayout.Location,
    frozenIndirectionTableLoc: Option<DiskLayout.Location>,
    outstandingIndirectionTableWrite: Option<BC.ReqId>,
    outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>,
    outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>,
    linear cache: LMutCache,
    linear lru: LinearLru.LinearLru,
    linear blockAllocator: BlockAllocatorImpl.BlockAllocator,

    // Loading
    indirectionTableLoc: DiskLayout.Location,
    indirectionTableRead: Option<BC.ReqId>
    
    // Unready
    // no fields
  )
  {
    // method DebugAccumulate()
    // returns (acc:DebugAccumulator.DebugAccumulator)
    // requires false
    // {
    //   acc := DebugAccumulator.EmptyAccumulator();
    //   //var r := new DebugAccumulator.AccRec(syncReqs.Count, "SyncReqStatus");
    //   //acc := DebugAccumulator.AccPut(acc, "syncReqs", r);
    //   var i := DebugAccumulator.EmptyAccumulator();
    //   if persistentIndirectionTable != null {
    //     i := persistentIndirectionTable.DebugAccumulate();
    //   }
    //   var a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "persistentIndirectionTable", a);
    //   i := DebugAccumulator.EmptyAccumulator();
    //   if frozenIndirectionTable != null {
    //     i := frozenIndirectionTable.DebugAccumulate();
    //   }
    //   a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "frozenIndirectionTable", a);
    //   i := DebugAccumulator.EmptyAccumulator();
    //   if ephemeralIndirectionTable != null {
    //     i := ephemeralIndirectionTable.DebugAccumulate();
    //   }
    //   a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "ephemeralIndirectionTable", a);
    //   //r := new DebugAccumulator.AccRec(if outstandingIndirectionTableWrite.Some? then 1 else 0, "ReqId");
    //   //acc := DebugAccumulator.AccPut(acc, "outstandingIndirectionTableWrite", r);
    //   //r := new DebugAccumulator.AccRec(|outstandingBlockWrites| as uint64, "OutstandingWrites");
    //   //acc := DebugAccumulator.AccPut(acc, "outstandingBlockWrites", r);
    //   //r := new DebugAccumulator.AccRec(|outstandingBlockReads| as uint64, "OutstandingReads");
    //   //acc := DebugAccumulator.AccPut(acc, "outstandingBlockReads", r);
    //   i := cache.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "cache", a);
    //   i := lru.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "lru", a);
    //   i := blockAllocator.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(i);
    //   acc := DebugAccumulator.AccPut(acc, "blockAllocator", a);
    // }

    predicate W()
    {
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable.lSome? ==> frozenIndirectionTable.value.Inv())
      && ephemeralIndirectionTable.Inv()
      && lru.Inv()
      && cache.Inv()
      && blockAllocator.Inv()
    }

    function I() : SBCM.BCVariables
    requires W()
    {
      if ready then (
        SBCM.Ready(
          persistentIndirectionTable,
          if frozenIndirectionTable.lSome? then Some(frozenIndirectionTable.value) else None,
          ephemeralIndirectionTable,
          persistentIndirectionTableLoc,
          frozenIndirectionTableLoc,
          outstandingIndirectionTableWrite,
          outstandingBlockWrites,
          outstandingBlockReads,
          cache.I(),
          lru.Queue(),
          blockAllocator.I())
      ) else if loading then (
        SBCM.LoadingIndirectionTable(
          indirectionTableLoc,
          indirectionTableRead)
      ) else (
        SBCM.Unready
      )
    }

    predicate WF()
    {
      && W()
      && SBCM.WFBCVars(I())
    }

    static method Constructor() returns (linear v: Variables)
    ensures !v.ready
    ensures !v.loading
    ensures v.WF()
    {
      linear var lru := LinearLru.LinearLru.Alloc();
      // Unused for the `ready = false` state but we need to initialize them.
      // (could make them nullable instead).
      linear var ephemeralIndirectionTable := IT.IndirectionTable.AllocEmpty();
      linear var persistentIndirectionTable := IT.IndirectionTable.AllocEmpty();
      linear var cache := LMutCache.NewCache();

      linear var bm := BitmapImpl.Bitmap.Constructor(NumBlocksUint64());
      linear var blockAllocator := BlockAllocatorImpl.BlockAllocator.Constructor(bm);

      v := Variables(
        false,
        false,
        persistentIndirectionTable,
        lNone,
        ephemeralIndirectionTable,
        DiskLayout.Location(0, 0),
        None,
        None,
        map[],
        map[],
        cache,
        lru,
        blockAllocator,
        DiskLayout.Location(0, 0),
        None);
    }

    predicate Inv()
    {
      && W()
      && SBCM.BCInv(I())
    }

    shared function method TotalCacheSize() : (res : uint64)
    requires cache.Inv()
    requires |cache.I()| + |outstandingBlockReads| < 0x1_0000_0000_0000_0000
    ensures res as int == SBCM.TotalCacheSize(I())
    {
      // cache.Count() + (|outstandingBlockReads| as uint64)
      CacheImpl.CacheCount(cache) + (|outstandingBlockReads| as uint64)
    }
  }
}
