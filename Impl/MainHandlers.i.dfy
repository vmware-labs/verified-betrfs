// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/DebugAccumulator.i.dfy"
include "Main.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "CoordinationImpl.i.dfy"
include "HandleReadResponseImpl.i.dfy"
include "HandleWriteResponseImpl.i.dfy"
include "Mkfs.i.dfy"
include "AllocationReport.i.dfy"
include "../ByteBlockCacheSystem/ByteSystem_Refines_ThreeStateVersionedMap.i.dfy"

//
// Implements the application-API-handler obligations laid out by Main.s.dfy. TODO rename in a way that emphasizes that this is a module-refinement of the abstract Main that satisfies its obligations.
//

module MainHandlers refines Main { 
  import DebugAccumulator
  import DOM = DiskOpModel
  import SI = StateBCImpl
  import opened EvictImpl // (jonh) only used for unverified debug hooks
  import CoordinationImpl
  import HandleReadResponseImpl
  import HandleReadResponseModel
  import HandleWriteResponseImpl
  import FullImpl
  import MkfsImpl
  import MkfsModel
  import Bounds  // (jonh) only used for metadata recording hook

  import BlockJournalCache
  import BBC = BetreeCache
  import BC = BlockCache
  import JC = JournalCache
  import ADM = ByteSystem

  import opened DiskOpImpl
  import opened InterpretationDiskOps
  import CacheImpl

  import System_Ref = ByteSystem_Refines_ThreeStateVersionedMap
  import AllocationReport
  import BJC = BlockJournalCache

  type FullVariables = FullImpl.Full

  // predicate W(fs: FullVariables)
  // {
  //   fs.W()
  // }

  predicate Inv(fs: FullVariables)
  {
    fs.Inv()
  }

  function I(fs: FullVariables) : ADM.M.Variables
  {
    fs.I()
  }

  method PrintMetadata()
  {
    print "metadata NodeBlockSize ", Bounds.NodeBlockSizeUint64(), "\n";
    print "metadata MaxTotalBucketWeight ", Bounds.MaxTotalBucketWeightUint64(), "\n";
    print "metadata MaxCacheSize ", Bounds.MaxCacheSizeUint64(), "\n";
    print "metadata MaxNumChildren ", Bounds.MaxNumChildrenUint64(), "\n";
    print "metadata IndirectionTableBlockSize ", Bounds.IndirectionTableBlockSizeUint64(), "\n";
    print "metadata MinNodeBlockIndex ", Bounds.MinNodeBlockIndexUint64(), "\n";
    print "metadata DiskNumJournalBlocks ", Bounds.DiskNumJournalBlocksUint64(), "\n";
  }

  method InitState() returns (linear fs: FullVariables)
    // conditions inherited:
    //ensures Inv(hs)
    //ensures ADM.M.Init(I(fs))
  {
    PrintMetadata();
    fs := FullImpl.Full.Constructor();
    assert Inv(fs);
    BlockJournalCache.InitImpliesInv(I(fs));
  }

  ////////// Top-level handlers
  method handlePushSync(linear inout fs: FullVariables, io: DiskIOHandler)
  returns (id: uint64)
  {
    var id1 := CoordinationImpl.pushSync(inout fs);

    //assert ADM.M.Next(old_fs.I(), SM.IVars(s.I()),
    //   if id1 == 0 then UI.NoOp else UI.PushSyncOp(id1 as int),
    //   D.NoDiskOp);

    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }

    //assert SM.Inv(hs.s.I());
    //assert hs.s.Inv();
    //assert Inv(hs);
    assert ADM.M.Next(I(old_fs), I(fs), uiop, io.diskOp()); // observe
  }

  // (jonh) unverified debug hook: Note "requires false" which prevents calling
  // this hook from any real handler code. It's only reachable from hooks
  // in the trusted benchmark driver; we used it to diagnose memory leaks.
  method handleEvictEverything(linear inout s: FullVariables, io: DiskIOHandler)
  requires false
  {
    print "\nBefore\n";
    // var acc := s.bc.DebugAccumulate();
    // DebugAccumulator.Display(acc, 0);

    // var count:uint64 := s.bc.cache.cache.Count;
    var count:uint64 := CacheImpl.CacheCount(s.bc.cache); // [yizhou7][REVIEW]: replace the above to this

//    var last_count:uint64 := count;
//    var last_at_this_count:uint64 = 0;
    while (count > 0)
    { // somehow it gets to where we can't get rid of the last few...?
      EvictOrDealloc(inout s.bc, io);
      // count := s.bc.cache.cache.Count;
      count := CacheImpl.CacheCount(s.bc.cache); // [yizhou7][REVIEW]: replace the above to this
    }
    print "\nAfter\n";
    // acc := s.bc.DebugAccumulate();
    // DebugAccumulator.Display(acc, 0);
  }

  // (jonh) unverified debug hook: Note "requires false" which prevents calling
  // this hook from any real handler code. It's only reachable from hooks
  // in the trusted benchmark driver; we used it to diagnose memory leaks.
  method handleCountAmassAllocations(linear inout fs: FullVariables, io: DiskIOHandler)
  requires false
  {
    /*
    AllocationReport.start();
    var s := hs.s;

    var cache := s.bc.cache.cache;
    var iter := cache.SimpleIterStart();
    var output := cache.SimpleIterOutput(iter);
    while (!output.Done?) {
      var node := output.value;

      AllocationReport.sampleNode(0, node);
      /*
      var bi:uint64 := 0;
      while (bi < |node.buckets| as uint64) {
        var bucket := node.buckets[bi];
        AllocationReport.sampleBucket(0, bucket);
        bi := bi + 1;
      }
      */

      iter := cache.SimpleIterInc(iter);
      output := cache.SimpleIterOutput(iter);
    }

    AllocationReport.stop();
    */
  }

  method handlePopSync(linear inout fs: FullVariables, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (wait: bool, success: bool)
  {
    var succ, w := CoordinationImpl.popSync(inout fs, io, id, graphSync);
    success := succ;
    wait := w;
    ghost var uiop := if succ then UI.PopSyncOp(id as int) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    assert ADM.M.Next(I(old_fs), I(fs), // observe
        uiop,
        io.diskOp());
  }

  method handleQuery(linear inout fs: FullVariables, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  {
    var value := CoordinationImpl.query(inout fs, io, key);
    ghost var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    v := value;
    assert ADM.M.Next(I(old_fs), I(fs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(linear inout fs: FullVariables, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  {
    var succ := CoordinationImpl.insert(inout fs, io, key, value);
    ghost var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    success := succ;
    assert ADM.M.Next(I(old_fs), I(fs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleSucc(linear inout fs: FullVariables, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  {
    var value := CoordinationImpl.succ(inout fs, io, start, maxToFind);
    ghost var uiop := 
      if value.Some? then UI.SuccOp(start, value.value.results, value.value.end) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    res := value;
    assert ADM.M.Next(I(old_fs), I(fs), // observe
        uiop,
        io.diskOp());
  }

  method handleReadResponse(linear inout fs: FullVariables, io: DiskIOHandler)
  {
    HandleReadResponseImpl.readResponse(inout fs, io);
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    assert ADM.M.Next(I(old_fs), I(fs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(linear inout fs: FullVariables, io: DiskIOHandler)
  {
    HandleWriteResponseImpl.writeResponse(inout fs, io);
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(old_fs.I(), fs.I(), uiop, IDiskOp(io.diskOp()));
    }
    assert ADM.M.Next(I(old_fs), I(fs), UI.NoOp, io.diskOp()); // observe
  }

  predicate InitDiskContents(diskContents: map<uint64, seq<byte>>)
  {
    MkfsModel.InitDiskContents(diskContents)
  }

  method Mkfs()
  returns (diskContents: map<uint64, seq<byte>>)
  {
    diskContents := MkfsImpl.Mkfs();
  }

  lemma InitialStateSatisfiesSystemInit(
      
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  {
    MkfsModel.InitialStateSatisfiesSystemInit(s, diskContents);
  }

  function SystemI(s: ADM.Variables) : ThreeStateVersionedMap.Variables
  {
    System_Ref.I(s)
  }

  lemma SystemRefinesCrashSafeMapInit(s: ADM.Variables)
  {
    System_Ref.RefinesInit(s);
  }

  lemma SystemRefinesCrashSafeMapNext(
    s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  {
    System_Ref.RefinesNext(s, s', uiop);
  }
}
