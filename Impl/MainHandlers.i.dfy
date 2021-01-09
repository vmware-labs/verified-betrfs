include "../lib/Base/DebugAccumulator.i.dfy"
include "Main.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "CoordinationImpl.i.dfy"
include "HandleReadResponseImpl.i.dfy"
include "HandleWriteResponseImpl.i.dfy"
include "Mkfs.i.dfy"
include "CoordinationModel.i.dfy"
include "AllocationReport.i.dfy"
include "../ByteBlockCacheSystem/ByteSystem_Refines_ThreeStateVersionedMap.i.dfy"

//
// Implements the application-API-handler obligations laid out by Main.s.dfy. TODO rename in a way that emphasizes that this is a module-refinement of the abstract Main that satisfies its obligations.
//

module MainHandlers refines Main { 
  import DebugAccumulator
  import DOM = DiskOpModel
  import SM = StateModel
  import SI = StateBCImpl
  import opened EvictImpl // (jonh) only used for unverified debug hooks
  import CoordinationImpl
  import HandleReadResponseImpl
  import HandleReadResponseModel
  import HandleWriteResponseImpl
  import HandleWriteResponseModel
  import CoordinationModel
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

  import System_Ref = ByteSystem_Refines_ThreeStateVersionedMap
  import AllocationReport

  type Variables = FullImpl.Full

  function HeapSet(hs: HeapState) : set<object> { hs.Repr }

  predicate Inv(hs: HeapState)
  {
    && hs.s in HeapSet(hs)
    && hs.s.Repr <= HeapSet(hs)
    && hs.s.Inv()
    && hs !in hs.s.Repr
  }

  function I(hs: HeapState) : ADM.M.Variables {
    SM.IVars(hs.s.I())
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

  method InitState() returns (hs: HeapState)
    // conditions inherited:
    //ensures Inv(hs)
    //ensures ADM.M.Init(I(hs))
  {
    PrintMetadata();
    var s := new Variables();
    hs := new HeapState(s, {});
    hs.Repr := s.Repr + {s};
    assert Inv(hs);
    BlockJournalCache.InitImpliesInv(I(hs));
  }

  ////////// Top-level handlers

  method handlePushSync(hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  {
    var s := hs.s;
    var id1 := CoordinationImpl.pushSync(s);

    CoordinationModel.pushSyncCorrect(old(s.I()));

    //assert ADM.M.Next(SM.IVars(old(s.I())), SM.IVars(s.I()),
    //   if id1 == 0 then UI.NoOp else UI.PushSyncOp(id1 as int),
    //   D.NoDiskOp);

    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    //assert SM.Inv(hs.s.I());
    //assert hs.s.Inv();
    //assert Inv(hs);
    assert ADM.M.Next(old(I(hs)), I(hs), uiop, io.diskOp()); // observe
  }

  // (jonh) unverified debug hook: Note "requires false" which prevents calling
  // this hook from any real handler code. It's only reachable from hooks
  // in the trusted benchmark driver; we used it to diagnose memory leaks.
  method handleEvictEverything(hs: HeapState, io: DiskIOHandler)
  requires false
  {
    var s := hs.s;
    print "\nBefore\n";
    // var acc := s.bc.DebugAccumulate();
    // DebugAccumulator.Display(acc, 0);

    // var count:uint64 := s.bc.cache.cache.Count;
    var count:uint64 := s.bc.cache.Count(); // [yizhou7][REVIEW]: replace the above to this

//    var last_count:uint64 := count;
//    var last_at_this_count:uint64 = 0;
    while (count > 0)
    { // somehow it gets to where we can't get rid of the last few...?
      EvictOrDealloc(s.bc, io);
      // count := s.bc.cache.cache.Count;
      count := s.bc.cache.Count(); // [yizhou7][REVIEW]: replace the above to this
    }
    print "\nAfter\n";
    // acc := s.bc.DebugAccumulate();
    // DebugAccumulator.Display(acc, 0);
  }

  // (jonh) unverified debug hook: Note "requires false" which prevents calling
  // this hook from any real handler code. It's only reachable from hooks
  // in the trusted benchmark driver; we used it to diagnose memory leaks.
  method handleCountAmassAllocations(hs: HeapState, io: DiskIOHandler)
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

  method handlePopSync(hs: HeapState, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (wait: bool, success: bool)
  {
    var s := hs.s;
    var succ, w := CoordinationImpl.popSync(s, io, id, graphSync);
    CoordinationModel.popSyncCorrect(old(s.I()), old(IIO(io)), id, graphSync, s.I(), IIO(io), succ);
    success := succ;
    wait := w;
    ghost var uiop := if succ then UI.PopSyncOp(id as int) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(old(I(hs)), I(hs), // observe
        uiop,
        io.diskOp());
  }

  method handleQuery(hs: HeapState, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  {
    var s := hs.s;
    var value := CoordinationImpl.query(s, io, key);
    CoordinationModel.queryCorrect(old(s.I()), old(IIO(io)), key, s.I(), value, IIO(io));
    ghost var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    v := value;
    assert ADM.M.Next(old(I(hs)), I(hs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(hs: HeapState, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  {
    var s := hs.s;
    var succ := CoordinationImpl.insert(s, io, key, value);
    CoordinationModel.insertCorrect(old(s.I()), old(IIO(io)), key, value, s.I(), succ, IIO(io));
    ghost var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    success := succ;
    assert ADM.M.Next(old(I(hs)), I(hs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleSucc(hs: HeapState, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  {
    var s := hs.s;
    var value := CoordinationImpl.succ(s, io, start, maxToFind);
    CoordinationModel.succCorrect(old(s.I()), old(IIO(io)), start, maxToFind as int, s.I(), value, IIO(io));
    ghost var uiop := 
      if value.Some? then UI.SuccOp(start, value.value.results, value.value.end) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    res := value;
    assert ADM.M.Next(old(I(hs)), I(hs), // observe
        uiop,
        io.diskOp());
  }

  method handleReadResponse(hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    HandleReadResponseImpl.readResponse(s, io);
    HandleReadResponseModel.readResponseCorrect(old(s.I()), old(IIO(io)));
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(old(I(hs)), I(hs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    HandleWriteResponseImpl.writeResponse(s, io);
    HandleWriteResponseModel.writeResponseCorrect(old(s.I()), old(IIO(io)));
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(old(I(hs)), I(hs), UI.NoOp, io.diskOp()); // observe
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

  lemma SystemRefinesCrashSafeMapInit(
    s: ADM.Variables)
  {
    System_Ref.RefinesInit(s);
  }

  lemma SystemRefinesCrashSafeMapNext(
    s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  {
    System_Ref.RefinesNext(s, s', uiop);
  }
}
