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
  import SI = StateImpl
  import opened EvictImpl // jonh hack
  import CoordinationImpl
  import HandleReadResponseImpl
  import HandleReadResponseModel
  import HandleWriteResponseImpl
  import HandleWriteResponseModel
  import CoordinationModel
  import FullImpl
  import MkfsImpl
  import MkfsModel
  import Bounds  // jonh hack for metadata recording

  import BlockJournalCache
  import BBC = BetreeCache
  import BC = BlockCache
  import JC = JournalCache
  import ADM = ByteSystem

  import opened DiskOpImpl
  import opened InterpretationDiskOps

  import System_Ref = ByteSystem_Refines_ThreeStateVersionedMap
  import AllocationReport

  type Constants = ImplConstants
  type Variables = FullImpl.Full

  function HeapSet(hs: HeapState) : set<object> { hs.Repr }

  predicate Inv(k: Constants, hs: HeapState)
  {
    && hs.s in HeapSet(hs)
    && hs.s.Repr <= HeapSet(hs)
    && hs.s.Inv(k)
    && hs !in hs.s.Repr
  }

  function Ik(k: Constants) : ADM.M.Constants {
    BlockJournalCache.Constants(BC.Constants(), JC.Constants())
  }
  function I(k: Constants, hs: HeapState) : ADM.M.Variables {
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

  method InitState() returns (k: Constants, hs: HeapState)
    // conditions inherited:
    //ensures Inv(k, hs)
    //ensures ADM.M.Init(Ik(k), I(k, hs))
  {
    PrintMetadata();
    var s := new Variables(k);
    hs := new HeapState(s, {});
    hs.Repr := s.Repr + {s};
    assert Inv(k, hs);
    BlockJournalCache.InitImpliesInv(Ik(k), I(k, hs));
  }

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  {
    var s := hs.s;
    var id1 := CoordinationImpl.pushSync(k, s);

    CoordinationModel.pushSyncCorrect(Ic(k), old(s.I()));

    //assert ADM.M.Next(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()),
    //   if id1 == 0 then UI.NoOp else UI.PushSyncOp(id1 as int),
    //   D.NoDiskOp);

    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    //assert SM.Inv(Ic(k), hs.s.I());
    //assert hs.s.Inv(k);
    //assert Inv(k, hs);
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), uiop, io.diskOp()); // observe
  }

  // jonh hack UNVERIFIED DEBUG ONLY
  method handleEvictEverything(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires false
  {
    var s := hs.s;
    print "\nBefore\n";
    var acc := s.bc.DebugAccumulate();
    DebugAccumulator.Display(acc, 0);
    var count:uint64 := s.bc.cache.cache.Count;
//    var last_count:uint64 := count;
//    var last_at_this_count:uint64 = 0;
    while (count > 0)
    { // somehow it gets to where we can't get rid of the last few...?
      EvictOrDealloc(k, s.bc, io);
      count := s.bc.cache.cache.Count;
    }
    print "\nAfter\n";
    acc := s.bc.DebugAccumulate();
    DebugAccumulator.Display(acc, 0);
  }

  // jonh hack UNVERIFIED DEBUG ONLY
  method handleCountAmassAllocations(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires false
  {
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
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (wait: bool, success: bool)
  {
    var s := hs.s;
    var succ, w := CoordinationImpl.popSync(k, s, io, id, graphSync);
    CoordinationModel.popSyncCorrect(Ic(k), old(s.I()), old(IIO(io)), id, graphSync, s.I(), IIO(io), succ);
    success := succ;
    wait := w;
    ghost var uiop := if succ then UI.PopSyncOp(id as int) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        uiop,
        io.diskOp());
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  {
    var s := hs.s;
    var value := CoordinationImpl.query(k, s, io, key);
    CoordinationModel.queryCorrect(Ic(k), old(s.I()), old(IIO(io)), key, s.I(), value, IIO(io));
    ghost var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    v := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  {
    var s := hs.s;
    var succ := CoordinationImpl.insert(k, s, io, key, value);
    CoordinationModel.insertCorrect(Ic(k), old(s.I()), old(IIO(io)), key, value, s.I(), succ, IIO(io));
    ghost var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    success := succ;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleSucc(k: Constants, hs: HeapState, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  {
    var s := hs.s;
    var value := CoordinationImpl.succ(k, s, io, start, maxToFind);
    CoordinationModel.succCorrect(Ic(k), old(s.I()), old(IIO(io)), start, maxToFind as int, s.I(), value, IIO(io));
    ghost var uiop := 
      if value.Some? then UI.SuccOp(start, value.value.results, value.value.end) else UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    res := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        uiop,
        io.diskOp());
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    HandleReadResponseImpl.readResponse(k, s, io);
    HandleReadResponseModel.readResponseCorrect(Ic(k), old(s.I()), old(IIO(io)));
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    HandleWriteResponseImpl.writeResponse(k, s, io);
    HandleWriteResponseModel.writeResponseCorrect(Ic(k), old(s.I()), old(IIO(io)));
    ghost var uiop := UI.NoOp;
    if ValidDiskOp(io.diskOp()) {
      BlockJournalCache.NextPreservesInv(DOM.Ik(Ic(k)), SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, IDiskOp(io.diskOp()));
    }
    hs.Repr := s.Repr + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
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
      k: ADM.Constants, 
      s: ADM.Variables,
      diskContents: map<uint64, seq<byte>>)
  {
    MkfsModel.InitialStateSatisfiesSystemInit(k, s, diskContents);
  }

  function SystemIk(k: ADM.Constants) : ThreeStateVersionedMap.Constants
  {
    System_Ref.Ik(k)
  }

  function SystemI(k: ADM.Constants, s: ADM.Variables) : ThreeStateVersionedMap.Variables
  {
    System_Ref.I(k, s)
  }

  lemma SystemRefinesCrashSafeMapInit(
    k: ADM.Constants, s: ADM.Variables)
  {
    System_Ref.RefinesInit(k, s);
  }

  lemma SystemRefinesCrashSafeMapNext(
    k: ADM.Constants, s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  {
    System_Ref.RefinesNext(k, s, s', uiop);
  }
}
