include "../lib/Base/DebugAccumulator.i.dfy"
include "Main.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../ByteBlockCacheSystem/ByteBetreeBlockCacheSystem.i.dfy"
include "../ByteBlockCacheSystem/Marshalling.i.dfy"
include "InsertImpl.i.dfy"
include "QueryImpl.i.dfy"
include "SuccImpl.i.dfy"
include "InsertModel.i.dfy"
include "QueryModel.i.dfy"
include "SyncModel.i.dfy"
include "Mkfs.i.dfy"
include "../ByteBlockCacheSystem/ByteBetreeBlockCacheSystem_Refines_ThreeStateVersionedMap.i.dfy"
include "AllocationReport.i.dfy"
//
// Implements the application-API-handler obligations laid out by Main.s.dfy. TODO rename in a way that emphasizes that this is a module-refinement of the abstract Main that satisfies its obligations.
//

module {:compileName "MainHandlers"} MainHandlers refines Main { 
  import IndirectionTableModel
  import NodeImpl
  import DebugAccumulator
  import SM = StateModel
  import SI = StateImpl
  import IOImpl
  import opened EvictImpl // jonh hack
  import opened InsertImpl
  import opened QueryImpl
  import opened SyncImpl
  import opened SuccImpl
  import IOModel
  import InsertModel
  import QueryModel
  import SyncModel
  import SuccModel
  import MkfsImpl
  import MkfsModel

  import BBC = BetreeBlockCache
  import BC = BetreeGraphBlockCache
  import ADM = ByteBetreeBlockCacheSystem

  import System_Ref = ByteBetreeBlockCacheSystem_Refines_ThreeStateVersionedMap
  import AllocationReport

  type Constants = SI.ImplConstants
  type Variables = SI.ImplVariables

  function HeapSet(hs: HeapState) : set<object> { hs.Repr }

  predicate Inv(k: Constants, hs: HeapState)
  {
    // TODO this is gross, what can we do about it?
    && hs.s in HeapSet(hs)
    && (
        {hs.s.persistentIndirectionTable, hs.s.ephemeralIndirectionTable, hs.s.lru, hs.s.cache, hs.s.blockAllocator, hs.s.syncReqs} +
        (if hs.s.frozenIndirectionTable != null then {hs.s.frozenIndirectionTable} else {})
       ) <= HeapSet(hs)
    && hs.s.Repr() <= HeapSet(hs)
    && SI.Inv(k, hs.s)
  }

  function Ik(k: Constants) : ADM.M.Constants { BC.Constants() }
  function I(k: Constants, hs: HeapState) : ADM.M.Variables { SM.IVars(hs.s.I()) }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    var s := new Variables();
    hs := new HeapState(s, {});
    hs.Repr := s.Repr() + {s};
    assert Inv(k, hs);
    BBC.InitImpliesInv(Ik(k), I(k, hs));
  }

  lemma ioAndHsNotInReadSet(s: Variables, io: DiskIOHandler, hs: HeapState)
  requires s.W()
  ensures io !in s.Repr()
  ensures hs !in s.Repr()
  // TODO I think this should just follow from the types of the objects
  // in the Repr

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    SyncModel.pushSyncCorrect(SI.Ic(k), s.I());
    var id1 := pushSync(k, s);
    ioAndHsNotInReadSet(s, io, hs);
    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), uiop, io.diskOp()); // observe
  }

  // jonh hack UNVERIFIED DEBUG ONLY
  method handleEvictEverything(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    print "\nBefore\n";
    var acc := s.DebugAccumulate();
    DebugAccumulator.Display(acc, 0);
    var count:uint64 := s.cache.cache.Count;
//    var last_count:uint64 := count;
//    var last_at_this_count:uint64 = 0;
    while (count > 0) { // somehow it gets to where we can't get rid of the last few...?
      EvictOrDealloc(k, s, io);
      count := s.cache.cache.Count;
    }
    print "\nAfter\n";
    acc := s.DebugAccumulate();
    DebugAccumulator.Display(acc, 0);
    assume false;
  }

  // jonh hack UNVERIFIED DEBUG ONLY
  method handleCountAmassAllocations(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    AllocationReport.start();
    var s := hs.s;
    var table/*:MutableMap.ResizingHashMap*/ := s.ephemeralIndirectionTable.t;
    var iter := table.SimpleIterStart();
    var output := table.SimpleIterOutput(iter);
    while (!output.Done?) {
      var ref/*:IndirectionTableModel.Entry*/ := output.key;
      var nodeOpt/*:Option<NodeImpl.Node>*/ := s.cache.GetOpt(ref);
      if nodeOpt.Some? {
        var node:NodeImpl.Node := nodeOpt.value;
        var bi:uint64 := 0;
        while (bi < |node.buckets| as uint64) {
          var bucket := node.buckets[bi];
          AllocationReport.sampleBucket(ref, bucket);
          /*
          if (bucket.format.BFKvl?) {
            var kvl := bucket.kvl;
            var keys := kvl.keys;
            var messages := kvl.messages;
            // ship things off to C++ here?
            print "amassCount ", ref, " ", bi, " ", |keys|, " ", |messages|, "\n";
          }
          */
          bi := bi + 1;
        }
      }
      iter := table.SimpleIterInc(iter);
      output := table.SimpleIterOutput(iter);
    }
    AllocationReport.stop();
    assume false;
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: uint64)
  returns (wait: bool, success: bool)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var w, succ := popSync(k, s, io, id);
    SyncModel.popSyncCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), id, s.I(), succ, SI.IIO(io));
    ioAndHsNotInReadSet(s, io, hs);
    success := succ;
    wait := w;
    ghost var uiop := if succ then UI.PopSyncOp(id as int) else UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        uiop,
        io.diskOp());
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key)
  returns (v: Option<Value>)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var value := query(k, s, io, key);
    QueryModel.queryCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), key, s.I(), value, SI.IIO(io));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    v := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var succ := insert(k, s, io, key, value);
    InsertModel.insertCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), key, value, s.I(), succ, SI.IIO(io));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    success := succ;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleSucc(k: Constants, hs: HeapState, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (res: Option<UI.SuccResultList>)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var value := doSucc(k, s, io, start, maxToFind);
    SuccModel.doSuccCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), start, maxToFind as int);
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := 
      if value.Some? then UI.SuccOp(start, value.value.results, value.value.end) else UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    res := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        uiop,
        io.diskOp());
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    IOImpl.readResponse(k, s, io);
    IOModel.readResponseCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    IOImpl.writeResponse(k, s, io);
    IOModel.writeResponseCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
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
