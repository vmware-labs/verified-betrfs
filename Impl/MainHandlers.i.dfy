include "Main.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "CoordinationImpl.i.dfy"
include "HandleReadResponseImpl.i.dfy"
include "HandleWriteResponseImpl.i.dfy"
include "Mkfs.i.dfy"

//
// Implements the application-API-handler obligations laid out by Main.s.dfy. TODO rename in a way that emphasizes that this is a module-refinement of the abstract Main that satisfies its obligations.
//

module {:extern} MainHandlers refines Main { 
  import SM = StateModel
  import SI = StateImpl
  import CoordinationModel
  import CoordinationImpl
  import HandleReadResponseImpl
  import HandleReadResponseModel
  import HandleWriteResponseImpl
  import HandleWriteResponseModel
  import FullImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import MkfsImpl
  import MkfsModel

  import BBC = BetreeCache
  import BC = BlockCache
  import ADM = ByteSystem

  import System_Ref = ByteBetreeBlockCacheSystem_Refines_ThreeStateVersionedMap

  type Constants = ImplConstants
  type Variables = FullImpl.Full

  function HeapSet(hs: HeapState) : set<object> { hs.Repr }

  predicate Inv(k: Constants, hs: HeapState)
  {
    && hs.s in HeapSet(hs)
    && hs.s.Repr <= HeapSet(hs)
    && hs.s.Inv(k)
  }

  function Ik(k: Constants) : ADM.M.Constants { BC.Constants() }
  function I(k: Constants, hs: HeapState) : ADM.M.Variables {
    SM.IVars(hs.s.I())
  }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    var s := new Variables();
    hs := new HeapState(s, {});
    hs.Repr := s.Repr() + {s};
    assert Inv(k, hs);
    BBC.InitImpliesInv(Ik(k), I(k, hs));
  }

  lemma ioAndHsNotInReadSet(s: Full, io: DiskIOHandler, hs: HeapState)
  requires s.W()
  ensures io !in s.Repr
  ensures hs !in s.Repr
  // TODO I think this should just follow from the types of the objects
  // in the Repr

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: uint64)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    CoordinatorModel.pushSyncCorrect(SI.Ic(k), s.I());
    var id1 := CoordinatorImpl.pushSync(k, s);
    ioAndHsNotInReadSet(s, io, hs);
    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    BBC.NextPreservesInv(k, SM.IVars(old(s.I())), SM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), uiop, io.diskOp()); // observe
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: uint64)
  returns (wait: bool, success: bool)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var w, succ := CoordinatorImpl.popSync(k, s, io, id);
    CoordinatorModel.popSyncCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), id, s.I(), succ, SI.IIO(io));
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
    var value := CoordinatorImpl.query(k, s, io, key);
    CoordinatorModel.queryCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), key, s.I(), value, SI.IIO(io));
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
    var succ := CoordinatorImpl.insert(k, s, io, key, value);
    CoordinatorModel.insertCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), key, value, s.I(), succ, SI.IIO(io));
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
    var value := CoordinatorImpl.doSucc(k, s, io, start, maxToFind);
    CoordinatorModel.doSuccCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)), start, maxToFind as int);
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
    HandleReadResponseImpl.readResponse(k, s, io);
    HandleReadResponseModel.readResponseCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)));
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
    HandleWriteResponseImpl.writeResponse(k, s, io);
    HandleWriteResponseModel.writeResponseCorrect(SI.Ic(k), old(s.I()), old(SI.IIO(io)));
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
