include "Main.s.dfy"

include "../lib/Sets.i.dfy"
include "ByteBetreeBlockCacheSystem.i.dfy"
include "Marshalling.i.dfy"

include "Impl.i.dfy"
include "ImplInsert.i.dfy"
include "ImplQuery.i.dfy"
include "ImplModelInsert.i.dfy"
include "ImplModelQuery.i.dfy"
include "ImplModelSync.i.dfy"

module {:extern} MainImpl refines Main { 
  import opened Impl
  import IM = ImplModel
  import ImplIO
  import opened ImplInsert
  import opened ImplQuery
  import opened ImplSync
  import ImplModelIO
  import ImplModelInsert
  import ImplModelQuery
  import ImplModelSync

  import ADM = Impl.ImplADM

  type Constants = ImplConstants
  type Variables = ImplVariables

  function HeapSet(hs: HeapState) : set<object> { hs.Repr }

  predicate Inv(k: Constants, hs: HeapState)
  {
    // TODO this is gross, what can we do about it?
    && hs.s in HeapSet(hs)
    && (
        {hs.s.persistentIndirectionTable, hs.s.ephemeralIndirectionTable, hs.s.lru, hs.s.cache, hs.s.blockAllocator} +
        (if hs.s.frozenIndirectionTable != null then {hs.s.frozenIndirectionTable} else {})
       ) <= HeapSet(hs)
    && hs.s.Repr() <= HeapSet(hs)
    && IS.Inv(k, hs.s)
  }

  function I(k: Constants, hs: HeapState) : ADM.M.Variables { IM.IVars(hs.s.I()) }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    var s := new Variables();
    hs := new HeapState(s, {});
    hs.Repr := s.Repr() + {s};
    assert Inv(k, hs);
    BBC.InitImpliesInv(Ik(k), I(k, hs));
  }

  lemma ioAndHsNotInReadSet(s: ImplVariables, io: DiskIOHandler, hs: HeapState)
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
    ImplModelSync.pushSyncCorrect(IS.Ic(k), s.I());
    var id1 := pushSync(k, s);
    ioAndHsNotInReadSet(s, io, hs);
    id := id1;
    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), uiop, io.diskOp()); // observe
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: uint64)
  returns (wait: bool, success: bool)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var w, succ := popSync(k, s, io, id);
    ImplModelSync.popSyncCorrect(IS.Ic(k), old(s.I()), old(IS.IIO(io)), id, s.I(), succ, IS.IIO(io));
    ioAndHsNotInReadSet(s, io, hs);
    success := succ;
    wait := w;
    ghost var uiop := if succ then UI.PopSyncOp(id as int) else UI.NoOp;
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        uiop,
        io.diskOp());
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var value := query(k, s, io, key);
    ImplModelQuery.queryCorrect(IS.Ic(k), old(s.I()), old(IS.IIO(io)), key);
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    v := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    var succ := insert(k, s, io, key, value);
    ImplModelInsert.insertCorrect(IS.Ic(k), old(s.I()), old(IS.IIO(io)), key, value, s.I(), succ, IS.IIO(io));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    success := succ;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    ImplIO.readResponse(k, s, io);
    ImplModelIO.readResponseCorrect(IS.Ic(k), old(s.I()), old(IS.IIO(io)));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    ioAndHsNotInReadSet(s, io, hs);
    ImplIO.writeResponse(k, s, io);
    ImplModelIO.writeResponseCorrect(IS.Ic(k), old(s.I()), old(IS.IIO(io)));
    ioAndHsNotInReadSet(s, io, hs);
    ghost var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IM.IVars(old(s.I())), IM.IVars(s.I()), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.Repr := s.Repr() + {s};
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }
}
