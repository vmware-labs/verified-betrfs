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
    && (if hs.s.Ready? then (
        {hs.s.persistentIndirectionTable, hs.s.ephemeralIndirectionTable} +
        (if hs.s.frozenIndirectionTable.Some? then {hs.s.frozenIndirectionTable.value} else {}))
        else {}) <= HeapSet(hs)
    && IS.VariablesReadSet(hs.s) <= HeapSet(hs)
    && IS.Inv(k, hs.s)
  }

  function I(k: Constants, hs: HeapState) : ADM.M.Variables { IM.IVars(IS.IVars(hs.s)) }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    var s := IS.Unready(None, map[]);
    hs := new HeapState(s, {});

    BBC.InitImpliesInv(Ik(k), I(k, hs));
  }

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: int)
  {
    var s := hs.s;
    ImplModelSync.pushSyncCorrect(IS.Ic(k), IS.IVars(s));
    var s', id1 := pushSync(k, s);
    id := id1;
    var uiop := UI.PushSyncOp(id);
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.PushSyncOp(id), io.diskOp()); // observe
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: int)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := popSync(k, s, io, id);
    ImplModelSync.popSyncCorrect(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)), id, IS.IVars(s'), succ, IS.IIO(io));
    success := succ;
    var uiop := if succ then UI.PopSyncOp(id) else UI.NoOp;
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if success then UI.PopSyncOp(id) else UI.NoOp,
        io.diskOp());
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    var s := hs.s;
    var s', value := query(k, s, io, key);
    ImplModelQuery.queryCorrect(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)), key);
    var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    v := value;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
        io.diskOp());
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := insert(k, s, io, key, value);
    ImplModelInsert.insertCorrect(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)), key, value, IS.IVars(s'), succ, IS.IIO(io));
    var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    success := succ;
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), // observe
        if success then UI.PutOp(key, value) else UI.NoOp,
        io.diskOp());
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    var s' := ImplIO.readResponse(k, s, io);
    ImplModelIO.readResponseCorrect(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)));
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    var s' := ImplIO.writeResponse(k, s, io);
    ImplModelIO.writeResponseCorrect(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)));
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, old(IM.IVars(IS.IVars(s))), IM.IVars(IS.IVars(s')), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    hs.Repr := IS.VariablesReadSet(s');
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp()); // observe
  }
}
