include "Main.dfy"

include "../lib/Sets.dfy"
include "ByteBetreeBlockCacheSystem.dfy"
include "Marshalling.dfy"

include "Impl.dfy"
include "ImplDo.dfy"

module {:extern} MainImpl refines Main { 

  import opened Impl
  import opened ImplDo

  import ADM = Impl.ImplADM

  type Constants = ImplConstants
  type Variables = ImplVariables

  type HeapState = IS.ImplHeapState

  function HeapSet(hs: HeapState) : set<object> { IS.ImplHeapSet(hs) }

  predicate Inv(k: Constants, hs: HeapState)
  {
    && IS.WFVars(hs.s)
    && BBC.Inv(k, IS.IVars(hs.s))
  }

  function I(k: Constants, hs: HeapState) : ADM.M.Variables { IS.IVars(hs.s) }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    hs := new IS.ImplHeapState();

    BBC.InitImpliesInv(k, IS.IVars(hs.s));
  }

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: int)
  {
    assume false; // TODO
    var s := hs.s;
    var s', id1 := pushSync(k, s, io);
    id := id1;
    var uiop := UI.PushSyncOp(id);
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: int)
  returns (success: bool)
  {
    assume false; // TODO
    var s := hs.s;
    var s', succ := popSync(k, s, io, id);
    success := succ;
    var uiop := if succ then UI.PopSyncOp(id) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    assume false; // TODO
    var s := hs.s;
    var s', value := query(k, s, io, key);
    var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    v := value;
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    assume false; // TODO
    var s := hs.s;
    var s', succ := insert(k, s, io, key, value);
    var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    assume false; // TODO
    var s := hs.s;
    var s' := readResponse(k, s, io);
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    assume false; // TODO
    var s := hs.s;
    var s' := writeResponse(k, s, io);
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }
}
