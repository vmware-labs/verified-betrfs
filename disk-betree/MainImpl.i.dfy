include "Main.s.dfy"

include "../lib/Sets.i.dfy"
include "ByteBetreeBlockCacheSystem.i.dfy"
include "Marshalling.i.dfy"

include "Impl.i.dfy"
include "ImplDo.i.dfy"

module {:extern} MainImpl refines Main { 

  import opened Impl
  import opened ImplDo

  //  ---   dep graph   ---
  //
  //       MainImpl
  //      /       \
  //    ImplDo    |
  //      |  \----+
  //      |       |
  //   ImplSync   |
  //      |       |
  //      \---+---/
  //          |
  //        Impl

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
    var s := hs.s;
    var s', id1 := pushSync(k, s, io);
    assert IS.WFVars(s');
    id := id1;
    var uiop := UI.PushSyncOp(id);
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    assert BC.Inv(k, IS.IVars(s'));
    if s'.Ready? {
      s'.persistentIndirectionTable.InvImpliesRepr();
      s'.ephemeralIndirectionTable.InvImpliesRepr();
      if s'.frozenIndirectionTable.Some? {
        s'.frozenIndirectionTable.value.InvImpliesRepr();
      }
    }
    // NOALIAS this could be unnecessary with statically enforced no-aliasing
    assert hs !in IS.VariablesReadSet(s');
    ghost var olds' := IS.IVars(s');
    label Here: assert true;
    assert olds' == IS.IVars(s');
    hs.s := s';
    assert olds' == IS.IVars(s');
    assert hs.s == old@Here(s');
    assert IS.IVars(s') == IS.IVars(old@Here(s'));
    assert BC.Inv(k, IS.IVars(s'));
    assert IS.IVars(hs.s) == IS.IVars(s');
    assert BC.Inv(k, IS.IVars(hs.s));
    assert BBC.Inv(k, IS.IVars(hs.s));
    assert Inv(k, hs);
    // assert ImplADM.M.NextStep(Ik(k), old(I(k, hs)), I(k, hs), UI.PushSyncOp(id), io.diskOp(), _);
    assume ImplADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.PushSyncOp(id), io.diskOp());
    assert ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.PushSyncOp(id), io.diskOp());
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
