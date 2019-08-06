include "MapSpec.s.dfy"
include "ThreeStateVersionedMap.s.dfy"
include "AsyncDiskModel.s.dfy"
include "../lib/NativeTypes.s.dfy"

module DiskTypes {
  import opened NativeTypes
  type LBA = uint64
  type ByteSector = seq<byte>
}

abstract module Main {
  import ADM : AsyncDiskModel
  import D = AsyncDisk

  import MS = MapSpec
  import ThreeStateVersionedMap
  import opened NativeTypes
  import opened Options
  import DiskTypes
  import UI

  type UIOp = ADM.M.UIOp

  // impl defined stuff

  type Constants // impl defined
  type HeapState // impl defined (heap state)
  function HeapSet(hs: HeapState) : set<object>

  predicate Inv(k: Constants, hs: HeapState)
    reads HeapSet(hs)
  function Ik(k: Constants): ADM.M.Constants
  function I(k: Constants, hs: HeapState): ADM.M.Variables
    requires Inv(k, hs)
    reads HeapSet(hs)

  method InitState() returns (k: Constants, hs: HeapState)
    ensures Inv(k, hs)

  // DiskInterface

  class DiskIOHandler {
    method {:axiom} write(addr: uint64, bytes: array<byte>) returns (id : D.ReqId)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    ensures diskOp() == D.ReqWriteOp(id, D.ReqWrite(addr, bytes[..]));

    method {:axiom} read(addr: uint64, len: uint64) returns (id: D.ReqId)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReqReadOp(id, D.ReqRead(addr, len))

    method {:axiom} getWriteResult() returns (id : D.ReqId)
    requires diskOp().RespWriteOp?
    ensures diskOp() == D.RespWriteOp(id, D.RespWrite)

    method {:axiom} getReadResult() returns (id : D.ReqId, bytes: array<byte>)
    requires diskOp().RespReadOp?
    ensures diskOp() == D.RespReadOp(id, D.RespRead(bytes[..]))

    function {:axiom} diskOp() : D.DiskOp
    reads this

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }

  // Implementation of the state transitions

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: int)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.PushSyncOp(id), io.diskOp())

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: int)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
      if success then UI.PopSyncOp(id) else UI.NoOp,
      io.diskOp())

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespReadOp?
  requires Inv(k, hs)
  modifies HeapSet(hs)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp())

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires Inv(k, hs)
  modifies HeapSet(hs)
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, io.diskOp())

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
    io.diskOp())

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())

  // TODO add proof obligation that the InitState together with the initial disk state
  // from mkfs together refine to the initial state of the BlockCacheSystem.

  function SystemIk(k: ADM.Constants) : ThreeStateVersionedMap.Constants
  function SystemI(k: ADM.Constants, s: ADM.Variables) : ThreeStateVersionedMap.Variables
  requires ADM.Inv(k, s)

  lemma SystemRefinesCrashSafeMapInit(
    k: ADM.Constants, s: ADM.Variables)
  requires ADM.Init(k, s)
  ensures ADM.Inv(k, s)
  ensures ThreeStateVersionedMap.Init(SystemIk(k), SystemI(k, s))
  // TODO (jonh): is this an obligation for the refining module, or an unintentional axiom?

  lemma SystemRefinesCrashSafeMapNext(
    k: ADM.Constants, s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  requires ADM.Inv(k, s)
  requires ADM.Next(k, s, s', uiop)
  ensures ADM.Inv(k, s')
  ensures ThreeStateVersionedMap.Next(SystemIk(k), SystemI(k, s), SystemI(k, s'), uiop)
}
