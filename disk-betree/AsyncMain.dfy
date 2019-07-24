include "MapSpec.dfy"
include "ThreeStateVersionedMap.dfy"
include "AsyncDiskModel.dfy"
include "../lib/NativeTypes.dfy"

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
  function ILBA(lba: LBA) : ADM.M.LBA

  predicate ValidSector(sector: Sector)

  function ISector(sector: Sector) : ADM.M.Sector
    requires ValidSector(sector)

  method InitState() returns (k: Constants, hs: HeapState)
    ensures Inv(k, hs)

  // DiskInterface

  function method BlockSize() : uint64 { 8*1024*1024 }

  type LBA = DiskTypes.LBA
  type Sector = DiskTypes.ByteSector

  type DiskOp = D.DiskOp<LBA, Sector>
  type ReqRead = D.ReqRead<LBA>
  type ReqWrite = D.ReqWrite<LBA, Sector>
  type RespRead = D.RespRead<Sector>
  type RespWrite = D.RespWrite

  predicate ValidReqRead(reqRead: ReqRead) { true }
  predicate ValidReqWrite(reqWrite: ReqWrite) { ValidSector(reqWrite.sector) }
  predicate ValidRespRead(respRead: RespRead) { ValidSector(respRead.sector) }
  predicate ValidRespWrite(respWrite: RespWrite) { true }
  predicate ValidDiskOp(dop: DiskOp)
  {
    match dop {
      case ReqReadOp(id, reqRead) => true
      case ReqWriteOp(id, reqWrite) => ValidSector(reqWrite.sector)
      case RespReadOp(id, respRead) => ValidSector(respRead.sector)
      case RespWriteOp(id, respWrite) => true
      case NoDiskOp => true
    }
  }

  class DiskIOHandler {
    method {:axiom} write(lba: LBA, sector: array<byte>) returns (id : D.ReqId)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    requires sector.Length == BlockSize() as int
    requires ValidSector(sector[..])
    ensures diskOp() == D.ReqWriteOp(id, D.ReqWrite(lba, sector[..]));

    method {:axiom} read(lba: LBA) returns (id: D.ReqId)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReqReadOp(id, D.ReqRead(lba))

    method {:axiom} getWriteResult() returns (id : D.ReqId)
    requires diskOp().RespWriteOp?
    ensures diskOp() == D.RespWriteOp(id, D.RespWrite)

    method {:axiom} getReadResult() returns (id : D.ReqId, sector: array<byte>)
    requires diskOp().RespReadOp?
    ensures sector.Length == BlockSize() as int
    ensures ValidSector(sector[..])
    ensures diskOp() == D.RespReadOp(id, D.RespRead(sector[..]))

    function {:axiom} diskOp() : DiskOp
    reads this
    ensures ValidDiskOp(diskOp())

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }

  function IReqRead(reqRead: ReqRead) : ADM.M.ReqRead
  requires ValidReqRead(reqRead)
  {
    D.ReqRead(ILBA(reqRead.lba))
  }
  function IReqWrite(reqWrite: ReqWrite) : ADM.M.ReqWrite
  requires ValidReqWrite(reqWrite)
  {
    D.ReqWrite(ILBA(reqWrite.lba), ISector(reqWrite.sector))
  }
  function IRespRead(respRead: RespRead) : ADM.M.RespRead
  requires ValidRespRead(respRead)
  {
    D.RespRead(ISector(respRead.sector))
  }
  function IRespWrite(respWrite: RespWrite) : ADM.M.RespWrite
  requires ValidRespWrite(respWrite)
  {
    D.RespWrite
  }

  function IDiskOp(diskOp: DiskOp) : ADM.M.DiskOp
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case ReqReadOp(id, reqRead) => D.ReqReadOp(id, IReqRead(reqRead))
      case ReqWriteOp(id, reqWrite) => D.ReqWriteOp(id, IReqWrite(reqWrite))
      case RespReadOp(id, respRead) => D.RespReadOp(id, IRespRead(respRead))
      case RespWriteOp(id, respWrite) => D.RespWriteOp(id, IRespWrite(respWrite))
      case NoDiskOp => D.NoDiskOp
    }
  }

  // Implementation of the state transitions

  /*
  method handleSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.SyncOp else UI.NoOp,
    IDiskOp(io.diskOp()))
  */

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespReadOp?
  requires Inv(k, hs)
  modifies HeapSet(hs)
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, IDiskOp(io.diskOp()))

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  requires io.diskOp().RespWriteOp?
  requires Inv(k, hs)
  modifies HeapSet(hs)
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs), UI.NoOp, IDiskOp(io.diskOp()))

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if v.Some? then UI.GetOp(key, v.value) else UI.NoOp,
    IDiskOp(io.diskOp()))

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, hs)
  modifies HeapSet(hs)
  modifies io
  ensures Inv(k, hs)
  ensures ValidDiskOp(io.diskOp())
  ensures ADM.M.Next(Ik(k), old(I(k, hs)), I(k, hs),
    if success then UI.PutOp(key, value) else UI.NoOp,
    IDiskOp(io.diskOp()))

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

  lemma SystemRefinesCrashSafeMapNext(
    k: ADM.Constants, s: ADM.Variables, s': ADM.Variables, uiop: ADM.UIOp)
  requires ADM.Inv(k, s)
  requires ADM.Next(k, s, s', uiop)
  ensures ADM.Inv(k, s')
  ensures ThreeStateVersionedMap.Next(SystemIk(k), SystemI(k, s), SystemI(k, s'), uiop)
}
