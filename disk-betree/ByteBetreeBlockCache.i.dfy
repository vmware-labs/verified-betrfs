include "AsyncDiskModel.s.dfy"
include "BetreeBlockCache.i.dfy"
include "Marshalling.i.dfy"
include "ImplState.i.dfy"

module ByteBetreeBlockCache refines AsyncDiskMachine {
  import opened NativeTypes
  import opened Options

  import BBC = BetreeBlockCache
  import Marshalling
  import IS = ImplState

  import SD = AsyncSectorDisk
  import LBAType`Internal

  type Constants = BBC.Constants
  type Variables = BBC.Variables

  function method BlockSize() : int { 8 * 1024 * 1024 }

  predicate ValidAddr(addr: uint64)
  {
    LBAType.ValidAddr(addr)
  }

  predicate ValidBytes(sector: seq<byte>)
  {
    && |sector| == BlockSize()
    && Marshalling.parseSector(sector).Some?
  }

  function IBytes(sector: seq<byte>) : BBC.Sector
  requires ValidBytes(sector)
  {
    IS.ISector(Marshalling.parseSector(sector).value)
  }

  function IBytesOpt(sector: seq<byte>) : Option<BBC.Sector>
  {
    if ValidBytes(sector) then
      Some(IBytes(sector))
    else
      None
  }

  predicate ValidReqRead(reqRead: D.ReqRead) { ValidAddr(reqRead.addr) && reqRead.len as int == BlockSize() }
  predicate ValidReqWrite(reqWrite: D.ReqWrite) { ValidAddr(reqWrite.addr) && ValidBytes(reqWrite.bytes) }
  predicate ValidRespRead(respRead: D.RespRead) { true }
  predicate ValidRespWrite(respWrite: D.RespWrite) { true }
  predicate ValidDiskOp(dop: D.DiskOp)
  {
    match dop {
      case ReqReadOp(id, reqRead) => ValidReqRead(reqRead)
      case ReqWriteOp(id, reqWrite) => ValidReqWrite(reqWrite)
      case RespReadOp(id, respRead) => ValidRespRead(respRead)
      case RespWriteOp(id, respWrite) => ValidRespWrite(respWrite)
      case NoDiskOp => true
    }
  }

  function IReqRead(reqRead: D.ReqRead) : SD.ReqRead<BBC.LBA>
  requires ValidReqRead(reqRead)
  {
    SD.ReqRead(reqRead.addr)
  }
  function IReqWrite(reqWrite: D.ReqWrite) : SD.ReqWrite<BBC.LBA, BBC.Sector>
  requires ValidReqWrite(reqWrite)
  {
    SD.ReqWrite(reqWrite.addr, IBytes(reqWrite.bytes))
  }
  function IRespRead(respRead: D.RespRead) : SD.RespRead<BBC.Sector>
  {
    SD.RespRead(IBytesOpt(respRead.bytes))
  }
  function IRespWrite(respWrite: D.RespWrite) : SD.RespWrite
  requires ValidRespWrite(respWrite)
  {
    SD.RespWrite
  }

  function IDiskOp(diskOp: D.DiskOp) : SD.DiskOp<BBC.LBA, BBC.Sector>
  requires ValidDiskOp(diskOp)
  {
    match diskOp {
      case ReqReadOp(id, reqRead) => SD.ReqReadOp(id, IReqRead(reqRead))
      case ReqWriteOp(id, reqWrite) => SD.ReqWriteOp(id, IReqWrite(reqWrite))
      case RespReadOp(id, respRead) => SD.RespReadOp(id, IRespRead(respRead))
      case RespWriteOp(id, respWrite) => SD.RespWriteOp(id, IRespWrite(respWrite))
      case NoDiskOp => SD.NoDiskOp
    }
  }

  predicate Init(k: Constants, s: Variables)
  {
    BBC.Init(k, s)
  }

  datatype Step = Step(step: BBC.Step)

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: Step)
  {
    && ValidDiskOp(dop)
    && BBC.NextStep(k, s, s', uiop, IDiskOp(dop), step.step)
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    exists step :: NextStep(k, s, s', uiop, dop, step)
  }
}
