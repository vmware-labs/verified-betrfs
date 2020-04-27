include "DiskOpModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../ByteBlockCacheSystem/ByteCache.i.dfy"

// TODO a better name might be IOImpl, but that's already
// taken. TODO rename that other thing, then rename this.

module DiskOpImpl {
  import DiskOpModel
  import ByteCache
  import opened MainDiskIOHandler

  type ImplConstants = ByteCache.Constants

  function Ic(k: ImplConstants) : DiskOpModel.Constants
  {
    DiskOpModel.Constants()
  }

  function IIO(io: DiskIOHandler) : DiskOpModel.IO
  reads io
  {
    match io.diskOp() {
      case NoDiskOp => DiskOpModel.IOInit(io.reservedId(), io.reservedId2())
      case ReqReadOp(id, reqRead) => DiskOpModel.IOReqRead(id, reqRead)
      case ReqWriteOp(id, reqWrite) => DiskOpModel.IOReqWrite(id, reqWrite)
      case ReqWrite2Op(id1, id2, reqWrite1, reqWrite2) => DiskOpModel.IOReqWrite2(id1, id2, reqWrite1, reqWrite2)
      case RespReadOp(id, respRead) => DiskOpModel.IORespRead(id, respRead)
      case RespWriteOp(id, respWrite) => DiskOpModel.IORespWrite(id, respWrite)
    }
  }
}
