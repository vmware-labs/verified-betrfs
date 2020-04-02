include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../BlockCacheSystem/BlockJournalCache.i.dfy"

module DiskOpModel {
  import D = AsyncDisk
  import opened NativeTypes
  import BJC = BlockJournalCache
  import BC = BlockCache
  import JC = JournalCache

  datatype Constants = Constants()

  function Ik(k: Constants) : BJC.Constants
  {
    BJC.Constants(BC.Constants(), JC.Constants())
  }

  // Functional model of the DiskIOHandler

  datatype IO =
    | IOInit(id: uint64, id2: uint64)
    | IOReqRead(id: uint64, reqRead: D.ReqRead)
    | IOReqWrite(id: uint64, reqWrite: D.ReqWrite)
    | IOReqWrite2(id: uint64, id2: uint64, reqWrite1: D.ReqWrite, reqWrite2: D.ReqWrite)
    | IORespRead(id: uint64, respRead: D.RespRead)
    | IORespWrite(id: uint64, respWrite: D.RespWrite)

  function diskOp(io: IO) : D.DiskOp {
    match io {
      case IOInit(id, id2) => D.NoDiskOp
      case IOReqRead(id, reqRead) => D.ReqReadOp(id, reqRead)
      case IOReqWrite(id, reqWrite) => D.ReqWriteOp(id, reqWrite)
      case IOReqWrite2(id1, id2, reqWrite1, reqWrite2) => D.ReqWrite2Op(id1, id2, reqWrite1, reqWrite2)
      case IORespRead(id, respRead) => D.RespReadOp(id, respRead)
      case IORespWrite(id, respWrite) => D.RespWriteOp(id, respWrite)
    }
  }
}
