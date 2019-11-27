// DiskInterface

include "../lib/Base/NativeTypes.s.dfy"
include "../BlockCacheSystem/AsyncDiskModel.s.dfy"

module {:extern} MainDiskIOHandler {
  import opened NativeTypes
  import D = AsyncDisk

  class {:extern} DiskIOHandler {
    method {:axiom} write(addr: uint64, bytes: array<byte>) returns (id : D.ReqId)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    ensures diskOp() == D.ReqWriteOp(id, D.ReqWrite(addr, bytes[..]));
    ensures id == old(reservedId())

    method {:axiom} read(addr: uint64, len: uint64) returns (id: D.ReqId)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReqReadOp(id, D.ReqRead(addr, len))
    ensures id == old(reservedId())

    method {:axiom} getWriteResult() returns (id : D.ReqId)
    requires diskOp().RespWriteOp?
    ensures diskOp() == D.RespWriteOp(id, D.RespWrite)

    method {:axiom} getReadResult() returns (id : D.ReqId, bytes: seq<byte>)
    requires diskOp().RespReadOp?
    ensures diskOp() == D.RespReadOp(id, D.RespRead(bytes))
    ensures |bytes| < 0x1_0000_0000_0000_0000

    function {:axiom} diskOp() : D.DiskOp
    reads this

    function {:axiom} reservedId() : D.ReqId
    reads this

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }
}
