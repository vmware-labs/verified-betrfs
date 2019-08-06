// DiskInterface

include "../lib/NativeTypes.dfy"
include "AsyncDiskModel.dfy"

module MainDiskIOHandler {
  import opened NativeTypes
  import D = AsyncDisk

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
}
