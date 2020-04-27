// DiskInterface

include "../lib/Base/NativeTypes.s.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"

module {:extern "MainDiskIOHandler_Compile"} MainDiskIOHandler {
  import opened NativeTypes
  import D = AsyncDisk

  class {:extern} DiskIOHandler {
    method {:extern "MainDiskIOHandler_Compile", "write"} 
    write(addr: uint64, bytes: seq<byte>) returns (id : D.ReqId)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    ensures diskOp() == D.ReqWriteOp(id, D.ReqWrite(addr, bytes));
    ensures id == old(reservedId())

    method {:extern "MainDiskIOHandler_Compile", "write2"} 
    write2(addr1: uint64, bytes1: seq<byte>,
           addr2: uint64, bytes2: seq<byte>)
    returns (id : D.ReqId, id2: D.ReqId)
    modifies this;
    requires diskOp() == D.NoDiskOp;
    ensures diskOp() == D.ReqWrite2Op(id, id2, D.ReqWrite(addr1, bytes1), D.ReqWrite(addr2, bytes2));
    ensures id == old(reservedId())
    ensures id2 == old(reservedId2())

    method {:extern "MainDiskIOHandler_Compile", "read"} 
    read(addr: uint64, len: uint64) returns (id: D.ReqId)
    modifies this
    requires diskOp() == D.NoDiskOp
    ensures diskOp() == D.ReqReadOp(id, D.ReqRead(addr, len))
    ensures id == old(reservedId())

    method {:extern "MainDiskIOHandler_Compile", "getWriteResult"} 
    getWriteResult() returns (id : D.ReqId, addr: uint64, len: uint64)
    requires diskOp().RespWriteOp?
    ensures diskOp() == D.RespWriteOp(id, D.RespWrite(addr, len))

    method {:extern "MainDiskIOHandler_Compile", "getReadResult"} 
    getReadResult() returns (id : D.ReqId, addr: uint64, bytes: seq<byte>)
    requires diskOp().RespReadOp?
    ensures diskOp() == D.RespReadOp(id, D.RespRead(addr, bytes))
    ensures |bytes| < 0x1_0000_0000_0000_0000

    function {:axiom} diskOp() : D.DiskOp
    reads this

    function {:axiom} reservedId() : D.ReqId
    reads this

    function {:axiom} reservedId2() : D.ReqId
    reads this
    ensures reservedId2() != reservedId()

    predicate initialized()
    reads this
    {
      diskOp() == D.NoDiskOp
    }
  }
}
