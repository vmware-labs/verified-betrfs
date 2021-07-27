include "../../lib/Lang/NativeTypes.s.dfy"
include "ArrayPtr.s.dfy"

abstract module AIOParams {
  import opened Ptrs
  type ReadPermission(!new)

  predicate is_read_perm(rp: ReadPermission, ptr: Ptr, data: seq<byte>)

  glinear method get_read_perm(
      gshared rp: ReadPermission, ghost ptr: Ptr, ghost data: seq<byte>)
  returns (gshared ad: PointsToArray<byte>)
  requires is_read_perm(rp, ptr, data)
  ensures ad == PointsToArray(ptr, data)
}

abstract module AIO(aioparams: AIOParams, ioifc: InputOutputIfc, ssm: DiskSSM(ioifc)) {
  import opened NativeTypes
  import opened Ptrs

  const PageSize := 4096

  /*
   * aiocb type
   *
   * implemented externally by aiocb struct from libaio
   *
   * addr: disk address, page-aligned
   * len: length of data, page-multiple
   * ptr: memory location to write data from or read data into
   */

  type Aiocb
  {
    function method addr() : uint64
    function method len() : uint64
    function method ptr() : Ptr
  }

  function method {:extern} new_aiocb(addr: uint64, ptr: Ptr, len: uint64)
    : (aiocb: Aiocb)
  ensures aiocb.addr() == addr
  ensures aiocb.ptr() == ptr
  ensures aiocb.len() == len

  /*
   * DiskInterface
   */

  method async_write<G>(
      aiocb_ptr: Ptr,
      glinear aiocb: Deref<Aiocb>,
      ptr: Ptr,
      ghost data: seq<byte>,
      glinear rp: aioparams.ReadPermission,
      glinear ticket: ssm.M)
  requires aiocb.ptr == aiocb_ptr
  requires aiocb.v.addr() as int % PageSize() == 0
  requires aiocb.v.len() as int % PageSize() == 0
  requires aiocb.v.len() > 0
  requires aioparams.is_read_perm(rp, ptr, data)
  requires ticket == DiskWriteTicket(aiocb.v.addr(), data)

  method async_read(
      aiocb_ptr: Ptr,
      glinear aiocb: Deref<Aiocb>,
      ptr: Ptr,
      glinear wp: ArrayDeref<byte>,
      glinear ticket: ssm.M)
  requires aiocb.ptr == aiocb_ptr
  requires aiocb.v.addr() as int % PageSize() == 0
  requires aiocb.v.len() as int % PageSize() == 0
  requires aiocb.v.len() > 0
  requires wp.ptr == aiocb.v.ptr()
  requires ticket == DiskReadTicket(aiocb.v.addr())

  method get_finished_req_blocking()
  returns (
    aiocb_ptr: Ptr,
    old_v: PendingTaskSet,
    new_v: PendingTaskSet,
    linear old_g: G,
    linear aiocb: lOption<Deref<Aiocb>>
    linear read_stub: lOption<DiskReadStub>,
    linear write_stub: lOption<DiskWriteStub>
  )
  ensures disk_interface_inv(disk_interface, old_v, old_g)
  ensures aiocb_ptr == nullptr() ==>
    && new_v == old_v
    && read_stub.lNone?
    && write_stub.lNone?
    && aiocb.lNone?
  ensures aiocb_ptr != nullptr() ==>
    aiocb_ptr in old_v.writeTasks || aiocb_ptr in old_v.readTasks
  ensures aiocb_ptr != nullptr() && aiocb_ptr in old_v.writeTasks ==>
    && aiocb_ptr !in old_v.readTasks
    && new_v == old_v.(writeTasks := MapRemove1(old_v.writeTasks, aiocb_ptr))
    && read_stub.lNone?
    && write_stub == lSome(DiskWriteStub(old_v.writeTasks[aiocb_ptr].addr))
    && aiocb == lSome(Deref(aiocb_ptr, aiocb_constructor(
}
