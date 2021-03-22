// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Lang/NativeTypes.s.dfy"
include "ArrayPtr.s.dfy"

module DiskInterfaceSpec {
  import opened NativeTypes
  import opened Ptrs

  type {:extern} AiocbOpaqueType(!new,==)
  
  function PageSize() : int { 4096 }

  /*
   * aiocb type
   *
   * implemented externally by aiocb struct from libaio
   *
   * addr: disk address, page-aligned
   * len: length of data, page-multiple
   * ptr: memory location to write data from or read data into
   */

  datatype Aiocb = Aiocb(_internal: AiocbOpaqueType)
  {
    function method {:extern} addr() : uint64
    function method {:extern} len() : uint64
    function method {:extern} ptr() : Ptr
  }

  function method {:extern} aiocb_constructor(addr: uint64, ptr: Ptr, len: uint64)
    : (aiocb: Aiocb)
  ensures aiocb.addr() == addr
  ensures aiocb.ptr() == ptr
  ensures aiocb.len() == len

  /*
   * Tickets and Stubs for doing reads/writes
   */

  linear datatype DiskReadTicket = DiskReadTicket(addr: uint64)
  linear datatype DiskReadStub = DiskReadStub(addr: uint64, contents: seq<byte>)
  linear datatype DiskWriteTicket = DiskWriteTicket(addr: uint64, contents: seq<byte>)
  linear datatype DiskWriteStub = DiskWriteStub(addr: uint64)

  /*
   * Internal state
   */

  datatype PendingWriteTask = PendingWriteTask(
      addr: uint64,
      len: uint64,
      ptr: Ptr,
      contents: seq<byte>)

  datatype PendingReadTask = PendingReadTask(
      addr: uint64,
      len: uint64,
      ptr: Ptr)

  datatype PendingTaskSet = PendingTaskSet(
      writeTasks: map<Ptr, PendingWriteTask>,
      readTasks: map<Ptr, PendingReadTask>)

  /*
   * DiskInterface
   */

  type {:extern} DiskInterface<G>

  predicate {:extern} disk_interface_inv<G>(
      disk_interface: DiskInterface<G>,
      v: PendingTaskSet,
      g: G)

  method {:extern} async_write<G>(
      disk_interface: DiskInterface<G>,
      aiocb_ptr: Ptr,
      linear aiocb: Deref<Aiocb>,
      /*readonly*/ linear data: ArrayDeref<byte>,
      linear ticket: DiskWriteTicket)
  returns (
    old_v: PendingTaskSet,
    new_v: PendingTaskSet,
    linear old_g: G
  )
  requires aiocb.ptr == aiocb_ptr
  requires aiocb.v.addr() as int % PageSize() == 0
  requires aiocb.v.len() as int % PageSize() == 0
  requires aiocb.v.len() > 0
  requires data.ptr == aiocb.v.ptr()
  requires |data.s| == aiocb.v.len() as int
  requires ticket == DiskWriteTicket(aiocb.v.addr(), data.s)

  ensures aiocb_ptr !in old_v.writeTasks
  ensures new_v == PendingTaskSet(
      old_v.writeTasks[aiocb_ptr :=
        PendingWriteTask(
          aiocb.v.addr(),
          aiocb.v.len(),
          aiocb.v.ptr(),
          data.s
        )
      ],
      old_v.readTasks)
  ensures disk_interface_inv(disk_interface, old_v, old_g)

  method {:extern} async_read(
      disk_interface: DiskInterface<G>,
      aiocb_ptr: Ptr,
      linear aiocb: Deref<Aiocb>,
      linear data: ArrayDeref<byte>,
      linear ticket: DiskReadTicket)
  requires aiocb.ptr == aiocb_ptr
  requires aiocb.v.addr() as int % PageSize() == 0
  requires aiocb.v.len() as int % PageSize() == 0
  requires aiocb.v.len() > 0
  requires data.ptr == aiocb.v.ptr()
  requires ticket == DiskReadTicket(aiocb.v.addr())

  method {:extern} get_finished_req<G>(
      disk_interface: DiskInterface<G>)
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
        

  method {:extern} disk_interface_op_cleanup<G>(
      disk_interface: DiskInterface<G>,
      new_v: PendingTaskSet,
      linear new_g: G)
  requires disk_interface_inv(disk_interface, new_v, new_g)
}
