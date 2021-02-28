// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "ArrayPtr.s.dfy"
include "RWLock.i.dfy"
include "CacheResources.i.dfy"

module DiskIO {
  import opened Ptrs
  import opened NativeTypes
  import RWLock
  import CacheResources

  linear datatype WritebackGhostState = WritebackGhostState(
      linear q: RWLock.R,
      /*readonly*/ linear cache_entry: CacheResources.R,
      /*readonly*/ linear idx: Deref<int>)
  {
    predicate WF(addr: uint64)
    {
    }
  }

  method disk_writeback_async(addr: uint64,
      ptr: Ptr,
      /*readonly*/ linear contents: Ptrs.ArrayDeref<byte>,
      linear g: WritebackGhostState,
      linear ticket: CacheResources.R)
  requires contents.ptr == ptr
  requires |contents.s| == 4096
  requires ticket == CacheResources.DiskWriteTicket(addr, contents.s)

  method disk_read_sync(
      addr: uint64,
      ptr: Ptr,
      inout linear contents: ArrayDeref<byte>,
      linear ticket: CacheResources.R)
  returns (linear stub: CacheResources.R)
  requires |old_contents.s| == 4096
  requires ticket == CacheResources.DiskReadTicket(addr)
  requires old_contents.ptr == ptr
  ensures contents.ptr == ptr
  ensures |contents.s| == 4096
  ensures stub == CacheResources.DiskReadStub(addr, contents.s)
}
