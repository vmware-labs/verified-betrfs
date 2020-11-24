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

  method disk_writeback_async(addr: uint64,
      ptr: Ptr,
      /*readonly*/ linear contents: Ptrs.ArrayDeref<byte>,
      linear g: WritebackGhostState)
  requires contents.ptr == ptr
  requires |contents.s| == 4096
}
