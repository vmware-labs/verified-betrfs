include "ArrayPtr.s.dfy"
include "RWLock.i.dfy"
include "CacheResources.i.dfy"

module DiskIO {
  import opened Ptrs
  import opened NativeTypes
  import ReadWriteLockResources
  import CacheResources

  linear datatype WritebackGhostState = WritebackGhostState(
      linear q: ReadWriteLockResources.Q,
      linear cache_entry: CacheResources.R, // TODO should be readonly
      linear idx: ConstDeref<int>)

  method disk_writeback_async(addr: uint64,
      ptr: Ptr, linear contents: Ptrs.R<byte>,
      linear g: WritebackGhostState)
  requires contents.ptr == ptr
  requires |contents.s| == 4096
}
