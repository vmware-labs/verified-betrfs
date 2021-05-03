include "Cache.i.dfy"

module CacheIOImpl {
  import opened CacheImpl
  import opened Constants
  import opened Ptrs
  import opened NativeTypes
  import RWLock
  import CacheResources
  import LinearMaps
  import opened DiskInterfaceSpec

  method get_free_io_slot(c: Cache, io: IOHandle)
  returns (idx: uint64, linear access: IOSlotAccess)
  requires io.Inv(c)
  ensures 0 <= idx as int < NUM_IO_SLOTS
  ensures is_slot_access(io.io_slots[idx], access)

  method disk_writeback_async(
      c: Cache,
      io: IOHandle,
      disk_idx: uint64,
      cache_idx: uint64,
      /*readonly*/ linear contents: Ptrs.ArrayDeref<byte>,
      linear g: WritebackGhostState,
      linear ticket: DiskWriteTicket)
  requires c.Inv()
  requires io.Inv(c)
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires 0 <= disk_idx as int < NUM_DISK_PAGES
  requires contents.ptr == c.data[cache_idx]
  requires |contents.s| == 4096
  requires ticket == DiskWriteTicket(disk_idx * 4096, contents.s)
  requires g.WF(c, cache_idx as int)
  {
    var idx;
    linear var access;
    idx, access := get_free_io_slot(c, io);
    linear var IOSlotAccess(aiocb, info) := access;

    ptr_write(io.io_slots[idx].aiocb_ptr,
        inout aiocb,
        aiocb_constructor(disk_idx * 4096, c.data[cache_idx], 4096));

    ptr_write(io.io_slots[idx].info_ptr,
        inout info,
        IOSlotWrite(cache_idx));

    var old_v, new_v;
    linear var old_g;
    old_v, new_v, old_g := async_write(
        io.disk_interface,
        io.io_slots[idx].aiocb_ptr,
        aiocb,
        contents,
        ticket);
    ///////////////////////////////////////////////////////////////////
    linear var DIGhost(writeMap, readMap) := old_g;
    writeMap := LinearMaps.add(writeMap, io.io_slots[idx].aiocb_ptr,
        WritebackGhostStateWithSlot(info, g));
    linear var new_g := DIGhost(writeMap, readMap);
    assert WriteTaskInv(new_v.writeTasks[io.io_slots[idx].aiocb_ptr],
        WritebackGhostStateWithSlot(info, g), c);
    ///////////////////////////////////////////////////////////////////
    disk_interface_op_cleanup(io.disk_interface, new_v, new_g);
    ///////////////////////////////////////////////////////////////////
  }

  method disk_read_sync(
      addr: uint64,
      ptr: Ptr,
      inout linear contents: ArrayDeref<byte>,
      linear ticket: DiskReadTicket)
  returns (linear stub: DiskReadStub)
  requires |old_contents.s| == 4096
  requires ticket == DiskReadTicket(addr)
  requires old_contents.ptr == ptr
  ensures contents.ptr == ptr
  ensures |contents.s| == 4096
  ensures stub == DiskReadStub(addr, contents.s)


  method disk_writeback_callback(
      c: Cache,
      addr: uint64,
      /*readonly*/ linear contents: Ptrs.ArrayDeref<byte>,
      linear g: CacheIOImpl.WritebackGhostState,
      linear stub: CacheResources.R)
  requires c.Inv()
  requires stub == CacheResources.DiskWriteStub(addr)
  requires g.WF(addr)
  {
    
  }
}
