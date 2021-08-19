include "CacheTypes.i.dfy"

module CacheIO(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened CT = CacheTypes(aio)
  import opened Constants
  import opened Ptrs
  import opened NativeTypes
  import T = RwLockToken
  import CacheResources
  import opened CacheAIOParams
  import opened IocbStruct

  method get_free_io_slot(shared cache: Cache, inout linear local: LocalState)
  returns (idx: uint64, glinear access: IOSlotAccess)
  requires cache.Inv()
  requires old_local.WF()
  ensures local.WF()
  ensures 0 <= idx as int < NUM_IO_SLOTS
  ensures is_slot_access(cache.io_slots[idx], access)

  method disk_writeback_async(
      shared cache: Cache,
      inout linear local: LocalState,
      disk_idx: uint64,
      cache_idx: uint64,
      glinear wbo: T.WritebackObtainedToken,
      glinear ticket: CacheResources.DiskWriteTicket)
  requires cache.Inv()
  requires old_local.WF()

  requires 0 <= cache_idx as int < CACHE_SIZE
  requires 0 <= disk_idx as int < NUM_DISK_PAGES
  requires wbo.is_handle(cache.key(cache_idx as int))
  requires wbo.b.CacheEntryHandle?
  requires ticket == CacheResources.DiskWriteTicket(disk_idx as int, wbo.b.data.s)

  ensures local.WF()
  {
    var idx: uint64;
    glinear var access;
    idx, access := get_free_io_slot(cache, inout local);
    glinear var IOSlotAccess(iocb, io_slot_info) := access;

    iocb_prepare_write(
        cache.io_slots[idx].iocb_ptr,
        inout iocb,
        disk_idx as int64,
        4096,
        cache.data[cache_idx]);

    cache.io_slots[idx].io_slot_info_ptr.write(
        inout io_slot_info,
        IOSlotWrite(cache_idx));

    glinear var writeg := WriteG(
        cache.key(cache_idx as int),
        wbo, idx as int, io_slot_info);

    aio.async_write(
        cache.ioctx,
        cache.io_slots[idx].iocb_ptr,
        iocb,
        wbo.b.data.s,
        writeg,
        CacheResources.DiskWriteTicket_unfold(ticket));
  }

  method disk_read_sync(
      disk_idx: uint64,
      ptr: Ptr,
      glinear inout contents: PointsToArray<byte>,
      glinear ticket: CacheResources.DiskReadTicket)
  returns (glinear stub: CacheResources.DiskReadStub)
  requires |old_contents.s| == PageSize
  requires ticket == CacheResources.DiskReadTicket(disk_idx as nat)
  requires old_contents.ptr == ptr
  requires 0 <= disk_idx as int < NUM_DISK_PAGES
  ensures contents.ptr == ptr
  ensures |contents.s| == PageSize
  ensures stub == CacheResources.DiskReadStub(disk_idx as nat, contents.s)
  {
    glinear var s := aio.sync_read(
        ptr,
        4096,
        disk_idx,
        inout contents,
        CacheResources.DiskReadTicket_unfold(ticket));
    stub := CacheResources.DiskReadStub_fold(disk_idx as nat, contents.s, s);
  }

  /*
  method disk_writeback_callback(
      cache: Cache,
      addr: uint64,
      /*readonly*/ linear contents: Ptrs.ArrayDeref<byte>,
      linear g: CacheIOImpl.WritebackGhostState,
      linear stub: CacheResources.R)
  requires cache.Inv()
  requires stub == CacheResources.DiskWriteStub(addr)
  requires g.WF(addr)
  {
    
  }
  */
}
