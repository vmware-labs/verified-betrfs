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
  import BasicLockImpl

  method get_free_io_slot(shared cache: Cache, inout linear local: LocalState)
  returns (idx: uint64, glinear access: IOSlotAccess)
  requires cache.Inv()
  requires old_local.WF()
  ensures local.WF()
  ensures 0 <= idx as int < NUM_IO_SLOTS
  ensures is_slot_access(cache.io_slots[idx], access)
  ensures local.t == old_local.t

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
  ensures local.t == old_local.t
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

  method disk_writeback_callback(
      shared cache: Cache,
      cache_idx: uint64,
      ghost disk_addr: nat,
      glinear wbo: T.WritebackObtainedToken,
      glinear stub: CacheResources.DiskWriteStub)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires stub == CacheResources.DiskWriteStub(disk_addr)
  requires wbo.is_handle(cache.key(cache_idx as int))
  requires wbo.token.loc == cache.status[cache_idx].rwlock_loc
  requires wbo.b.CacheEntryHandle?
  requires wbo.b.cache_entry.disk_idx == disk_addr
  {
    cache.status[cache_idx].release_writeback(wbo, stub);
  }

  method io_cleanup(shared cache: Cache, max_io_events: uint64)
  requires cache.Inv()
  {
    var counter: uint64 := 0;
    var done := false;
    while counter < max_io_events && !done
    invariant 0 <= counter <= max_io_events
    {
      counter := counter + 1;
      
      var iocb_ptr;
      glinear var fr;
      iocb_ptr, fr := aio.get_event(cache.ioctx);

      if iocb_ptr == nullptr {
        done := true;
        dispose_anything(fr);
      } else {
        assert fr.FRWrite?;

        glinear var FRWrite(iocb, data, wg, stub) := fr;
        glinear var WriteG(key, wbo, g_slot_idx, io_slot_info) := wg;

        var slot_idx;
        assume slot_idx == g_slot_idx; // TODO

        var io_slot_info_value :=
            cache.io_slots[slot_idx].io_slot_info_ptr.read(io_slot_info);

        match io_slot_info_value {
          case IOSlotWrite(cache_idx) => {
            glinear var ustub := CacheResources.DiskWriteStub_fold(iocb.offset, stub);
            ghost var disk_idx := ustub.disk_idx;
            disk_writeback_callback(cache, cache_idx, disk_idx, wbo, ustub);
          }
          case IOSlotRead(cache_idx) => {
            assert false;
            dispose_anything(wbo);
            dispose_anything(stub);
          }
        }

        BasicLockImpl.release(
            cache.io_slots[slot_idx].lock,
            IOSlotAccess(iocb, io_slot_info));
      }
    }
  }
}
