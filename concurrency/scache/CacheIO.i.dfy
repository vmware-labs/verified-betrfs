include "CacheTypes.i.dfy"
include "../Math/Math.i.dfy"

module CacheIO(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened CT = CacheTypes(aio)
  import opened Constants
  import opened Ptrs
  import opened NativeTypes
  import RwLock
  import T = RwLockToken
  import CacheResources
  import opened CacheAIOParams
  import opened IocbStruct
  import BasicLockImpl
  import opened CacheHandle
  import opened LinearSequence_i
  import opened Cells
  import Math

  method get_free_io_slot(shared cache: Cache, inout linear local: LocalState)
  returns (idx: uint64, glinear access: IOSlotAccess)
  requires cache.Inv()
  requires old_local.WF()
  ensures local.WF()
  ensures 0 <= idx as int < NUM_IO_SLOTS
  ensures is_slot_access(cache.io_slots[idx as nat], access)
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
  requires wbo.token.loc == cache.status[cache_idx as nat].rwlock_loc
  requires wbo.b.cache_entry.disk_idx == disk_idx as nat

  ensures local.WF()
  ensures local.t == old_local.t
  {
    var idx: uint64;
    glinear var access;
    idx, access := get_free_io_slot(cache, inout local);
    glinear var IOSlotAccess(iocb, io_slot_info) := access;

    iocb_prepare_write(
        lseq_peek(cache.io_slots, idx).iocb_ptr,
        inout iocb,
        disk_idx as int64,
        4096,
        cache.data_ptr(cache_idx));

    write_cell(
        lseq_peek(cache.io_slots, idx).io_slot_info_cell,
        inout io_slot_info,
        IOSlotWrite(cache_idx));

    glinear var writeg := WriteG(
        cache.key(cache_idx as int),
        wbo, idx as int, io_slot_info);

    assert WriteGInv(
        cache.io_slots, cache.data, cache.disk_idx_of_entry, cache.status,
        cache.io_slots[idx as nat].iocb_ptr,
        iocb, wbo.b.data.s, writeg);
    aio.async_write(
        cache.ioctx,
        lseq_peek(cache.io_slots, idx).iocb_ptr,
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
  requires |old_contents.s| == PageSize as int
  requires ticket == CacheResources.DiskReadTicket(disk_idx as nat)
  requires old_contents.ptr == ptr
  requires 0 <= disk_idx as int < NUM_DISK_PAGES
  requires ptr.aligned(PageSize as int)
  ensures contents.ptr == ptr
  ensures |contents.s| == PageSize as int
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

  method disk_read_callback(
      shared cache: Cache,
      cache_idx: uint64,
      ghost disk_addr: nat,
      glinear wp: PointsToArray<byte>,
      glinear ro: T.Token,
      glinear cache_reading: CacheResources.CacheReading,
      glinear idx: CellContents<int64>,
      glinear stub: CacheResources.DiskReadStub)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires 0 <= disk_addr < NUM_DISK_PAGES
  requires wp.ptr == cache.data[cache_idx]
  requires |wp.s| == PageSize as int
  requires stub == CacheResources.DiskReadStub(disk_addr as nat, wp.s)
  requires cache_reading.disk_idx == disk_addr as nat
  requires cache_reading.cache_idx == cache_idx as nat
  requires ro.loc == cache.status[cache_idx].rwlock_loc
  requires ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
  requires idx.cell == cache.disk_idx_of_entry[cache_idx]
  requires idx.v as int == disk_addr
  {
    glinear var status, cache_entry;
    status, cache_entry := CacheResources.finish_page_in(
          cache_idx as int, disk_addr as nat,
          cache_reading, stub);

    /*write_cell(
            cache.disk_idx_of_entry_ptr(cache_idx),
            inout idx,
            disk_addr as int64);*/

    glinear var ceh := CacheEntryHandle(
        cache.key(cache_idx as int), cache_entry, idx, wp);

    cache.status_atomic(cache_idx).load_phase_finish_threadless(ro, ceh, status);
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
  requires wbo.token.loc == cache.status[cache_idx as nat].rwlock_loc
  requires wbo.b.CacheEntryHandle?
  requires wbo.b.cache_entry.disk_idx == disk_addr
  {
    cache.status_atomic(cache_idx).release_writeback(wbo, stub);
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
        ghost var si := (if fr.FRWrite? then fr.wg.slot_idx else fr.rg.slot_idx);
        calc {
          ptr_diff(iocb_ptr, cache.iocb_base_ptr) as int / SizeOfIocb() as int;
          ptr_diff(
            ptr_add(cache.iocb_base_ptr, si as uint64 * SizeOfIocb()),
            cache.iocb_base_ptr) as int / SizeOfIocb() as int;
          (si * SizeOfIocb() as int) / SizeOfIocb() as int;
          {
            Math.lemma_div_by_multiple(si, SizeOfIocb() as int);
          }
          si;
        }

        var slot_idx: uint64 := ptr_diff(iocb_ptr, cache.iocb_base_ptr) / SizeOfIocb();

        var io_slot_info_value :=
            read_cell(
                lseq_peek(cache.io_slots, slot_idx).io_slot_info_cell,
                if fr.FRWrite? then fr.wg.io_slot_info else fr.rg.io_slot_info);

        glinear var iocb1, io_slot_info1;

        match io_slot_info_value {
          case IOSlotWrite(cache_idx) => {
            glinear var FRWrite(iocb, data, wg, stub) := fr;
            glinear var WriteG(key, wbo, g_slot_idx, io_slot_info) := wg;

            glinear var ustub := CacheResources.DiskWriteStub_fold(iocb.offset, stub);
            ghost var disk_idx := ustub.disk_idx;
            disk_writeback_callback(cache, cache_idx, disk_idx, wbo, ustub);

            iocb1 := iocb;
            io_slot_info1 := io_slot_info;
          }
          case IOSlotRead(cache_idx) => {
            glinear var FRRead(iocb, wp, rg, stub) := fr;
            glinear var ReadG(key, cache_reading, idx, ro, g_slot_idx, io_slot_info) := rg;

            glinear var ustub := CacheResources.DiskReadStub_fold(iocb.offset, wp.s, stub);
            ghost var disk_idx := ustub.addr;
            disk_read_callback(cache, cache_idx, disk_idx, wp, ro, cache_reading, idx, ustub);

            iocb1 := iocb;
            io_slot_info1 := io_slot_info;
          }
        }

        glinear var slot_access := IOSlotAccess(iocb1, io_slot_info1);
        assert slot_access.iocb.ptr == cache.io_slots[slot_idx as nat].iocb_ptr;
        assert slot_access.io_slot_info.cell == cache.io_slots[slot_idx as nat].io_slot_info_cell;
        assert lseq_peek(cache.io_slots, slot_idx).WF();
        BasicLockImpl.release(
            lseq_peek(cache.io_slots, slot_idx).lock,
            slot_access);
      }
    }
  }
}
