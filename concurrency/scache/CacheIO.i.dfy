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
  import opened GlinearOption
  import opened GlinearMap
  import opened PageSizeConstant
  import opened Atomics
  import CacheSSM
  import DT = DiskToken(CacheIfc, CacheSSM)

  method get_free_io_slot(shared cache: Cache, inout linear local: LocalState)
  returns (idx: uint64, glinear access: IOSlotAccess)
  requires cache.Inv()
  requires old_local.WF(cache.config)
  ensures local.WF(cache.config)
  ensures 0 <= idx as int < NUM_IO_SLOTS as int
  ensures is_slot_access(cache.io_slots[idx as nat], access, cache.config)
  ensures local.t == old_local.t
  decreases *
  {
    // TODO this is naive and probably bad
    // (what does splinter do?)

    glinear var access_opt : glOption<IOSlotAccess> := glNone;

    var i: uint64 := local.io_slot_hand;
    var done := false;
    while !done
    invariant 0 <= i as int <= NUM_IO_SLOTS
    invariant done ==> access_opt.glSome?
        && 0 <= idx as int < NUM_IO_SLOTS
        && is_slot_access(cache.io_slots[idx as nat], access_opt.value, cache.config)
    decreases *
    {
      if i % AIO_HAND_BATCH_SIZE_64() == 0 {
        atomic_block var j := execute_atomic_fetch_add_uint32(cache.req_hand_base, 32) { }
        i := (j as uint64) % NUM_IO_SLOTS_64();

        var cleanup_done := false;
        while !cleanup_done
        decreases *
        {
          cleanup_done := io_cleanup_1(cache);
        }
      }

      glinear var iosa;
      assert cache.io_slots[i as nat].WF(cache.config);
      done, iosa := BasicLockImpl.try_acquire(lseq_peek(cache.io_slots, i).lock);

      if !done {
        i := i + 1;
        dispose_anything(iosa);
      } else {
        idx := i;
        i := i + 1;
        dispose_anything(access_opt);
        access_opt := iosa;
      }
    }

    access := unwrap_value(access_opt);

    inout local.io_slot_hand := i;
  }

  method disk_writeback_async(
      shared cache: Cache,
      inout linear local: LocalState,
      disk_idx: uint64,
      cache_idx: uint32,
      glinear wbo: T.WritebackObtainedToken,
      glinear ticket: CacheResources.DiskWriteTicket)
  requires cache.Inv()
  requires old_local.WF(cache.config)

  requires 0 <= cache_idx as int < cache.config.cache_size as int
  requires 0 <= disk_idx as int < cache.config.num_disk_pages as int
  requires wbo.is_handle(cache.key(cache_idx as int), cache.config)
  requires wbo.b.CacheEntryHandle?
  requires ticket == CacheResources.DiskWriteTicket(disk_idx as int, wbo.b.data.s)
  requires wbo.token.loc == cache.status[cache_idx as nat].rwlock_loc
  requires wbo.b.cache_entry.disk_idx == disk_idx as nat

  ensures local.WF(cache.config)
  ensures local.t == old_local.t
  decreases *
  {
    var idx: uint64;
    glinear var access;
    idx, access := get_free_io_slot(cache, inout local);
    glinear var IOSlotAccess(iocb, iovec) := access;

    iocb_prepare_write(
        lseq_peek(cache.io_slots, idx).iocb_ptr,
        inout iocb,
        disk_idx as int64,
        4096,
        cache.data_ptr(cache_idx));

    glinear var writeg := WriteG(
        cache.key(cache_idx as int),
        wbo, idx as int, iovec, cache.config);

    assert WriteGInv(
        cache.io_slots, cache.data, cache.page_handles, cache.status, cache.config,
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

  method disk_read_async(
      shared cache: Cache,
      inout linear local: LocalState,
      disk_idx: uint64,
      cache_idx: uint32,
      ptr: Ptr,
      glinear cache_reading: CacheResources.CacheReading,
      glinear ro: T.Token,
      glinear contents: PointsToArray<byte>,
      glinear idx_perm: CellContents<PageHandle>,
      glinear ticket: CacheResources.DiskReadTicket)
  requires cache.Inv()
  requires old_local.WF(cache.config)
  requires 0 <= cache_idx as int < cache.config.cache_size as int
  requires 0 <= disk_idx as int < cache.config.num_disk_pages as int
  requires |contents.s| == PageSize as int
  requires ticket == CacheResources.DiskReadTicket(disk_idx as nat)
  requires contents.ptr == ptr
  requires 0 <= disk_idx as int < cache.config.num_disk_pages as int
  requires ptr.aligned(PageSize as int)
  requires cache_reading.disk_idx == disk_idx as nat
  requires cache_reading.cache_idx == cache_idx as nat
  requires ro.loc == cache.status[cache_idx].rwlock_loc
  requires ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
  requires contents.ptr == cache.data[cache_idx]
  requires idx_perm.cell == cache.page_handles[cache_idx]
  requires idx_perm.v.disk_addr as int == disk_idx as int * PageSize
  requires idx_perm.v.data_ptr == cache.data[cache_idx]

  ensures local.WF(cache.config)
  ensures local.t == old_local.t
  decreases *
  {
    var idx: uint64;
    glinear var access;
    idx, access := get_free_io_slot(cache, inout local);
    glinear var IOSlotAccess(iocb, iovec) := access;

    iocb_prepare_read(
        lseq_peek(cache.io_slots, idx).iocb_ptr,
        inout iocb,
        disk_idx as int64,
        4096,
        cache.data_ptr(cache_idx));

    glinear var readg := ReadG(
        cache.key(cache_idx as int),
        cache_reading,
        idx_perm,
        ro,
        idx as int,
        iovec);

    assert ReadGInv(
        cache.io_slots, cache.data, cache.page_handles, cache.status, cache.config,
        cache.io_slots[idx as nat].iocb_ptr,
        iocb, contents, readg);

    aio.async_read(
        cache.ioctx,
        lseq_peek(cache.io_slots, idx).iocb_ptr,
        iocb,
        contents,
        readg,
        CacheResources.DiskReadTicket_unfold(ticket));
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
  requires 0 <= disk_idx as int
  requires disk_idx as int * 4096 < 0x1_0000_0000_0000_0000
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
    stub := CacheResources.DiskReadStub_fold(CacheResources.DiskReadStub(disk_idx as nat, contents.s), s);
  }

  method disk_writeback_sync(
      shared cache: Cache,
      ghost cache_idx: nat,
      disk_idx: uint64,
      ptr: Ptr,
      gshared wbo: T.WritebackObtainedToken,
      glinear ticket: CacheResources.DiskWriteTicket)
  returns (glinear stub: CacheResources.DiskWriteStub)
  requires cache.Inv()
  requires 0 <= cache_idx < cache.config.cache_size as int
  requires 0 <= disk_idx as int < cache.config.num_disk_pages as int
  requires wbo.is_handle(cache.key(cache_idx), cache.config)
  requires wbo.b.CacheEntryHandle?
  requires ticket == CacheResources.DiskWriteTicket(disk_idx as int, wbo.b.data.s)
  requires wbo.token.loc == cache.status[cache_idx].rwlock_loc
  requires wbo.b.cache_entry.disk_idx == disk_idx as nat
  requires ptr == cache.data[cache_idx]
  ensures stub == CacheResources.DiskWriteStub(disk_idx as nat)
  {
    glinear var s := aio.sync_write(
        ptr,
        4096,
        disk_idx,
        T.borrow_wb(wbo.token).data,
        CacheResources.DiskWriteTicket_unfold(ticket));
    stub := CacheResources.DiskWriteStub_fold(CacheResources.DiskWriteStub(disk_idx as nat), s);
  }

  method disk_read_callback(
      shared cache: Cache,
      cache_idx: uint32,
      ghost disk_addr: nat,
      glinear wp: PointsToArray<byte>,
      glinear ro: T.Token,
      glinear cache_reading: CacheResources.CacheReading,
      glinear idx: CellContents<PageHandle>,
      glinear stub: CacheResources.DiskReadStub)
  requires cache.Inv()
  requires 0 <= cache_idx as int < cache.config.cache_size as int
  requires 0 <= disk_addr < cache.config.num_disk_pages as int
  requires wp.ptr == cache.data[cache_idx]
  requires |wp.s| == PageSize as int
  requires stub == CacheResources.DiskReadStub(disk_addr as nat, wp.s)
  requires cache_reading.disk_idx == disk_addr as nat
  requires cache_reading.cache_idx == cache_idx as nat
  requires ro.loc == cache.status[cache_idx].rwlock_loc
  requires ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
  requires idx.cell == cache.page_handles[cache_idx]
  requires idx.v.disk_addr as int == disk_addr * PageSize
  requires idx.v.data_ptr == cache.data[cache_idx]
  {
    glinear var status, cache_entry;
    status, cache_entry := CacheResources.finish_page_in(
          cache_idx as int, disk_addr as nat,
          cache_reading, stub);

    /*write_cell(
            cache.page_handles_ptr(cache_idx),
            inout idx,
            disk_addr as int64);*/

    glinear var ceh := CacheEntryHandle(
        cache.key(cache_idx as int), cache_entry, idx, wp);

    cache.status_atomic(cache_idx).load_phase_finish_threadless(ro, ceh, status);
  }

  method disk_writeback_callback(
      shared cache: Cache,
      cache_idx: uint32,
      ghost disk_addr: nat,
      glinear wbo: T.WritebackObtainedToken,
      glinear stub: CacheResources.DiskWriteStub)
  requires cache.Inv()
  requires 0 <= cache_idx as int < cache.config.cache_size as int
  requires stub == CacheResources.DiskWriteStub(disk_addr)
  requires wbo.is_handle(cache.key(cache_idx as int), cache.config)
  requires wbo.token.loc == cache.status[cache_idx as nat].rwlock_loc
  requires wbo.b.CacheEntryHandle?
  requires wbo.b.cache_entry.disk_idx == disk_addr
  {
    cache.status_atomic(cache_idx).release_writeback(wbo, stub);
  }

  method disk_writeback_callback_vec(
      shared cache: Cache,
      iovec_ptr: Ptr,
      iovec_len: uint64,
      gshared iovec: PointsToArray<Iovec>,
      ghost offset: nat,
      ghost keys: seq<Key>,
      ghost datas: seq<seq<byte>>,
      glinear wbos: map<nat, T.WritebackObtainedToken>,
      glinear stubs: map<nat, DT.Token>)
  requires cache.Inv()
  requires |iovec.s| >= |datas| == |keys| == iovec_len as int
  requires iovec.ptr == iovec_ptr
  requires forall i | 0 <= i < |keys| ::
    && i in wbos
    && i in stubs
    && simpleWriteGInv(cache.io_slots, cache.data, cache.page_handles,
        cache.status, cache.config, offset + i, datas[i], keys[i], wbos[i])
    && stubs[i].val == CacheSSM.DiskWriteResp(offset + i)
    && iovec.s[i].iov_base() == cache.data[keys[i].cache_idx]
  {
    glinear var wbos' := wbos;
    glinear var stubs' := stubs;

    var j : uint64 := 0;
    while j < iovec_len
    invariant 0 <= j as int <= iovec_len as int
    invariant |iovec.s| >= |datas| == |keys| == iovec_len as int
    invariant forall i: int | j as int <= i < |keys| ::
      && i in wbos'
      && i in stubs'
      && simpleWriteGInv(cache.io_slots, cache.data, cache.page_handles,
          cache.status, cache.config, offset + i, datas[i], keys[i], wbos'[i])
      && stubs'[i].val == CacheSSM.DiskWriteResp(offset + i)
    {
      glinear var wbo, stub;
      wbos', wbo := glmap_take(wbos', j as int);
      stubs', stub := glmap_take(stubs', j as int);
      var my_iovec := iovec_ptr.index_read(iovec, j);
      var data_ptr := my_iovec.iov_base();
      var cache_idx := cache_idx_of_data_ptr(cache, data_ptr, keys[j].cache_idx);
      glinear var ustub := CacheResources.DiskWriteStub_fold(CacheResources.DiskWriteStub(offset + j as int), stub);
      disk_writeback_callback(cache, cache_idx, offset + j as int, wbo, ustub);
      j := j + 1;
    }

    dispose_anything(wbos');
    dispose_anything(stubs');
  }

  method disk_read_callback_vec(
      shared cache: Cache,
      iovec_ptr: Ptr,
      iovec_len: uint64,
      gshared iovec: PointsToArray<Iovec>,
      ghost offset: nat,
      ghost keys: seq<Key>,
      glinear wps: map<nat, PointsToArray<byte>>,
      glinear ros: map<nat, T.Token>,
      glinear idxs: map<nat, CellContents<PageHandle>>,
      glinear cache_readings: map<nat, CacheResources.CacheReading>,
      glinear stubs: map<nat, DT.Token>)
  requires cache.Inv()
  requires |iovec.s| >= |keys| == iovec_len as int
  requires iovec.ptr == iovec_ptr
  requires offset + |keys| <= cache.config.num_disk_pages as int
  requires forall i | 0 <= i < |keys| ::
    && i in ros && i in wps && i in idxs && i in stubs && i in cache_readings
    && simpleReadGInv(cache.io_slots, cache.data, cache.page_handles,
        cache.status, cache.config, offset + i, wps[i], keys[i], cache_readings[i], idxs[i], ros[i])
    && |wps[i].s| == PageSize as int
    && stubs[i].val == CacheSSM.DiskReadResp(offset + i, wps[i].s)
    && iovec.s[i].iov_base() == cache.data[keys[i].cache_idx]
  {
    glinear var wps' := wps;
    glinear var stubs' := stubs;
    glinear var ros' := ros;
    glinear var idxs' := idxs;
    glinear var cache_readings' := cache_readings;

    var j : uint64 := 0;
    while j < iovec_len
    invariant 0 <= j as int <= iovec_len as int
    invariant |iovec.s| >= |keys| == iovec_len as int
    invariant forall i: int | j as int <= i < |keys| ::
      && i in ros' && i in wps' && i in idxs' && i in stubs' && i in cache_readings'
      && simpleReadGInv(cache.io_slots, cache.data, cache.page_handles,
          cache.status, cache.config, offset + i, wps'[i], keys[i], cache_readings'[i], idxs'[i], ros'[i])
      && |wps'[i].s| == PageSize as int
      && stubs'[i].val == CacheSSM.DiskReadResp(offset + i, wps'[i].s)
      && iovec.s[i].iov_base() == cache.data[keys[i].cache_idx]
    {
      glinear var wp, stub, idx, ro, cache_reading;
      wps', wp := glmap_take(wps', j as int);
      stubs', stub := glmap_take(stubs', j as int);
      ros', ro := glmap_take(ros', j as int);
      cache_readings', cache_reading := glmap_take(cache_readings', j as int);
      idxs', idx := glmap_take(idxs', j as int);
      var my_iovec := iovec_ptr.index_read(iovec, j);
      var data_ptr := my_iovec.iov_base();
      var cache_idx := cache_idx_of_data_ptr(cache, data_ptr, keys[j].cache_idx);
      assert |wp.s| == PageSize as int;
      glinear var ustub := CacheResources.DiskReadStub_fold(CacheResources.DiskReadStub(offset + j as int, wp.s), stub);
      disk_read_callback(cache, cache_idx, offset + j as int,
          wp, ro, cache_reading, idx, ustub);
      j := j + 1;
    }

    dispose_anything(stubs');
    dispose_anything(wps');
    dispose_anything(ros');
    dispose_anything(idxs');
    dispose_anything(cache_readings');
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
      done := io_cleanup_1(cache);
    }
  }

  method io_cleanup_all(shared cache: Cache)
  requires cache.Inv()
  decreases *
  {
    var i: uint64 := 0;
    while i < NUM_IO_SLOTS_64()
    {
      assert lseq_peek(cache.io_slots, i).WF(cache.config);
      var isl := BasicLockImpl.is_locked(lseq_peek(cache.io_slots, i).lock);
      while isl
      decreases *
      {
        var done := false;
        while !done
        decreases *
        {
          done := io_cleanup_1(cache);
        }
        isl := BasicLockImpl.is_locked(lseq_peek(cache.io_slots, i).lock);
      }
      i := i + 1;
    }
  }

  method cache_idx_of_data_ptr(shared cache: Cache, data_ptr: Ptr, ghost cache_idx: nat)
  returns (ci: uint32)
  requires cache.Inv()
  requires 0 <= cache_idx < |cache.data|
  requires data_ptr == cache.data[cache_idx]
  ensures ci as nat == cache_idx
  {
    ci := (ptr_diff(data_ptr, cache.data_base_ptr) / 4096) as uint32;
  }

  method io_cleanup_1(shared cache: Cache)
  returns (done: bool)
  requires cache.Inv()
  {
    var iocb_ptr;
    glinear var fr;
    iocb_ptr, fr := aio.get_event(cache.ioctx);

    if iocb_ptr == nullptr() {
      done := true;
      dispose_anything(fr);
    } else {
      ghost var si := (if fr.FRWrite? then fr.wg.slot_idx else
          if fr.FRWritev? then fr.wvg.slot_idx else
          fr.rg.slot_idx);
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

      glinear var iocb1;
      glinear var iovec1;

      var is_write := iocb_is_write(iocb_ptr, fr.iocb);
      var is_writev := iocb_is_writev(iocb_ptr, fr.iocb);
      var is_read := iocb_is_read(iocb_ptr, fr.iocb);

      if is_write {
        assert fr.FRWrite?;
        glinear var FRWrite(iocb, data, wg, stub) := fr;
        glinear var WriteG(key, wbo, g_slot_idx, iovec, c_config) := wg;

        glinear var ustub := CacheResources.DiskWriteStub_fold(CacheResources.DiskWriteStub(iocb.offset), stub);
        ghost var disk_idx := ustub.disk_idx;

        var data_ptr := iocb_buf(iocb_ptr, iocb);
        var cache_idx := cache_idx_of_data_ptr(cache, data_ptr, key.cache_idx);

        disk_writeback_callback(cache, cache_idx, disk_idx, wbo, ustub);

        iocb1 := iocb;
        iovec1 := iovec;
      } else if is_writev {
        assert fr.FRWritev?;

        glinear var FRWritev(iocb, iovec, datas, wvg, stubs) := fr;
        glinear var WritevG(keys, wbos, g_slot_idx, c_config) := wvg;

        var iovec_ptr := iocb_iovec(iocb_ptr, iocb);
        var iovec_len := iocb_iovec_len(iocb_ptr, iocb);
        ghost var disk_idx := iocb.offset;

        disk_writeback_callback_vec(cache, iovec_ptr, iovec_len, iovec, disk_idx, keys, datas, wbos, stubs);

        iocb1 := iocb;
        iovec1 := iovec;
      } else if is_read {
        glinear var FRRead(iocb, wp, rg, stub) := fr;
        glinear var ReadG(key, cache_reading, idx, ro, g_slot_idx, iovec) := rg;

        glinear var ustub := CacheResources.DiskReadStub_fold(CacheResources.DiskReadStub(iocb.offset, wp.s), stub);
        ghost var disk_idx := ustub.addr;

        var data_ptr := iocb_buf(iocb_ptr, iocb);
        var cache_idx := cache_idx_of_data_ptr(cache, data_ptr, key.cache_idx);

        disk_read_callback(cache, cache_idx, disk_idx, wp, ro, cache_reading, idx, ustub);

        iocb1 := iocb;
        iovec1 := iovec;
      } else {
        assert fr.FRReadv?;

        glinear var FRReadv(iocb, iovec, wps, rvg, stubs) := fr;
        glinear var ReadvG(keys, cache_reading, idx, ro, g_slot_idx) := rvg;

        var iovec_ptr := iocb_iovec(iocb_ptr, iocb);
        var iovec_len := iocb_iovec_len(iocb_ptr, iocb);
        ghost var disk_idx := iocb.offset;

        disk_read_callback_vec(cache, iovec_ptr, iovec_len, iovec, disk_idx, keys, wps, ro, idx, cache_reading, stubs);

        iocb1 := iocb;
        iovec1 := iovec;
      }

      glinear var slot_access := IOSlotAccess(iocb1, iovec1);
      assert slot_access.iocb.ptr == cache.io_slots[slot_idx as nat].iocb_ptr;
      assert slot_access.iovec.ptr == cache.io_slots[slot_idx as nat].iovec_ptr;
      assert |slot_access.iovec.s| == cache.config.pages_per_extent as int;
      assert lseq_peek(cache.io_slots, slot_idx).WF(cache.config);
      BasicLockImpl.release(
          lseq_peek(cache.io_slots, slot_idx).lock,
          slot_access);
    }
  }
}
