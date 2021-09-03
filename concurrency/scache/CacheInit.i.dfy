include "CacheTypes.i.dfy"

module CacheInit(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened IocbStruct
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened NativeTypes
  import opened Ptrs
  import opened Constants
  import opened GlinearSeq
  import opened CT = CacheTypes(aio)
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened CacheHandle
  import opened Atomics
  import opened Cells
  import T = DiskSSMTokens(CacheIfc, CacheSSM)
  import opened CacheResources
  import opened GlinearOption
  import opened CacheAIOParams
  import opened BasicLockImpl

  method split_into_page_size_chunks(glinear pta: PointsToArray<byte>)
  returns (glinear pta_seq: glseq<PointsToArray<byte>>)
  requires |pta.s| == CACHE_SIZE * PageSize
  ensures pta_seq.len() == CACHE_SIZE
  ensures forall i | 0 <= i < CACHE_SIZE ::
      pta_seq.has(i)
        && 0 <= pta.ptr.as_nat() + i * PageSize < 0x1_0000_0000_0000_0000
        && pta_seq.get(i).ptr == ptr_add(pta.ptr, i as uint64 * PageSize as uint64)
        && |pta_seq.get(i).s| == PageSize

  method init_cache(glinear init_tok: T.Token)
  returns (linear c: Cache)
  requires CacheSSM.Init(init_tok.val)
  ensures c.Inv()
  {
    var data_base_ptr;
    glinear var data_pta_full;
    data_base_ptr, data_pta_full := alloc_array_aligned<byte>(
        CACHE_SIZE as uint64 * PageSize as uint64, 0, PageSize as uint64);
    glinear var data_pta_seq : glseq<PointsToArray<byte>> :=
        split_into_page_size_chunks(data_pta_full);

    var iocb_base_ptr;
    glinear var iocbs;
    iocb_base_ptr, iocbs := new_iocb_array(NUM_IO_SLOTS as uint64);

    linear var read_refcounts_array := lseq_alloc(RC_WIDTH as uint64 * CACHE_SIZE as uint64);
    linear var status_idx_array := lseq_alloc(CACHE_SIZE as uint64);

    glinear var empty_seq, dis := split_init(init_tok);

    ghost var data := seq(CACHE_SIZE, (i) requires 0 <= i < CACHE_SIZE =>
        data_pta_seq.get(i).ptr);

    var i: uint64 := 0;
    while i < CACHE_SIZE as uint64
    {
      linear var cell_idx;
      glinear var cell_idx_contents;
      cell_idx, cell_idx_contents := new_cell<int64>(0);
      glinear var data_pta;
      data_pta_seq, data_pta := glseq_take(data_pta_seq, i as nat);

      ghost var key := Key(data_pta.ptr, cell_idx, i as nat);

      glinear var cache_empty;
      cache_empty, empty_seq := pop_EmptySeq(empty_seq, i as nat, CACHE_SIZE);
      glinear var handle := CacheEmptyHandle(key, cache_empty, cell_idx_contents, data_pta);
      glinear var central, rcs := RwLockToken.perform_Init(handle);
      ghost var rwlock_loc := central.loc;

      linear var atomic_status_atomic := new_atomic(
          flag_unmapped,
          AtomicStatusImpl.G(central, glNone),
          (v, g) => AtomicStatusImpl.state_inv(v, g, key, rwlock_loc),
          0);
      linear var atomic_status := AtomicStatus(
          atomic_status_atomic,
          rwlock_loc,
          key);

      linear var status_idx := StatusIdx(atomic_status, cell_idx);
      lseq_give_inout(inout status_idx_array, i, status_idx);

      var j : uint64 := 0;
      while j < RC_WIDTH as uint64
      {
        glinear var rc;
        rc, rcs := RwLockToken.pop_rcs(rcs, j as nat, RC_WIDTH);
        linear var ar_atomic := new_atomic(0, rc,
            (v, g) => AtomicRefcountImpl.state_inv(v, g, j as nat, rwlock_loc),
            0);
        linear var ar := AtomicRefcount(ar_atomic, rwlock_loc);

        // XXX I don't care about the perf of the initialization method, but do note
        // that the access pattern for writing to this array might be completely awful.
        lseq_give_inout(inout read_refcounts_array, j * CACHE_SIZE as uint64 + i, ar);

        j := j + 1;
      }

      dispose_anything(rcs);

      i := i + 1;
    }

    linear var cache_idx_of_page_array := lseq_alloc(NUM_DISK_PAGES as uint64);

    i := 0;
    while i < NUM_DISK_PAGES as uint64
    {
      glinear var di;
      di, dis := pop_IdxSeq(dis, i as nat, NUM_DISK_PAGES);
      linear var ail := new_atomic(-1, di,
          (v, g) => AtomicIndexLookupImpl.state_inv(v, g, i as nat),
          0);
      lseq_give_inout(inout cache_idx_of_page_array, i, ail);
      i := i + 1;
    }

    dispose_anything(data_pta_seq);
    dispose_anything(empty_seq);
    dispose_anything(dis);

    linear var global_clockpointer := new_atomic(0, NullGhostType, (v, g) => true, 0);
    linear var io_slots := lseq_alloc(NUM_IO_SLOTS as uint64);
    linear var ioctx;

    i := 0;
    while i < NUM_IO_SLOTS as uint64
    {
      linear var io_slot_info_cell;
      glinear var io_slot_info_contents;
      io_slot_info_cell, io_slot_info_contents := new_cell(IOSlotRead(0)); // dummy value

      glinear var iocb;
      iocbs, iocb := glseq_take(iocbs, i as int);

      glinear var io_slot_access := IOSlotAccess(iocb, io_slot_info_contents); 

      var iocb_ptr := ptr_add(iocb_base_ptr, i as uint64 * SizeOfIocb());
      linear var slot_lock := new_basic_lock(io_slot_access, 
        (slot_access: IOSlotAccess) =>
          && slot_access.iocb.ptr == iocb_ptr
          && slot_access.io_slot_info.cell == io_slot_info_cell
      );
      linear var io_slot := IOSlot(
          iocb_ptr,
          io_slot_info_cell,
          slot_lock);
      lseq_give_inout(inout io_slots, i, io_slot);
    }

    ghost var disk_idx_of_entry := seq(CACHE_SIZE, (i) requires 0 <= i < CACHE_SIZE =>
        status_idx_array[i].idx);
    ghost var status := seq(CACHE_SIZE, (i) requires 0 <= i < CACHE_SIZE =>
        status_idx_array[i].status);
    ghost var read_refcounts :=
        seq(RC_WIDTH, (j) requires 0 <= j < RC_WIDTH =>
          seq(CACHE_SIZE, (i) requires 0 <= i < CACHE_SIZE =>
            read_refcounts_array[j * CACHE_SIZE + i]));
    ghost var cache_idx_of_page :=
        seq(NUM_DISK_PAGES, (i) requires 0 <= i < NUM_DISK_PAGES =>
          cache_idx_of_page_array[i]);

    c := Cache(
        data_base_ptr,
        iocb_base_ptr,
        read_refcounts_array,
        cache_idx_of_page_array,
        status_idx_array,
        data,
        disk_idx_of_entry,
        status,
        read_refcounts,
        cache_idx_of_page,
        global_clockpointer,
        io_slots,
        ioctx);
  }

}
