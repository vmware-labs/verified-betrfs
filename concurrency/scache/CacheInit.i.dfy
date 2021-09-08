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
  import RwLockToken
  import RwLock

  glinear method split_into_page_size_chunks(glinear pta: PointsToArray<byte>)
  returns (glinear pta_seq: glseq<PointsToArray<byte>>)
  requires |pta.s| == PageSize * CACHE_SIZE
  ensures pta_seq.len() == CACHE_SIZE
  ensures forall i {:trigger pta_seq.has(i)} | 0 <= i < CACHE_SIZE ::
      pta_seq.has(i)
        && 0 <= pta.ptr.as_nat() + i * PageSize < 0x1_0000_0000_0000_0000
        && pta_seq.get(i).ptr == ptr_add(pta.ptr, i as uint64 * PageSize as uint64)
        && |pta_seq.get(i).s| == PageSize

  method init_batch_busy()
  returns (linear batch_busy: lseq<Atomic<bool, NullGhostType>>)
  ensures |batch_busy| == NUM_CHUNKS
  ensures (forall i :: 0 <= i < NUM_CHUNKS ==> lseq_has(batch_busy)[i])
  ensures (forall i, v, g :: 0 <= i < NUM_CHUNKS ==> atomic_inv(batch_busy[i], v, g) <==> true)

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

    linear var read_refcounts_array := lseq_alloc<AtomicRefcount>(RC_WIDTH as uint64 * CACHE_SIZE as uint64);
    linear var status_idx_array := lseq_alloc<StatusIdx>(CACHE_SIZE as uint64);

    glinear var dis, empty_seq := split_init(init_tok);

    ghost var data := seq(CACHE_SIZE, (i) requires 0 <= i < CACHE_SIZE =>
        data_pta_seq.get(i).ptr);

    ghost var data_pta_seq_copy := data_pta_seq;

    var i: uint64 := 0;
    while i < CACHE_SIZE as uint64
    invariant 0 <= i as int <= CACHE_SIZE
    invariant empty_seq == EmptySeq(i as nat, CACHE_SIZE)
    invariant data_pta_seq.len() == CACHE_SIZE
    invariant forall j | i as int <= j < CACHE_SIZE :: 
        data_pta_seq.has(j) && data_pta_seq.get(j) == data_pta_seq_copy.get(j)
    invariant |status_idx_array| == CACHE_SIZE
    invariant forall j | i as int <= j < CACHE_SIZE :: j !in status_idx_array
    invariant forall j | 0 <= j < i as int :: j in status_idx_array
        && status_idx_array[j].status.inv()
        && status_idx_array[j].status.key == Key(data[j], status_idx_array[j].idx, j)

    invariant |read_refcounts_array| == RC_WIDTH * CACHE_SIZE
    invariant forall i', j' | i as int <= i' < CACHE_SIZE && 0 <= j' < RC_WIDTH ::
        (j' * CACHE_SIZE + i') !in read_refcounts_array
    invariant forall i', j' | 0 <= i' < i as int && 0 <= j' < RC_WIDTH ::
        (j' * CACHE_SIZE + i') in read_refcounts_array
        && read_refcounts_array[j' * CACHE_SIZE + i'].inv(j')
        && read_refcounts_array[j' * CACHE_SIZE + i'].rwlock_loc
            == status_idx_array[i'].status.rwlock_loc

    decreases CACHE_SIZE - i as int
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
      invariant 0 <= i as int < CACHE_SIZE
      invariant 0 <= j as int <= RC_WIDTH
      invariant rcs.val == RwLock.Rcs(j as nat, RC_WIDTH)
      invariant rcs.loc == rwlock_loc

      invariant |read_refcounts_array| == RC_WIDTH * CACHE_SIZE
      invariant forall i', j' | i as int < i' < CACHE_SIZE && 0 <= j' < RC_WIDTH ::
          (j' * CACHE_SIZE as int + i') !in read_refcounts_array
      invariant forall j' | j as int <= j' < RC_WIDTH ::
          (j' * CACHE_SIZE as int + i as int) !in read_refcounts_array
      invariant forall i', j' |
          (0 <= i' < i as int && 0 <= j' < RC_WIDTH) ::
        (j' * CACHE_SIZE + i') in read_refcounts_array
        && read_refcounts_array[j' * CACHE_SIZE + i'].inv(j')
        && read_refcounts_array[j' * CACHE_SIZE + i'].rwlock_loc
            == status_idx_array[i'].status.rwlock_loc
      invariant forall j': int |
          (0 <= j' < j as int) ::
        (j' * CACHE_SIZE + i as int) in read_refcounts_array
        && read_refcounts_array[j' * CACHE_SIZE + i as int].inv(j')
        && read_refcounts_array[j' * CACHE_SIZE + i as int].rwlock_loc
            == status_idx_array[i as int].status.rwlock_loc

      decreases RC_WIDTH - j as int
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

    assert {:split_here} true;

    linear var cache_idx_of_page_array := lseq_alloc(NUM_DISK_PAGES as uint64);

    var i2 := 0;
    while i2 < NUM_DISK_PAGES as uint64
    invariant 0 <= i2 as int <= NUM_DISK_PAGES
    invariant dis == IdxsSeq(i2 as nat, NUM_DISK_PAGES);
    invariant |cache_idx_of_page_array| == NUM_DISK_PAGES
    invariant forall j | i2 as int <= j < NUM_DISK_PAGES :: j !in cache_idx_of_page_array
    invariant forall j | 0 <= j < i2 as int :: j in cache_idx_of_page_array
        && atomic_index_lookup_inv(cache_idx_of_page_array[j], j)
    decreases NUM_DISK_PAGES - i2 as int
    {
      glinear var di;
      di, dis := pop_IdxSeq(dis, i2 as nat, NUM_DISK_PAGES);
      linear var ail := new_atomic(NOT_MAPPED, di,
          (v, g) => AtomicIndexLookupImpl.state_inv(v, g, i2 as nat),
          0);
      lseq_give_inout(inout cache_idx_of_page_array, i2, ail);
      i2 := i2 + 1;
    }

    dispose_anything(data_pta_seq);
    dispose_anything(empty_seq);
    dispose_anything(dis);

    linear var global_clockpointer := new_atomic(0, NullGhostType, (v, g) => true, 0);
    linear var io_slots := lseq_alloc<IOSlot>(NUM_IO_SLOTS as uint64);

    ghost var iocbs_copy := iocbs;

    assert {:split_here} true;

    var i3 := 0;
    while i3 < NUM_IO_SLOTS as uint64
    invariant 0 <= i3 as int <= NUM_IO_SLOTS
    invariant iocbs.len() == NUM_IO_SLOTS
    invariant forall j | i3 as int <= j < NUM_IO_SLOTS :: 
        iocbs.has(j) && iocbs.get(j) == iocbs_copy.get(j)
    invariant |io_slots| == NUM_IO_SLOTS
    invariant forall j | i3 as int <= j < NUM_IO_SLOTS :: j !in io_slots
    invariant forall j | 0 <= j < i3 as int :: j in io_slots
        && io_slots[j].WF()
        && iocb_base_ptr.as_nat() + j * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
        && 0 <= j * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
        && io_slots[j].iocb_ptr == ptr_add(iocb_base_ptr, j as uint64 * SizeOfIocb())
    {
      linear var io_slot_info_cell;
      glinear var io_slot_info_contents;
      io_slot_info_cell, io_slot_info_contents := new_cell(IOSlotRead(0)); // dummy value

      glinear var iocb;
      iocbs, iocb := glseq_take(iocbs, i3 as int);

      glinear var io_slot_access := IOSlotAccess(iocb, io_slot_info_contents); 

      var iocb_ptr := ptr_add(iocb_base_ptr, i3 as uint64 * SizeOfIocb());
      linear var slot_lock := new_basic_lock(io_slot_access, 
        (slot_access: IOSlotAccess) =>
          && slot_access.iocb.ptr == iocb_ptr
          && slot_access.io_slot_info.cell == io_slot_info_cell
      );
      linear var io_slot := IOSlot(
          iocb_ptr,
          io_slot_info_cell,
          slot_lock);
      lseq_give_inout(inout io_slots, i3, io_slot);

      i3 := i3 + 1;
    }

    assert {:split_here} true;

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

    linear var ioctx := aio.init_ctx(
      ((iocb_ptr, iocb, wp, g) =>
          ReadGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, wp, g)),
      ((iocb_ptr, iocb, p, g) =>
          WriteGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, p, g)));

    dispose_anything(iocbs);

    linear var batch_busy := init_batch_busy();

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
        batch_busy,
        io_slots,
        ioctx);

    forall i | 0 <= i < CACHE_SIZE
    ensures data[i].aligned(PageSize)
    {
    }

    forall j, i | 0 <= j < RC_WIDTH && 0 <= i < CACHE_SIZE
    ensures read_refcounts[j][i].inv(j)
    ensures read_refcounts[j][i].rwlock_loc == status[i].rwlock_loc
    {
      assert read_refcounts[j][i] == 
          read_refcounts_array[j * CACHE_SIZE + i];
      assert read_refcounts_array[j * CACHE_SIZE + i].inv(j);
    }

    var i0 := CACHE_SIZE - 1;
    assert data_pta_seq_copy.has(i0);
    assert 0 <= data_pta_full.ptr.as_nat() + i0 * PageSize < 0x1_0000_0000_0000_0000;

    forall i | 0 <= i < RC_WIDTH * CACHE_SIZE
    ensures lseq_has(read_refcounts_array)[i]
    {
      var i1 := i % CACHE_SIZE;
      var j1 := i / CACHE_SIZE;
      assert i == j1 * CACHE_SIZE + i1;
      assert lseq_has(read_refcounts_array)[j1 * CACHE_SIZE + i1];
    }

    assert c.Inv();
  }

}
