include "CacheTypes.i.dfy"

module CacheInit(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened IocbStruct
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened NativeTypes
  import opened Ptrs
  import opened Constants
  import opened GlinearMap
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
  import opened PageSizeConstant

  glinear method split_into_page_size_chunks(glinear pta: PointsToArray<byte>)
  returns (glinear pta_seq: map<nat, PointsToArray<byte>>)
  requires |pta.s| == PageSize as int * CACHE_SIZE as int
  ensures forall i {:trigger i in pta_seq} | 0 <= i < CACHE_SIZE as int ::
      i in pta_seq
        && 0 <= pta.ptr.as_nat() + i * PageSize as int < 0x1_0000_0000_0000_0000
        && pta_seq[i].ptr == ptr_add(pta.ptr, i as uint64 * PageSize)
        && |pta_seq[i].s| == PageSize as int

  glinear method iovec_split(glinear pta: PointsToArray<Iovec>)
  returns (glinear pta_seq: map<nat, PointsToArray<Iovec>>)
  requires |pta.s| == NUM_IO_SLOTS as int * PAGES_PER_EXTENT as int
  ensures forall i {:trigger i in pta_seq} | 0 <= i < NUM_IO_SLOTS as int ::
      i in pta_seq
        && 0 <= i * PAGES_PER_EXTENT as int * sizeof<Iovec>() as int
        && 0 <= pta.ptr.as_nat() + i * PAGES_PER_EXTENT as int * sizeof<Iovec>() as int
                < 0x1_0000_0000_0000_0000
        && pta_seq[i].ptr == ptr_add(pta.ptr, i as uint64 * PAGES_PER_EXTENT * sizeof<Iovec>())
        && |pta_seq[i].s| == PAGES_PER_EXTENT as int

  method init_batch_busy()
  returns (linear batch_busy: lseq<Atomic<bool, NullGhostType>>)
  ensures |batch_busy| == NUM_CHUNKS as int
  ensures (forall i :: 0 <= i < NUM_CHUNKS as int ==> lseq_has(batch_busy)[i])
  ensures (forall i, v, g :: 0 <= i < NUM_CHUNKS as int ==> atomic_inv(batch_busy[i], v, g) <==> true)
  {
    batch_busy := lseq_alloc<Atomic<bool, NullGhostType>>(NUM_CHUNKS);
    var i: uint64 := 0;
    while i < NUM_CHUNKS
    invariant 0 <= i as int <= NUM_CHUNKS as int
    invariant |batch_busy| == NUM_CHUNKS as int
    invariant (forall j :: i as int <= j < NUM_CHUNKS as int ==> !lseq_has(batch_busy)[j])
    invariant (forall j :: 0 <= j < i as int ==> lseq_has(batch_busy)[j])
    invariant (forall j, v, g :: 0 <= j < i as int ==> atomic_inv(batch_busy[j], v, g) <==> true)
    {
      linear var ato := new_atomic(false, NullGhostType, (v, g) => true, 0);
      lseq_give_inout(inout batch_busy, i, ato);
      i := i + 1;
    }
  }

  method init_ioslots()
  returns (iocb_base_ptr: Ptr, linear io_slots: lseq<IOSlot>)
  {
    glinear var iocbs;
    iocb_base_ptr, iocbs := new_iocb_array(NUM_IO_SLOTS);

    io_slots := lseq_alloc<IOSlot>(NUM_IO_SLOTS);

    var full_iovec_ptr;
    glinear var full_iovec;
    var dummy_iovec := new_iovec(nullptr(), 0);
    full_iovec_ptr, full_iovec := alloc_array(PAGES_PER_EXTENT * NUM_IO_SLOTS, dummy_iovec);
    glinear var iovecs := iovec_split(full_iovec);

    ghost var iocbs_copy := iocbs;

    var i3: uint64 := 0;
    while i3 < NUM_IO_SLOTS
    invariant 0 <= i3 as int <= NUM_IO_SLOTS as int
    invariant forall j | i3 as int <= j < NUM_IO_SLOTS as int ::
        j in iocbs && iocbs[j] == iocbs_copy[j]
    invariant |io_slots| == NUM_IO_SLOTS as int
    invariant forall j | i3 as int <= j < NUM_IO_SLOTS as int :: j !in io_slots
    invariant forall j | 0 <= j < i3 as int :: j in io_slots
        && io_slots[j].WF()
        && iocb_base_ptr.as_nat() + j * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
        && 0 <= j * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
        && io_slots[j].iocb_ptr == ptr_add(iocb_base_ptr, j as uint64 * SizeOfIocb())
    invariant forall j {:trigger j in iovecs} | i3 as int <= j < NUM_IO_SLOTS as int ::
      j in iovecs
        && 0 <= j * PAGES_PER_EXTENT as int * sizeof<Iovec>() as int
        && 0 <= full_iovec_ptr.as_nat() + j * PAGES_PER_EXTENT as int * sizeof<Iovec>() as int
                < 0x1_0000_0000_0000_0000
        && iovecs[j].ptr == ptr_add(full_iovec_ptr, j as uint64 * PAGES_PER_EXTENT * sizeof<Iovec>())
        && |iovecs[j].s| == PAGES_PER_EXTENT as int

    {
      assume false; // TODO timeout
      glinear var iocb;
      iocbs, iocb := glmap_take(iocbs, i3 as int);

      assert (i3 as int) in iovecs;
      assume 0 <= i3 as int * sizeof<Iovec>() as int;
      var iovec_ptr := ptr_add(full_iovec_ptr, i3 * PAGES_PER_EXTENT * sizeof<Iovec>());
      glinear var iovec;
      iovecs, iovec := glmap_take(iovecs, i3 as int);

      assert iovec.ptr == iovec_ptr;
      assert |iovec.s| == PAGES_PER_EXTENT as int;

      glinear var io_slot_access := IOSlotAccess(iocb, iovec);

      var iocb_ptr := ptr_add(iocb_base_ptr, i3 as uint64 * SizeOfIocb());
      linear var slot_lock := new_basic_lock(io_slot_access, 
        (slot_access: IOSlotAccess) =>
          && slot_access.iocb.ptr == iocb_ptr
          && slot_access.iovec.ptr == iovec_ptr
          && |slot_access.iovec.s| == PAGES_PER_EXTENT as int
      );
      linear var io_slot := IOSlot(
          iocb_ptr,
          iovec_ptr,
          slot_lock);
      assert io_slot.WF();
      lseq_give_inout(inout io_slots, i3, io_slot);

      i3 := i3 + 1;
    }

    dispose_anything(iocbs);
    dispose_anything(iovecs);
  }

  predicate refcount_i_inv(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        i': int, j': int, i: int)
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i' < i as int <= CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int
  {
    (j' * CACHE_SIZE as int + i') in read_refcounts_array
    && read_refcounts_array[j' * CACHE_SIZE as int + i'].inv(j')
    && read_refcounts_array[j' * CACHE_SIZE as int + i'].rwlock_loc
        == status_idx_array[i'].status.rwlock_loc
  }

  method init_cache(glinear init_tok: T.Token)
  returns (linear c: Cache)
  requires CacheSSM.Init(init_tok.val)
  ensures c.Inv()
  {
    var data_base_ptr;
    glinear var data_pta_full;
    data_base_ptr, data_pta_full := alloc_array_aligned<byte>(
        CACHE_SIZE * PageSize, 0, PageSize);
    glinear var data_pta_seq : map<nat, PointsToArray<byte>> :=
        split_into_page_size_chunks(data_pta_full);

    linear var read_refcounts_array := lseq_alloc<AtomicRefcount>(RC_WIDTH * CACHE_SIZE);
    linear var status_idx_array := lseq_alloc<StatusIdx>(CACHE_SIZE);

    glinear var dis, empty_seq := split_init(init_tok);

    ghost var data := seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
        data_pta_seq[i].ptr);

    ghost var data_pta_seq_copy := data_pta_seq;

    var i: uint64 := 0;
    while i < CACHE_SIZE
    invariant 0 <= i as int <= CACHE_SIZE as int
    invariant empty_seq == EmptySeq(i as nat, CACHE_SIZE as int)
    invariant forall j | i as int <= j < CACHE_SIZE as int :: 
        j in data_pta_seq && data_pta_seq[j] == data_pta_seq_copy[j]
    invariant |status_idx_array| == CACHE_SIZE as int
    invariant forall j | i as int <= j < CACHE_SIZE as int :: j !in status_idx_array
    invariant forall j | 0 <= j < i as int :: j in status_idx_array
        && status_idx_array[j].status.inv()
        && status_idx_array[j].status.key == Key(data[j], status_idx_array[j].idx, j)

    invariant |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
    invariant forall i', j' | i as int <= i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int ::
        (j' * CACHE_SIZE as int + i') !in read_refcounts_array
    invariant forall i', j' | 0 <= i' < i as int && 0 <= j' < RC_WIDTH as int ::
        refcount_i_inv(read_refcounts_array, status_idx_array, i', j', i as int)

    decreases CACHE_SIZE as int - i as int
    {
      assume false;
      linear var cell_idx;
      glinear var cell_idx_contents;
      cell_idx, cell_idx_contents := new_cell<int64>(0);
      glinear var data_pta;
      data_pta_seq, data_pta := glmap_take(data_pta_seq, i as nat);

      ghost var key := Key(data_pta.ptr, cell_idx, i as nat);

      glinear var cache_empty;
      cache_empty, empty_seq := pop_EmptySeq(empty_seq, i as nat, CACHE_SIZE as int);
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
      while j < RC_WIDTH
      invariant 0 <= i as int < CACHE_SIZE as int
      invariant 0 <= j as int <= RC_WIDTH as int
      invariant rcs.val == RwLock.Rcs(j as nat, RC_WIDTH as int)
      invariant rcs.loc == rwlock_loc

      invariant |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
      invariant forall i', j' | i as int < i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int ::
          (j' * CACHE_SIZE as int + i') !in read_refcounts_array
      invariant forall j' | j as int <= j' < RC_WIDTH as int ::
          (j' * CACHE_SIZE as int + i as int) !in read_refcounts_array
      invariant forall i', j' |
          (0 <= i' < i as int && 0 <= j' < RC_WIDTH as int) ::
        (j' * CACHE_SIZE as int + i') in read_refcounts_array
        && read_refcounts_array[j' * CACHE_SIZE as int + i'].inv(j')
        && read_refcounts_array[j' * CACHE_SIZE as int + i'].rwlock_loc
            == status_idx_array[i'].status.rwlock_loc
      invariant forall j': int |
          (0 <= j' < j as int) ::
        (j' * CACHE_SIZE as int + i as int) in read_refcounts_array
        && read_refcounts_array[j' * CACHE_SIZE as int + i as int].inv(j')
        && read_refcounts_array[j' * CACHE_SIZE as int + i as int].rwlock_loc
            == status_idx_array[i as int].status.rwlock_loc

      decreases RC_WIDTH as int - j as int
      {
        glinear var rc;
        rc, rcs := RwLockToken.pop_rcs(rcs, j as nat, RC_WIDTH as int);
        linear var ar_atomic := new_atomic(0, rc,
            (v, g) => AtomicRefcountImpl.state_inv(v, g, j as nat, rwlock_loc),
            0);
        linear var ar := AtomicRefcount(ar_atomic, rwlock_loc);

        // XXX I don't care about the perf of the initialization method, but do note
        // that the access pattern for writing to this array might be completely awful.
        lseq_give_inout(inout read_refcounts_array, j * CACHE_SIZE + i, ar);

        j := j + 1;
      }

      dispose_anything(rcs);

      i := i + 1;
    }

    assert {:split_here} true;

    linear var cache_idx_of_page_array := lseq_alloc(NUM_DISK_PAGES);

    var i2 := 0;
    while i2 < NUM_DISK_PAGES
    invariant 0 <= i2 as int <= NUM_DISK_PAGES as int
    invariant dis == IdxsSeq(i2 as nat, NUM_DISK_PAGES as int);
    invariant |cache_idx_of_page_array| == NUM_DISK_PAGES as int
    invariant forall j | i2 as int <= j < NUM_DISK_PAGES as int :: j !in cache_idx_of_page_array
    invariant forall j | 0 <= j < i2 as int :: j in cache_idx_of_page_array
        && atomic_index_lookup_inv(cache_idx_of_page_array[j], j)
    decreases NUM_DISK_PAGES as int - i2 as int
    {
      glinear var di;
      di, dis := pop_IdxSeq(dis, i2 as nat, NUM_DISK_PAGES as int);
      linear var ail := new_atomic(NOT_MAPPED, di,
          (v, g) => AtomicIndexLookupImpl.state_inv(v, g, i2 as nat),
          0);
      lseq_give_inout(inout cache_idx_of_page_array, i2, ail);
      i2 := i2 + 1;
    }

    dispose_anything(data_pta_seq);
    dispose_anything(empty_seq);
    dispose_anything(dis);

    linear var global_clockpointer := new_atomic(0 as uint32, NullGhostType, (v, g) => true, 0);
    linear var req_hand_base := new_atomic(0 as uint32, NullGhostType, (v, g) => true, 0);

    assert {:split_here} true;

    linear var io_slots;
    var iocb_base_ptr;
    iocb_base_ptr, io_slots := init_ioslots();

    ghost var disk_idx_of_entry := seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
        status_idx_array[i].idx);
    ghost var status := seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
        status_idx_array[i].status);
    ghost var read_refcounts :=
        seq(RC_WIDTH as int, (j) requires 0 <= j < RC_WIDTH as int =>
          seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
            read_refcounts_array[j * CACHE_SIZE as int + i]));
    ghost var cache_idx_of_page :=
        seq(NUM_DISK_PAGES as int, (i) requires 0 <= i < NUM_DISK_PAGES as int =>
          cache_idx_of_page_array[i]);

    linear var ioctx := aio.init_ctx(
      ((iocb_ptr, iocb, wp, g) =>
          ReadGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, wp, g)),
      ((iocb_ptr, iocb, p, g) =>
          WriteGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, p, g)),
      ((iocb_ptr, iocb, x, p, g) =>
          WritevGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, x, p, g)));

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
        req_hand_base,
        batch_busy,
        io_slots,
        ioctx);

    forall i | 0 <= i < CACHE_SIZE as int
    ensures data[i].aligned(PageSize as int)
    {
    }

    forall j, i | 0 <= j < RC_WIDTH as int && 0 <= i < CACHE_SIZE as int
    ensures read_refcounts[j][i].inv(j)
    ensures read_refcounts[j][i].rwlock_loc == status[i].rwlock_loc
    {
      assert read_refcounts[j][i] == 
          read_refcounts_array[j * CACHE_SIZE as int + i];
      assert read_refcounts_array[j * CACHE_SIZE as int + i].inv(j);
    }

    ghost var i0 := CACHE_SIZE as int - 1;
    assert i0 in data_pta_seq_copy;
    assert 0 <= data_pta_full.ptr.as_nat() + i0 * PageSize as int < 0x1_0000_0000_0000_0000;

    forall i | 0 <= i < RC_WIDTH as int * CACHE_SIZE as int
    ensures lseq_has(read_refcounts_array)[i]
    {
      var i1 := i % CACHE_SIZE as int;
      var j1 := i / CACHE_SIZE as int;
      assert i == j1 * CACHE_SIZE as int + i1;
      assert lseq_has(read_refcounts_array)[j1 * CACHE_SIZE as int + i1];
    }

    assert c.Inv();
  }

  method init_thread_local_state(t: uint64)
  returns (linear l: LocalState)
  ensures l.WF()
  {
    l := LocalState(t % RC_WIDTH, 0xffff_ffff_ffff_ffff, 0);
  }
}
