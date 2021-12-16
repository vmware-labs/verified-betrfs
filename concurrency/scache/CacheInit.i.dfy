include "CacheTypes.i.dfy"
include "MemSplit.i.dfy"

module CacheInit(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened IocbStruct
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened NativeTypes
  import opened ClientCounter
  import opened Ptrs
  import opened Constants
  import opened GlinearMap
  import opened CT = CacheTypes(aio)
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened CacheHandle
  import opened Atomics
  import opened Cells
  import T = DiskToken(CacheIfc, CacheSSM)
  import opened CacheResources
  import opened GlinearOption
  import opened CacheAIOParams
  import opened BasicLockImpl
  import opened MemSplit
  import opened GhostLoc
  import NonlinearLemmas
  import RwLockToken
  import RwLock
  import opened PageSizeConstant

  method init_batch_busy()
  returns (linear batch_busy: lseq<Atomic<bool, NullGhostType>>)
  ensures |batch_busy| == NUM_CHUNKS as int
  ensures (forall i :: 0 <= i < NUM_CHUNKS as int ==> lseq_has(batch_busy)[i])
  ensures (forall i, v, g :: 0 <= i < NUM_CHUNKS as int ==> atomic_inv(batch_busy[i], v, g) <==> true)
  {
    batch_busy := lseq_alloc<Atomic<bool, NullGhostType>>(NUM_CHUNKS_64());
    var i: uint64 := 0;
    while i < NUM_CHUNKS_64()
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
  ensures |io_slots| == NUM_IO_SLOTS as int
  ensures (forall i | 0 <= i < |io_slots| :: lseq_has(io_slots)[i])
  ensures (forall i | 0 <= i < |io_slots| :: io_slots[i].WF())
  ensures (forall i | 0 <= i < |io_slots| ::
          iocb_base_ptr.as_nat() + i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
          && 0 <= i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
          && io_slots[i].iocb_ptr == ptr_add(iocb_base_ptr, i as uint64 * SizeOfIocb())
       )

  {
    glinear var iocbs;
    iocb_base_ptr, iocbs := new_iocb_array(NUM_IO_SLOTS_64());

    io_slots := lseq_alloc<IOSlot>(NUM_IO_SLOTS_64());

    var full_iovec_ptr;
    glinear var full_iovec;
    var dummy_iovec := new_iovec(nullptr(), 0);
    full_iovec_ptr, full_iovec := alloc_array(PAGES_PER_EXTENT_64() * NUM_IO_SLOTS_64(), dummy_iovec);
    glinear var iovecs := mem_split(full_iovec, PAGES_PER_EXTENT, NUM_IO_SLOTS);

    ghost var iocbs_copy := iocbs;

    var i3: uint64 := 0;
    while i3 < NUM_IO_SLOTS_64()
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
    invariant forall j | i3 as int <= j < NUM_IO_SLOTS as int ::
        has_single(full_iovec, PAGES_PER_EXTENT, iovecs, j)
    {
      ghost var old_iovecs := iovecs;

      glinear var iocb;
      iocbs, iocb := glmap_take(iocbs, i3 as int);

      assert has_single(full_iovec, PAGES_PER_EXTENT, iovecs, i3 as int);
      assert (i3 as int) in iovecs;
      NonlinearLemmas.mul_ge_0(i3 as int, sizeof<Iovec>() as int);
      var iovec_ptr := ptr_add(full_iovec_ptr, i3 * PAGES_PER_EXTENT_64() * sizeof<Iovec>());
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

      assert forall j | i3 as int <= j < NUM_IO_SLOTS as int ::
          has_single(full_iovec, PAGES_PER_EXTENT, old_iovecs, j) ==>
          has_single(full_iovec, PAGES_PER_EXTENT, iovecs, j);
    }

    dispose_anything(iocbs);
    dispose_anything(iovecs);
  }

  predicate {:opaque} refcount_i_inv(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
        i': int, j': int)
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int
  {
    && var rci := rc_index(j' as uint64, i' as uint64) as int;
    && rci in read_refcounts_array
    && read_refcounts_array[rci].inv(j')
    && read_refcounts_array[rci].rwlock_loc
        == status_idx_array[i'].status.rwlock_loc
    && read_refcounts_array[rci].counter_loc
        == counter_loc
  }

  // something is messed up with dafny's triggers here.
  // use this trigger as a workaround
  predicate True(a: nat, b: nat) { true }

  predicate refcount_i_inv_i(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
        i: int)
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i <= CACHE_SIZE as int
  {
    && (forall i', j' {:trigger True(i',j')} |
          (0 <= i' < i as int && 0 <= j' < RC_WIDTH as int) ::
        refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j'))
  }

  predicate refcount_i_inv_ij(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
        i: int, j: int)
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i < CACHE_SIZE as int && 0 <= j <= RC_WIDTH as int
  {
    && (forall i', j' {:trigger True(i',j')} |
          (0 <= i' < i as int && 0 <= j' < RC_WIDTH as int) ::
        refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j'))
    && (forall j': int {:Trigger True(i,j')} |
          (0 <= j' < j as int) ::
        refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i, j'))
  }

  lemma refcount_i_inv_ij_base(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        status_idx_array': lseq<StatusIdx>,
        counter_loc: Loc,
        i: int)
  requires |status_idx_array'| == |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i < CACHE_SIZE
  requires forall k | 0 <= k < i :: k in status_idx_array && k in status_idx_array'
      && status_idx_array[k] == status_idx_array'[k]
  requires refcount_i_inv_i(read_refcounts_array, status_idx_array, counter_loc, i)
  ensures refcount_i_inv_ij(read_refcounts_array, status_idx_array', counter_loc, i, 0)
  {
    forall i', j' | (0 <= i' < i as int && 0 <= j' < RC_WIDTH as int)
    ensures refcount_i_inv(read_refcounts_array, status_idx_array', counter_loc, i', j');
    {
      assert True(i', j');
      assert refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j');
      reveal_refcount_i_inv();
    }
  }

  lemma refcount_i_inv_ij_inc(
        read_refcounts_array: lseq<AtomicRefcount>,
        read_refcounts_array': lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
        i: int, j: int)
  requires 0 <= i < CACHE_SIZE as int && 0 <= j < RC_WIDTH as int
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == |read_refcounts_array'| == RC_WIDTH * CACHE_SIZE
  requires forall k | 0 <= k < |read_refcounts_array| && k in read_refcounts_array
      :: k in read_refcounts_array' && read_refcounts_array'[k] == read_refcounts_array[k]
  requires refcount_i_inv_ij(read_refcounts_array, status_idx_array, counter_loc, i, j)
  requires refcount_i_inv(read_refcounts_array', status_idx_array, counter_loc, i, j)
  ensures refcount_i_inv_ij(read_refcounts_array', status_idx_array, counter_loc, i, j + 1)
  {
    forall i', j' | (0 <= i' < i as int && 0 <= j' < RC_WIDTH as int)
    ensures refcount_i_inv(read_refcounts_array', status_idx_array, counter_loc, i', j')
    {
      assert True(i', j');
      assert refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j');
      reveal_refcount_i_inv();
    }
    forall j': int | (0 <= j' < j as int + 1)
    ensures refcount_i_inv(read_refcounts_array', status_idx_array, counter_loc, i, j')
    {
      if j' == j {
        assert refcount_i_inv(read_refcounts_array', status_idx_array, counter_loc, i, j');
      } else {
        assert True(i, j');
        assert refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i, j');
        reveal_refcount_i_inv();
        assert refcount_i_inv(read_refcounts_array', status_idx_array, counter_loc, i, j');
      }
    }
  }

  lemma refcount_i_inv_ij_end(read_refcounts_array: lseq<AtomicRefcount>,
        status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
        i: int)
  requires |status_idx_array| == CACHE_SIZE
  requires |read_refcounts_array| == RC_WIDTH * CACHE_SIZE
  requires 0 <= i < CACHE_SIZE
  requires refcount_i_inv_ij(read_refcounts_array, status_idx_array, counter_loc, i, RC_WIDTH)
  ensures refcount_i_inv_i(read_refcounts_array, status_idx_array, counter_loc, i+1)
  {
    forall i', j' | (0 <= i' < i + 1 && 0 <= j' < RC_WIDTH)
    ensures refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j')
    {
      assert True(i', j');
    }
  }

  lemma refcount_i_inv_i_get(
      read_refcounts_array: lseq<AtomicRefcount>,
      status_idx_array: lseq<StatusIdx>,
        counter_loc: Loc,
      i: nat, i': nat, j': nat)
  requires |status_idx_array| == CACHE_SIZE as int
  requires |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
  requires 0 <= i <= CACHE_SIZE as int
  requires refcount_i_inv_i(read_refcounts_array, status_idx_array, counter_loc, i)
  requires 0 <= i' < i
  requires 0 <= j' < RC_WIDTH
  ensures refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j')
  {
    assert True(i', j');
    assert refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i', j');
  }

  lemma inverse_rc_index(k: int)
  returns (j: int, i: int)
  requires 0 <= k as int < RC_WIDTH as int * CACHE_SIZE as int
  ensures 0 <= j as int < RC_WIDTH as int
  ensures 0 <= i as int < CACHE_SIZE as int
  ensures k == rc_index(j as uint64, i as uint64) as int
  {
    j := k / CACHE_SIZE;
    var rc_number := k % CACHE_SIZE;

    var cacheline_capacity: int := (CACHE_SIZE_64() / PLATFORM_CACHELINE_SIZE_64()) as int;
    assert cacheline_capacity as int == CACHELINE_CAPACITY();

    i := (rc_number % (PLATFORM_CACHELINE_SIZE_64() as int)) * cacheline_capacity
        + (rc_number / (PLATFORM_CACHELINE_SIZE_64() as int));

    var rc_number2 := (i % cacheline_capacity) * (PLATFORM_CACHELINE_SIZE_64() as int)
        + (i / cacheline_capacity);

    calc {
      rc_number2 % (PLATFORM_CACHELINE_SIZE_64() as int);
      (i / cacheline_capacity);
      rc_number % (PLATFORM_CACHELINE_SIZE_64() as int);
    }

    calc {
      rc_number2 / (PLATFORM_CACHELINE_SIZE_64() as int);
      (i % cacheline_capacity);
      rc_number / (PLATFORM_CACHELINE_SIZE_64() as int);
    }

    assert rc_number == rc_number2;
    reveal_rc_index();
  }

  method init_cache(glinear init_tok: T.Token)
  returns (linear c: Cache, glinear counter: Clients)
  requires CacheSSM.Init(init_tok.val)
  ensures c.Inv()
  ensures counter.loc == c.counter_loc && counter.n == 255
  {
    counter := counter_init();
    ghost var counter_loc := counter.loc;

    var data_base_ptr;
    glinear var data_pta_full;
    sizeof_int_types();
    data_base_ptr, data_pta_full := alloc_array_hugetables<byte>(
        CACHE_SIZE_64() * PageSize64(), 0);
    glinear var data_pta_seq : map<nat, PointsToArray<byte>> :=
        mem_split(data_pta_full, PageSize as int, CACHE_SIZE);

    linear var read_refcounts_array := lseq_alloc<AtomicRefcount>(RC_WIDTH_64() * CACHE_SIZE_64());
    linear var status_idx_array := lseq_alloc<StatusIdx>(CACHE_SIZE_64());

    glinear var dis, empty_seq := split_init(init_tok);

    forall i | 0 <= i < CACHE_SIZE
    ensures i in data_pta_seq
    {
      assert has_single(data_pta_full, PageSize as int, data_pta_seq, i);
    }

    ghost var data := seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
        data_pta_seq[i].ptr);

    ghost var data_pta_seq_copy := data_pta_seq;

    var i: uint64 := 0;
    while i < CACHE_SIZE_64()
    invariant 0 <= i as int <= CACHE_SIZE as int
    invariant empty_seq == EmptySeq(i as nat, CACHE_SIZE as int)
    invariant forall j | i as int <= j < CACHE_SIZE as int :: 
        j in data_pta_seq && data_pta_seq[j] == data_pta_seq_copy[j]
    invariant |status_idx_array| == CACHE_SIZE as int
    invariant forall j | i as int <= j < CACHE_SIZE as int :: j !in status_idx_array
    invariant forall j | 0 <= j < i as int :: j in status_idx_array
        && status_idx_array[j].status.inv()
        && status_idx_array[j].status.key == Key(data[j], status_idx_array[j].page_handle, j)

    invariant |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
    invariant forall i', j' | i as int <= i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int ::
        (rc_index(j' as uint64, i' as uint64) as int) !in read_refcounts_array
    invariant refcount_i_inv_i(read_refcounts_array, status_idx_array, counter_loc, i as int)

    decreases CACHE_SIZE as int - i as int
    {
      linear var cell_idx;
      glinear var cell_idx_contents;

      assert has_single(data_pta_full, PageSize as int, data_pta_seq_copy, i as int);
      assert data_base_ptr.as_nat() == data_pta_full.ptr.as_nat();
      sizeof_int_types();
      assert 0 <= data_base_ptr.as_nat() + i as int * PageSize < 0x1_0000_0000_0000_0000;

      cell_idx, cell_idx_contents := new_cell<PageHandle>(PageHandle(
          ptr_add(data_base_ptr, i * PageSize64()),
          0));
      glinear var data_pta;

      data_pta_seq, data_pta := glmap_take(data_pta_seq, i as nat);

      assert ptr_add(data_base_ptr, i * PageSize64())
          == data_pta.ptr;

      ghost var key := Key(data_pta.ptr, cell_idx, i as nat);

      glinear var cache_empty;
      cache_empty, empty_seq := pop_EmptySeq(empty_seq, i as nat, CACHE_SIZE as int);
      glinear var handle := CacheEmptyHandle(key, cache_empty, cell_idx_contents, data_pta);
      glinear var central, rcs := RwLockToken.perform_Init(handle);
      ghost var rwlock_loc := central.loc;

      assert AtomicStatusImpl.state_inv(flag_unmapped(), 
          AtomicStatusImpl.G(central, glNone),
          key, rwlock_loc);
      linear var atomic_status_atomic := new_atomic(
          flag_unmapped(),
          AtomicStatusImpl.G(central, glNone),
          (v, g) => AtomicStatusImpl.state_inv(v, g, key, rwlock_loc),
          0);
      linear var atomic_status := AtomicStatus(
          atomic_status_atomic,
          rwlock_loc,
          key);

      linear var status_idx := StatusIdx(atomic_status, cell_idx);
      ghost var sia := status_idx_array;
      lseq_give_inout(inout status_idx_array, i, status_idx);

      refcount_i_inv_ij_base(read_refcounts_array, sia, status_idx_array, counter_loc, i as int);

      var j : uint64 := 0;
      while j < RC_WIDTH_64()
      invariant 0 <= i as int < CACHE_SIZE as int
      invariant 0 <= j as int <= RC_WIDTH as int
      invariant rcs.val == RwLock.Rcs(j as nat, RC_WIDTH as int)
      invariant rcs.loc == rwlock_loc

      invariant |read_refcounts_array| == RC_WIDTH as int * CACHE_SIZE as int
      invariant forall i', j' | i as int < i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int ::
          rc_index(j' as uint64, i' as uint64) as int !in read_refcounts_array
      invariant forall j' | j as int <= j' < RC_WIDTH as int ::
          rc_index(j' as uint64, i as uint64) as int !in read_refcounts_array
      invariant refcount_i_inv_ij(read_refcounts_array, status_idx_array, counter_loc, i as int, j as int)

      decreases RC_WIDTH as int - j as int
      {
        glinear var rc;
        rc, rcs := RwLockToken.pop_rcs(rcs, j as nat, RC_WIDTH as int);
        glinear var empty_c := empty_counter(counter_loc);
        glinear var rg := RG(rc, empty_c);
        linear var ar_atomic := new_atomic(0, rg,
            (v, g) => AtomicRefcountImpl.state_inv(v, g, j as nat, rwlock_loc, counter_loc),
            0);
        linear var ar := AtomicRefcount(ar_atomic, rwlock_loc, counter_loc);

        ghost var rra := read_refcounts_array;

        // XXX I don't care about the perf of the initialization method, but do note
        // that the access pattern for writing to this array might be completely awful.
        lseq_give_inout(inout read_refcounts_array, rc_index(j, i), ar);

        assert refcount_i_inv(read_refcounts_array, status_idx_array, counter_loc, i as int, j as int) by {
          reveal_refcount_i_inv();
        }

        refcount_i_inv_ij_inc(rra, read_refcounts_array, status_idx_array, counter_loc, i as int, j as int);

        j := j + 1;

        forall i', j' | i as int < i' < CACHE_SIZE as int && 0 <= j' < RC_WIDTH as int
        //ensures rc_index(j' as uint64, i' as uint64) as int !in read_refcounts_array
        ensures rc_index(j' as uint64, i' as uint64) != rc_index(j-1, i)
        {
          reveal_rc_index();
          var cacheline_capacity := CACHE_SIZE_64() / PLATFORM_CACHELINE_SIZE_64();
          assert cacheline_capacity as int == CACHELINE_CAPACITY();
          assert rc_index(j' as uint64, i' as uint64) != rc_index(j-1, i);
        }
        /*
        forall j' | j as int <= j' < RC_WIDTH as int
        ensures rc_index(j' as uint64, i as uint64) as int !in read_refcounts_array
        {
          reveal_rc_index();
        }
        */
        reveal_rc_index();
      }

      refcount_i_inv_ij_end(read_refcounts_array, status_idx_array, counter_loc, i as int);
      dispose_anything(rcs);

      i := i + 1;
    }

    assert {:split_here} true;

    linear var cache_idx_of_page_array := lseq_alloc(NUM_DISK_PAGES_64());

    var i2 := 0;
    while i2 < NUM_DISK_PAGES_64()
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
      linear var ail := new_atomic(NOT_MAPPED as uint32, di,
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
        status_idx_array[i].page_handle);
    ghost var status := seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
        status_idx_array[i].status);
    ghost var read_refcounts :=
        seq(RC_WIDTH as int, (j) requires 0 <= j < RC_WIDTH as int =>
          seq(CACHE_SIZE as int, (i) requires 0 <= i < CACHE_SIZE as int =>
            read_refcounts_array[rc_index(j as uint64, i as uint64) as int]));
    ghost var cache_idx_of_page :=
        seq(NUM_DISK_PAGES as int, (i) requires 0 <= i < NUM_DISK_PAGES as int =>
          cache_idx_of_page_array[i]);

    linear var ioctx := aio.init_ctx(
      ((iocb_ptr, iocb, wp, g) =>
          ReadGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, wp, g)),
      ((iocb_ptr, iocb, p, g) =>
          WriteGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, p, g)),
      ((iocb_ptr, iocb, x, p, g) =>
          ReadvGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, x, p, g)),
      ((iocb_ptr, iocb, x, p, g) =>
          WritevGInv(io_slots, data, disk_idx_of_entry, status, iocb_ptr, iocb, x, p, g))
    );

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
        ioctx,
        counter_loc);

    forall i | 0 <= i < CACHE_SIZE as int
    ensures data[i].aligned(PageSize as int)
    {
      assert has_single(data_pta_full, PageSize as int, data_pta_seq_copy, i as int);
      assert data_base_ptr.as_nat() == data_pta_full.ptr.as_nat();
      sizeof_int_types();
      assert data[i].aligned(PageSize as int);
    }

    forall j, i | 0 <= j < RC_WIDTH as int && 0 <= i < CACHE_SIZE as int
    ensures read_refcounts[j][i].inv(j)
    ensures read_refcounts[j][i].rwlock_loc == status[i].rwlock_loc
    {
      refcount_i_inv_i_get(read_refcounts_array, status_idx_array, counter_loc, CACHE_SIZE, i, j);
      reveal_refcount_i_inv();
      var rci := rc_index(j as uint64, i as uint64) as int;
      assert read_refcounts[j][i] == 
          read_refcounts_array[rci];
      assert read_refcounts_array[rci].inv(j);
    }

    ghost var i0 := CACHE_SIZE as int - 1;
    assert i0 in data_pta_seq_copy;
    assert data_base_ptr.as_nat() == data_pta_full.ptr.as_nat();
    assert 0 <= data_pta_full.ptr.as_nat() + i0 * PageSize as int < 0x1_0000_0000_0000_0000
    by {
      assert has_single(data_pta_full, PageSize as int, data_pta_seq_copy, i0);
      sizeof_int_types();
    }

    forall i | 0 <= i < RC_WIDTH as int * CACHE_SIZE as int
    ensures lseq_has(read_refcounts_array)[i]
    {
      var j1, i1 := inverse_rc_index(i);
      var rci := rc_index(j1 as uint64, i1 as uint64) as int;
      assert i == rci;
      refcount_i_inv_i_get(read_refcounts_array, status_idx_array, counter_loc, CACHE_SIZE, i1, j1);
      reveal_refcount_i_inv();
      assert lseq_has(read_refcounts_array)[rci];
    }

    forall j, i {:trigger c.read_refcounts[j][i]}
        | 0 <= j < RC_WIDTH as int && 0 <= i < CACHE_SIZE as int
    ensures c.read_refcounts[j][i].inv(j)
    ensures c.read_refcounts[j][i].rwlock_loc == c.status[i].rwlock_loc
    ensures c.read_refcounts[j][i].counter_loc == counter_loc
    {
      refcount_i_inv_i_get(read_refcounts_array, status_idx_array, counter_loc, CACHE_SIZE, i, j);
      reveal_refcount_i_inv();
    }

    forall i | 0 <= i < CACHE_SIZE as int
    ensures c.data[i] == ptr_add(c.data_base_ptr, (PageSize as int * i) as uint64)
    {
      assert has_single(data_pta_full, PageSize as int, data_pta_seq_copy, i);
      sizeof_int_types();
      assert c.data[i] == ptr_add(c.data_base_ptr, (PageSize as int * i) as uint64);
    }

    assert c.Inv();
  }

  method init_thread_local_state(t: uint64)
  returns (linear l: LocalState)
  ensures l.WF()
  {
    l := LocalState(t % RC_WIDTH_64(), 0xffff_ffff_ffff_ffff, 0);
  }
}
