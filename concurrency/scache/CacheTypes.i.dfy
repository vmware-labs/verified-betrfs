include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"
include "AtomicIndexLookup.i.dfy"
include "../framework/Ptrs.s.dfy"
include "BasicLock.i.dfy"
include "../framework/AIO.s.dfy"
include "cache/CacheSM.i.dfy"
include "CacheAIOParams.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"

module CacheTypes(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened Ptrs
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened AtomicStatusImpl
  import opened Atomics
  import opened Constants
  import opened NativeTypes
  import opened BasicLockImpl
  import opened CacheHandle
  import opened IocbStruct
  import opened CacheAIOParams
  import opened LinearSequence_i
  import opened LinearSequence_s
  import RwLockToken
  import opened Cells
  import opened PageSizeConstant

  glinear datatype NullGhostType = NullGhostType

  linear datatype StatusIdx = StatusIdx(
    linear status: AtomicStatus,
    linear page_handle: Cell<PageHandle>
  )

  linear datatype Cache = Cache(
    data_base_ptr: Ptr,
    iocb_base_ptr: Ptr,
    linear read_refcounts_array: lseq<AtomicRefcount>,
    linear cache_idx_of_page_array: lseq<AtomicIndexLookup>,
    linear status_idx_array: lseq<StatusIdx>,

    ghost data: seq<Ptr>,
    ghost page_handles: seq<Cell<PageHandle>>,
    ghost status: seq<AtomicStatus>,

    ghost read_refcounts: seq<seq<AtomicRefcount>>,

    ghost cache_idx_of_page: seq<AtomicIndexLookup>,

    linear global_clockpointer: Atomic<uint32, NullGhostType>,
    linear req_hand_base: Atomic<uint32, NullGhostType>,
    linear batch_busy: lseq<Atomic<bool, NullGhostType>>,

    linear io_slots: lseq<IOSlot>,
    linear ioctx: aio.IOCtx
  )
  {
    function key(i: int) : Key
    requires 0 <= i < |this.data|
    requires 0 <= i < |this.page_handles|
    {
      Key(this.data[i], this.page_handles[i], i)
    }

    predicate Inv()
    {
      && |this.data| == CACHE_SIZE as int
      && |this.page_handles| == CACHE_SIZE as int
      && |this.status| == CACHE_SIZE as int
      && (forall i | 0 <= i < CACHE_SIZE as int ::
         && this.status[i].key == this.key(i)
         && this.status[i].inv()
        )
      && |this.read_refcounts| == RC_WIDTH as int
      && (forall j | 0 <= j < RC_WIDTH as int ::
          |this.read_refcounts[j]| == CACHE_SIZE as int)
      && (forall j, i | 0 <= j < RC_WIDTH as int && 0 <= i < CACHE_SIZE as int ::
          && this.read_refcounts[j][i].inv(j)
          && this.read_refcounts[j][i].rwlock_loc == this.status[i].rwlock_loc)
      && |this.cache_idx_of_page| == NUM_DISK_PAGES as int
      && (forall d | 0 <= d < NUM_DISK_PAGES as int ::
          atomic_index_lookup_inv(this.cache_idx_of_page[d], d))
      && |io_slots| == NUM_IO_SLOTS as int
      && (forall i | 0 <= i < |io_slots| :: lseq_has(io_slots)[i])
      && (forall i | 0 <= i < |io_slots| :: io_slots[i].WF())
      && (forall i | 0 <= i < |io_slots| ::
            this.iocb_base_ptr.as_nat() + i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
            && 0 <= i * SizeOfIocb() as int < 0x1_0000_0000_0000_0000
            && io_slots[i].iocb_ptr == ptr_add(this.iocb_base_ptr, i as uint64 * SizeOfIocb())
         )

      && (forall iocb_ptr, iocb, wp, g :: ioctx.async_read_inv(iocb_ptr, iocb, wp, g)
        <==> ReadGInv(io_slots, data, page_handles, status,
                  iocb_ptr, iocb, wp, g))

      && (forall iocb_ptr, iocb, wp, g :: ioctx.async_write_inv(iocb_ptr, iocb, wp, g)
        <==> WriteGInv(io_slots, data, page_handles, status,
                  iocb_ptr, iocb, wp, g))

      && (forall iocb_ptr, iocb, iovec, datas, g :: ioctx.async_writev_inv(iocb_ptr, iocb, iovec, datas, g)
        <==> WritevGInv(io_slots, data, page_handles, status,
                  iocb_ptr, iocb, iovec, datas, g))

      && (forall iocb_ptr, iocb, iovec, datas, g :: ioctx.async_readv_inv(iocb_ptr, iocb, iovec, datas, g)
        <==> ReadvGInv(io_slots, data, page_handles, status,
                  iocb_ptr, iocb, iovec, datas, g))

      && (forall v, g :: atomic_inv(global_clockpointer, v, g) <==> true)
      && (forall v, g :: atomic_inv(req_hand_base, v, g) <==> true)

      && (forall i | 0 <= i < CACHE_SIZE as int ::
        this.data[i].aligned(PageSize as int))

      && this.data_base_ptr.as_nat() + PageSize as int * (CACHE_SIZE as int - 1) < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < CACHE_SIZE as int ::
        && this.data[i] == ptr_add(this.data_base_ptr, (PageSize as int * i) as uint64))

      && |lseqs_raw(this.cache_idx_of_page_array)| == NUM_DISK_PAGES as int
      && (forall i | 0 <= i < NUM_DISK_PAGES as int :: lseq_has(this.cache_idx_of_page_array)[i]
          && lseq_peek(this.cache_idx_of_page_array, i as uint64) == this.cache_idx_of_page[i])

      && |lseqs_raw(this.read_refcounts_array)| == RC_WIDTH as int * CACHE_SIZE as int
      && (forall i | 0 <= i < RC_WIDTH as int * CACHE_SIZE as int :: lseq_has(this.read_refcounts_array)[i])
      && (forall j, i | 0 <= j < RC_WIDTH as int && 0 <= i < CACHE_SIZE as int ::
          lseq_peek(this.read_refcounts_array, (j * CACHE_SIZE as int + i) as uint64)
              == this.read_refcounts[j][i])

      && |lseqs_raw(this.status_idx_array)| == CACHE_SIZE as int
      && (forall i | 0 <= i < CACHE_SIZE as int :: lseq_has(this.status_idx_array)[i]
        && lseq_peek(this.status_idx_array, i as uint64)
            == StatusIdx(this.status[i], this.page_handles[i])
      )
      /*
      && this.read_refcounts_base_ptr.as_nat() + (RC_WIDTH-1) * CACHE_SIZE as int * (CACHE_SIZE as int -1) < 0x1_0000_0000_0000_0000
      && this.read_refcounts_gshared.len() == RC_WIDTH
      && (forall j | 0 <= j < RC_WIDTH ::
          && this.read_refcounts_gshared.has(j)
          && this.read_refcounts_gshared.get(j).len() == CACHE_SIZE as int)
      && (forall j, i | 0 <= j < RC_WIDTH && 0 <= i < CACHE_SIZE as int ::
          && this.read_refcounts[j][i].a.ptr ==
              ptr_add(this.read_refcounts_base_ptr, (j * CACHE_SIZE as int + i) as uint64)
          && this.read_refcounts_gshared.get(j).has(i)
          && this.read_refcounts[j][i].a.ga ==
              this.read_refcounts_gshared.get(j).get(i))
      */

      && |this.batch_busy| == NUM_CHUNKS as int
      && (forall i :: 0 <= i < NUM_CHUNKS as int ==> lseq_has(this.batch_busy)[i])
      && (forall i, v, g :: 0 <= i < NUM_CHUNKS as int ==> atomic_inv(this.batch_busy[i], v, g) <==> true)
    }

    shared function method data_ptr(i: uint64) : (p: Ptr)
    requires this.Inv()
    requires 0 <= i as int < CACHE_SIZE as int
    ensures p == this.data[i]
    {
      ptr_add(this.data_base_ptr, PageSize64() * i)
    }

    shared function method status_atomic(i: uint64) : (shared at: AtomicStatus)
    requires this.Inv()
    requires 0 <= i as int < CACHE_SIZE as int
    ensures at == this.status[i]
    {
      lseq_peek(this.status_idx_array, i as uint64).status
    }

    shared function method page_handle_ptr(i: uint64) : (shared c: Cell<PageHandle>)
    requires this.Inv()
    requires 0 <= i as int < CACHE_SIZE as int
    ensures c == this.page_handles[i]
    {
      lseq_peek(this.status_idx_array, i as uint64).page_handle
    }

    shared function method read_refcount_atomic(j: uint64, i: uint64) : (shared at: AtomicRefcount)
    requires this.Inv()
    requires 0 <= j as int < RC_WIDTH as int
    requires 0 <= i as int < CACHE_SIZE as int
    ensures at == this.read_refcounts[j][i]
    {
      lseq_peek(this.read_refcounts_array, j * CACHE_SIZE_64() + i)
    }

    shared function method cache_idx_of_page_atomic(i: uint64) : (shared at: AtomicIndexLookup)
    requires this.Inv()
    requires 0 <= i as int < NUM_DISK_PAGES as int
    ensures at == this.cache_idx_of_page[i]
    {
      lseq_peek(this.cache_idx_of_page_array, i)
    }
  }

  linear datatype LocalState = LocalState(
    t: uint64,
    free_hand: uint64,
    io_slot_hand: uint64
  )
  {
    predicate WF()
    {
      && (0 <= this.free_hand as int < NUM_CHUNKS as int || this.free_hand == 0xffff_ffff_ffff_ffff)
      && 0 <= t as int < RC_WIDTH as int
      && 0 <= io_slot_hand as int <= NUM_IO_SLOTS as int
    }
  }

  ////////////////////////////////////////
  //// IO stuff

  linear datatype IOSlot = IOSlot(
    iocb_ptr: Ptr,
    iovec_ptr: Ptr,
    linear lock: pre_BasicLock<IOSlotAccess>)
  {
    predicate WF()
    {
      && lock.wf()
      && (forall slot_access: IOSlotAccess :: this.lock.inv(slot_access) <==>
        && slot_access.iocb.ptr == this.iocb_ptr
        && slot_access.iovec.ptr == this.iovec_ptr
        && |slot_access.iovec.s| == PAGES_PER_EXTENT as int
      )
    }
  }

  predicate is_slot_access(io_slot: IOSlot, io_slot_access: IOSlotAccess)
  {
    && io_slot.iocb_ptr == io_slot_access.iocb.ptr
    && io_slot.iovec_ptr == io_slot_access.iovec.ptr
    && |io_slot_access.iovec.s| == PAGES_PER_EXTENT as int
  }

  predicate ReadGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_page_handles: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      iocb_ptr: Ptr,
      iocb: Iocb,
      data: PointsToArray<byte>,
      g: ReadG)
  {
    && iocb.IocbRead?
    && iocb.ptr == iocb_ptr
    && g.slot_idx < NUM_IO_SLOTS as int
    && |cache_io_slots| == NUM_IO_SLOTS as int
    && iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && 0 <= g.key.cache_idx < CACHE_SIZE as int
    && 0 <= iocb.offset < NUM_DISK_PAGES as int
    && |cache_data| == CACHE_SIZE as int
    && |cache_page_handles| == CACHE_SIZE as int
    && |cache_status| == CACHE_SIZE as int
    && data.ptr == cache_data[g.key.cache_idx]
    && iocb.nbytes == PageSize as int
    && g.idx.cell == cache_page_handles[g.key.cache_idx]
    && g.idx.v.disk_addr as int == iocb.offset * PageSize
    && g.idx.v.data_ptr == cache_data[g.key.cache_idx]
    && iocb.offset == g.cache_reading.disk_idx
    && g.cache_reading.cache_idx == g.key.cache_idx
    && g.ro.loc == cache_status[g.key.cache_idx].rwlock_loc
    && g.ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
    && g.iovec.ptr == cache_io_slots[g.slot_idx].iovec_ptr
    && |g.iovec.s| == PAGES_PER_EXTENT as int
    && iocb.buf == cache_data[g.key.cache_idx]
  }

  predicate simpleWriteGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_page_handles: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      offset: nat,
      data: seq<byte>,
      key: Key,
      wbo: T.WritebackObtainedToken)
  {
    && wbo.b.CacheEntryHandle?
    && 0 <= wbo.b.key.cache_idx < CACHE_SIZE as int
    && wbo.is_handle(key)
    && |cache_data| == CACHE_SIZE as int
    && |cache_page_handles| == CACHE_SIZE as int
    && |cache_status| == CACHE_SIZE as int
    && key.data_ptr == cache_data[key.cache_idx]
    && key.idx_cell == cache_page_handles[key.cache_idx]
    && wbo.token.loc == cache_status[wbo.b.key.cache_idx as nat].rwlock_loc
    && wbo.b.cache_entry.disk_idx == offset
  }

  predicate WriteGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)
  {
    && iocb.IocbWrite?
    && g.slot_idx < NUM_IO_SLOTS as int
    && |cache_io_slots| == NUM_IO_SLOTS as int
    && iocb.ptr == iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && g.iovec.ptr == cache_io_slots[g.slot_idx].iovec_ptr
    && |g.iovec.s| == PAGES_PER_EXTENT as int
    && is_read_perm(iocb_ptr, iocb, data, g)
    && simpleWriteGInv(cache_io_slots, cache_data, cache_disk_idx_of_entry, cache_status,
        iocb.offset, data, g.key, g.wbo)
    && iocb.buf == cache_data[g.key.cache_idx]
  }

  predicate WritevGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      iocb_ptr: Ptr,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      datas: seq<seq<byte>>,
      g: WritevG)
  {
    && iocb.IocbWritev?
    && iocb.ptr == iocb_ptr
    && g.slot_idx < NUM_IO_SLOTS as int
    && |cache_io_slots| == NUM_IO_SLOTS as int
    && iovec.ptr == iocb.iovec == cache_io_slots[g.slot_idx].iovec_ptr
    && iocb.ptr == iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && is_read_perm_v(iocb_ptr, iocb, iovec, datas, g)
    && |iovec.s| >= |datas| == iocb.iovec_len == |g.keys|
    && |iovec.s| == PAGES_PER_EXTENT as int
    && (forall i | 0 <= i < |datas| :: i in g.wbos && 
        simpleWriteGInv(cache_io_slots, cache_data, cache_disk_idx_of_entry, cache_status,
            iocb.offset + i, datas[i], g.keys[i], g.wbos[i])
    && (forall i | 0 <= i < |datas| ::
        && 0 <= g.keys[i].cache_idx < |cache_data|
        && iovec.s[i].iov_base() == cache_data[g.keys[i].cache_idx])
    )
  }

  predicate simpleReadGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      offset: nat,
      wp: PointsToArray<byte>,
      key: Key,
      cache_reading: CacheResources.CacheReading,
      idx: CellContents<PageHandle>,
      ro: T.Token)
  {
    && 0 <= key.cache_idx < CACHE_SIZE as int
    && |cache_data| == CACHE_SIZE as int
    && wp.ptr == cache_data[key.cache_idx]
    && |cache_disk_idx_of_entry| == CACHE_SIZE as int
    && |cache_status| == CACHE_SIZE as int
    && idx.cell == cache_disk_idx_of_entry[key.cache_idx]
    && idx.v.disk_addr as int == offset * PageSize
    && idx.v.data_ptr == cache_data[key.cache_idx]
    && offset == cache_reading.disk_idx
    && cache_reading.cache_idx == key.cache_idx
    && ro.loc == cache_status[key.cache_idx].rwlock_loc
    && ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
  }

  predicate ReadvGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<PageHandle>>,
      cache_status: seq<AtomicStatus>,

      iocb_ptr: Ptr,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      wps: map<nat, PointsToArray<byte>>,
      g: ReadvG)
  {
    && iocb.IocbReadv?
    && iocb.ptr == iocb_ptr
    && g.slot_idx < NUM_IO_SLOTS as int
    && |cache_io_slots| == NUM_IO_SLOTS as int
    && iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && 0 <= iocb.offset < NUM_DISK_PAGES as int
    && iovec.ptr == cache_io_slots[g.slot_idx].iovec_ptr
    && |g.keys| <= |iovec.s| == PAGES_PER_EXTENT as int

    && (forall i | 0 <= i < |g.keys| ::
        && i in wps
        && i in g.cache_reading
        && i in g.idx
        && i in g.ro
        && simpleReadGInv(cache_io_slots, cache_data, cache_disk_idx_of_entry, cache_status,
            iocb.offset + i, wps[i], g.keys[i], g.cache_reading[i],
            g.idx[i], g.ro[i])

    && (forall i | 0 <= i < |g.keys| ::
        && 0 <= g.keys[i].cache_idx < |cache_data|
        && iovec.s[i].iov_base() == cache_data[g.keys[i].cache_idx])
        && iovec.s[i].iov_len() as int == PageSize as int
    )
  }
}
