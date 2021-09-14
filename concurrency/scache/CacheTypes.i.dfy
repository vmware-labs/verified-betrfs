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
  import opened GlinearSeq
  import opened LinearSequence_i
  import opened LinearSequence_s
  import RwLockToken
  import opened Cells
  import opened PageSizeConstant

  glinear datatype NullGhostType = NullGhostType

  linear datatype StatusIdx = StatusIdx(
    linear status: AtomicStatus,
    linear idx: Cell<int64>
  )

  linear datatype Cache = Cache(
    data_base_ptr: Ptr,
    iocb_base_ptr: Ptr,
    linear read_refcounts_array: lseq<AtomicRefcount>,
    linear cache_idx_of_page_array: lseq<AtomicIndexLookup>,
    linear status_idx_array: lseq<StatusIdx>,

    ghost data: seq<Ptr>,
    ghost disk_idx_of_entry: seq<Cell<int64>>,
    ghost status: seq<AtomicStatus>,

    ghost read_refcounts: seq<seq<AtomicRefcount>>,

    ghost cache_idx_of_page: seq<AtomicIndexLookup>,

    linear global_clockpointer: Atomic<uint32, NullGhostType>,
    linear batch_busy: lseq<Atomic<bool, NullGhostType>>,

    linear io_slots: lseq<IOSlot>,
    linear ioctx: aio.IOCtx
  )
  {
    function key(i: int) : Key
    requires 0 <= i < |this.data|
    requires 0 <= i < |this.disk_idx_of_entry|
    {
      Key(this.data[i], this.disk_idx_of_entry[i], i)
    }

    predicate Inv()
    {
      && |this.data| == CACHE_SIZE as int
      && |this.disk_idx_of_entry| == CACHE_SIZE as int
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
        <==> ReadGInv(io_slots, data, disk_idx_of_entry, status,
                  iocb_ptr, iocb, wp, g))

      && (forall iocb_ptr, iocb, wp, g :: ioctx.async_write_inv(iocb_ptr, iocb, wp, g)
        <==> WriteGInv(io_slots, data, disk_idx_of_entry, status,
                  iocb_ptr, iocb, wp, g))

      && (forall v, g :: atomic_inv(global_clockpointer, v, g) <==> true)

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
            == StatusIdx(this.status[i], this.disk_idx_of_entry[i])
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
      ptr_add(this.data_base_ptr, PageSize * i)
    }

    shared function method status_atomic(i: uint64) : (shared at: AtomicStatus)
    requires this.Inv()
    requires 0 <= i as int < CACHE_SIZE as int
    ensures at == this.status[i]
    {
      lseq_peek(this.status_idx_array, i as uint64).status
    }

    shared function method disk_idx_of_entry_ptr(i: uint64) : (shared c: Cell<int64>)
    requires this.Inv()
    requires 0 <= i as int < CACHE_SIZE as int
    ensures c == this.disk_idx_of_entry[i]
    {
      lseq_peek(this.status_idx_array, i as uint64).idx
    }

    shared function method read_refcount_atomic(j: uint64, i: uint64) : (shared at: AtomicRefcount)
    requires this.Inv()
    requires 0 <= j as int < RC_WIDTH as int
    requires 0 <= i as int < CACHE_SIZE as int
    ensures at == this.read_refcounts[j][i]
    {
      lseq_peek(this.read_refcounts_array, j * CACHE_SIZE + i)
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
      && 0 <= io_slot_hand as int < NUM_IO_SLOTS as int
    }
  }

  ////////////////////////////////////////
  //// IO stuff

  linear datatype IOSlot = IOSlot(
    iocb_ptr: Ptr,
    linear io_slot_info_cell: Cell<IOSlotInfo>,
    linear lock: pre_BasicLock<IOSlotAccess>)
  {
    predicate WF()
    {
      && lock.wf()
      && (forall slot_access: IOSlotAccess :: this.lock.inv(slot_access) <==>
        && slot_access.iocb.ptr == this.iocb_ptr
        && slot_access.io_slot_info.cell == this.io_slot_info_cell
      )
    }
  }

  predicate is_slot_access(io_slot: IOSlot, io_slot_access: IOSlotAccess)
  {
    && io_slot.iocb_ptr == io_slot_access.iocb.ptr
    && io_slot.io_slot_info_cell == io_slot_access.io_slot_info.cell
  }

  predicate ReadGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<int64>>,
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
    && g.io_slot_info.cell == cache_io_slots[g.slot_idx].io_slot_info_cell
    && iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && 0 <= g.key.cache_idx < CACHE_SIZE as int
    && 0 <= iocb.offset < NUM_DISK_PAGES as int
    && |cache_data| == CACHE_SIZE as int
    && |cache_disk_idx_of_entry| == CACHE_SIZE as int
    && |cache_status| == CACHE_SIZE as int
    && data.ptr == cache_data[g.key.cache_idx]
    && g.io_slot_info.v == IOSlotRead(g.key.cache_idx as uint64)
    && iocb.nbytes == PageSize as int
    && g.idx.cell == cache_disk_idx_of_entry[g.key.cache_idx]
    && g.idx.v as int == iocb.offset == g.cache_reading.disk_idx
    && g.cache_reading.cache_idx == g.key.cache_idx
    && g.ro.loc == cache_status[g.key.cache_idx].rwlock_loc
    && g.ro.val == RwLock.ReadHandle(RwLock.ReadObtained(-1))
  }

  predicate WriteGInv(
      cache_io_slots: lseq<IOSlot>,
      cache_data: seq<Ptr>,
      cache_disk_idx_of_entry: seq<Cell<int64>>,
      cache_status: seq<AtomicStatus>,

      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)
  {
    && iocb.IocbWrite?
    && iocb.ptr == iocb_ptr
    && is_read_perm(iocb_ptr, iocb, data, g)
    && g.slot_idx < NUM_IO_SLOTS as int
    && |cache_io_slots| == NUM_IO_SLOTS as int
    && g.io_slot_info.cell == cache_io_slots[g.slot_idx].io_slot_info_cell
    && iocb_ptr == cache_io_slots[g.slot_idx].iocb_ptr
    && g.wbo.b.CacheEntryHandle?
    && 0 <= g.wbo.b.key.cache_idx < CACHE_SIZE as int
    && g.io_slot_info.v == IOSlotWrite(g.wbo.b.key.cache_idx as uint64)
    && g.wbo.is_handle(g.key)
    && |cache_data| == CACHE_SIZE as int
    && |cache_disk_idx_of_entry| == CACHE_SIZE as int
    && |cache_status| == CACHE_SIZE as int
    && g.key.data_ptr == cache_data[g.key.cache_idx]
    && g.key.idx_cell == cache_disk_idx_of_entry[g.key.cache_idx]
    && g.wbo.token.loc == cache_status[g.wbo.b.key.cache_idx as nat].rwlock_loc
    && g.wbo.b.cache_entry.disk_idx == iocb.offset
  }
}
