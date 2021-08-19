include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"
include "AtomicIndexLookup.i.dfy"
include "../framework/Ptrs.s.dfy"
include "BasicLock.i.dfy"
include "../framework/AIO.s.dfy"
include "cache/CacheSM.i.dfy"
include "CacheAIOParams.i.dfy"

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

  linear datatype NullGhostType = NullGhostType

  linear datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>,

    global_clockpointer: Atomic<uint32, NullGhostType>,

    io_slots: seq<IOSlot>,
    linear ioctx: aio.IOCtx
  )
  {
    function method key(i: int) : Key
    requires 0 <= i < |this.data|
    requires 0 <= i < |this.disk_idx_of_entry|
    {
      Key(this.data[i], this.disk_idx_of_entry[i], i)
    }

    predicate Inv()
    {
      && |this.data| == CACHE_SIZE
      && |this.disk_idx_of_entry| == CACHE_SIZE
      && |this.status| == CACHE_SIZE
      && (forall i | 0 <= i < CACHE_SIZE ::
         && this.status[i].key == this.key(i)
         && this.status[i].inv()
        )
      && |this.read_refcounts| == NUM_THREADS
      && (forall j | 0 <= j < NUM_THREADS ::
          |this.read_refcounts[j]| == CACHE_SIZE)
      && (forall j, i | 0 <= j < NUM_THREADS && 0 <= i < CACHE_SIZE ::
          && this.read_refcounts[j][i].inv(j)
          && this.read_refcounts[j][i].rwlock_loc == this.status[i].rwlock_loc)
      && |this.cache_idx_of_page| == NUM_DISK_PAGES
      && (forall d | 0 <= d < NUM_DISK_PAGES ::
          atomic_index_lookup_inv(this.cache_idx_of_page[d], d))
      && |io_slots| == NUM_IO_SLOTS
      && (forall iocb_ptr, iocb, wp, g :: ioctx.async_read_inv(iocb_ptr, iocb, wp, g)
        <==> ReadGInv(this, iocb_ptr, iocb, wp, g))
      && (forall iocb_ptr, iocb, wp, g :: ioctx.async_write_inv(iocb_ptr, iocb, wp, g)
        <==> WriteGInv(this, iocb_ptr, iocb, wp, g))
    }
  }

  datatype LocalState = LocalState(
    t: uint64,
    chunk_idx: uint64,
    io_slot_hand: uint64
  )
  {
    predicate WF()
    {
      && 0 <= this.chunk_idx as int < NUM_CHUNKS
      && 0 <= t as int < NUM_THREADS
      && 0 <= io_slot_hand as int < NUM_IO_SLOTS
    }
  }

  ////////////////////////////////////////
  //// IO stuff

  datatype IOSlot = IOSlot(
    iocb_ptr: Ptr,
    io_slot_info_ptr: Ptr,
    lock: BasicLock<IOSlotAccess>)
  {
    predicate WF()
    {
      && (forall slot_access: IOSlotAccess :: this.lock.inv(slot_access) <==>
        && slot_access.iocb.ptr == this.iocb_ptr
        && slot_access.io_slot_info.ptr == this.io_slot_info_ptr
      )
    }
  }

  predicate is_slot_access(io_slot: IOSlot, io_slot_access: IOSlotAccess)
  {
    && io_slot.iocb_ptr == io_slot_access.iocb.ptr
    && io_slot.io_slot_info_ptr == io_slot_access.io_slot_info.ptr
  }

  predicate ReadGInv(
      cache: Cache,
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: PointsToArray<byte>,
      g: ReadG)
  {
    && g.slot_idx < NUM_IO_SLOTS
    && |cache.io_slots| == NUM_IO_SLOTS
    && g.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.reading.CacheReadingHandle?
    && g.key.cache_idx < 0x1_0000_0000_0000_0000
    && g.io_slot_info.v == IOSlotRead(g.key.cache_idx as uint64)
  }

  predicate WriteGInv(
      cache: Cache,
      iocb_ptr: Ptr,
      iocb: Iocb,
      data: seq<byte>,
      g: WriteG)
  {
    && is_read_perm(iocb_ptr, iocb, data, g)
    && g.slot_idx < NUM_IO_SLOTS
    && |cache.io_slots| == NUM_IO_SLOTS
    && g.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.wbo.b.CacheEntryHandle?
    && g.wbo.b.key.cache_idx < 0x1_0000_0000_0000_0000
    && g.io_slot_info.v == IOSlotWrite(g.wbo.b.key.cache_idx as uint64)
  }
}
