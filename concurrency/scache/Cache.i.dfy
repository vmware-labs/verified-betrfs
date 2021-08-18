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

  datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>,

    global_clockpointer: Atomic<uint32, NullGhostType>,

    io_slots: seq<IOSlot>,
    ioctx: aio.IOCtx
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
    }
  }

  datatype LocalState = LocalState(
    t: int,
    chunk_idx: uint64
  )
  {
    predicate WF()
    {
      && 0 <= this.chunk_idx as int < NUM_CHUNKS
      && 0 <= t < NUM_THREADS
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
      data: seq<byte>,
      g: WriteG)
  {
    && is_read_perm(iocb_ptr, iocb, data, g)
    && g.slot_idx < NUM_IO_SLOTS
    && |cache.io_slots| == NUM_IO_SLOTS
    && g.slot_access.iocb.ptr == cache.io_slots[g.slot_idx].iocb_ptr
    && g.slot_access.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.slot_access.iocb == iocb
    && g.slot_access.io_slot_info.ptr == cache.io_slots[g.slot_idx].io_slot_info_ptr
    && g.slot_access.io_slot_info.v == IOSlotRead(g.wbo.b.key.cache_idx as uint64)
  }

  /*
  predicate WriteTaskInv(task: PendingWriteTask, g: WritebackGhostStateWithSlot, c: Cache)
  requires c.Inv()
  {
    && g.info.v.IOSlotWrite?
    && var cache_idx := g.info.v.cache_idx as int;
    && g.g.WF(c, cache_idx)
    && task.ptr == c.data[cache_idx]
  }

  predicate ReadTaskInv(task: PendingReadTask, g: LoadGhostStateWithSlot, c: Cache)
  requires c.Inv()
  {
    true
  }

  predicate WriteMapInv(
    writeTasks: map<Ptr, PendingWriteTask>,
    writes: map<Ptr, WritebackGhostStateWithSlot>,
    c: Cache)
  requires c.Inv()
  {
    && (forall ptr | ptr in writeTasks :: ptr in writes
        && WriteTaskInv(writeTasks[ptr], writes[ptr], c))
    && (forall ptr | ptr in writes :: ptr in writeTasks)
  }

  predicate ReadMapInv(
    readTasks: map<Ptr, PendingReadTask>,
    read: map<Ptr, LoadGhostStateWithSlot>,
    c: Cache)
  requires c.Inv()
  {
    && (forall ptr | ptr in readTasks :: ptr in read
        && ReadTaskInv(readTasks[ptr], read[ptr], c))
    && (forall ptr | ptr in read :: ptr in readTasks)
  }

  predicate DIInvGhost(v: PendingTaskSet, g: DIGhost, c: Cache)
  requires c.Inv()
  {
    && WriteMapInv(v.writeTasks, map_of(g.write), c)
    && ReadMapInv(v.readTasks, map_of(g.read), c)
  }

  predicate DIInv(di: DiskInterface<DIGhost>, c: Cache)
  requires c.Inv()
  {
    forall v, g ::
      disk_interface_inv(di, v, g) <==> DIInvGhost(v, g, c)
  }

  datatype IOHandle = IOHandle(
    io_slots: seq<IOSlot>,
    disk_interface: DiskInterface<DIGhost>)
  {
    predicate Inv(c: Cache)
    {
      && c.Inv()
      && |this.io_slots| == NUM_IO_SLOTS
      && (forall i | 0 <= i < |this.io_slots| :: this.io_slots[i].WF())
      && DIInv(this.disk_interface, c)
    }
  }
  */
}
