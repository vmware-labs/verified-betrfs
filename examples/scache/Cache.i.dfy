include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"
include "AtomicIndexLookup.i.dfy"
include "ArrayPtr.s.dfy"
include "DiskInterface.s.dfy"
include "BasicLock.i.dfy"
include "LinearMap.s.dfy"

module CacheImpl {
  import opened Ptrs
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened AtomicStatusImpl
  import opened AtomicSpec
  import opened Constants
  import opened NativeTypes
  import opened DiskInterfaceSpec
  import opened BasicLockImpl
  import opened LinearMaps

  linear datatype NullGhostType = NullGhostType

  datatype IOSlotInfo =
    | IOSlotUnused
    | IOSlotWrite(cache_idx: uint64)
    | IOSlotRead(cache_idx: uint64)

  linear datatype IOSlotAccess = IOSlotAccess(
    linear aiocb: Deref<Aiocb>,
    linear info: Deref<IOSlotInfo>)

  datatype IOSlot = IOSlot(
    aiocb_ptr: Ptr,
    info_ptr: Ptr,
    lock: BasicLock<IOSlotAccess>)
  {
    predicate WF()
    {
      && this.lock.inv((slot_access: IOSlotAccess) =>
        && slot_access.aiocb.ptr == this.aiocb_ptr
        && slot_access.info.ptr == this.info_ptr
      )
    }
  }

  predicate is_slot_access(io_slot: IOSlot, io_slot_access: IOSlotAccess)
  {
    && io_slot.aiocb_ptr == io_slot_access.aiocb.ptr
    && io_slot.info_ptr == io_slot_access.info.ptr
  }

  linear datatype WritebackGhostState = WritebackGhostState(
      linear q: RWLock.R,
      /*readonly*/ linear cache_entry: CacheResources.R,
      /*readonly*/ linear idx: Deref<int>)
  /*{
    predicate WF(addr: uint64)
    {
    }
  }*/

  linear datatype LoadGhostState = LoadGhostState

  linear datatype WritebackGhostStateWithSlot = WritebackGhostStateWithSlot(
        linear info: Deref<IOSlotInfo>,
        linear g: WritebackGhostState)

  linear datatype LoadGhostStateWithSlot = LoadGhostStateWithSlot(
        linear info: Deref<IOSlotInfo>,
        linear g: LoadGhostState)

  linear datatype DIGhost = DIGhost(
    linear write: LinearMap<Ptr, WritebackGhostStateWithSlot>,
    linear read: LinearMap<Ptr, LoadGhostStateWithSlot>
  )

  predicate WriteMapInv(
    writeTasks: map<Ptr, PendingWriteTask>,
    writes: map<Ptr, WritebackGhostStateWithSlot>)
  {
    && (forall ptr | ptr in writeTasks :: ptr in writes)
    && (forall ptr | ptr in writes :: ptr in writeTasks)
  }

  predicate ReadMapInv(
    readTasks: map<Ptr, PendingReadTask>,
    read: map<Ptr, LoadGhostStateWithSlot>)
  {
    && (forall ptr | ptr in readTasks :: ptr in read)
    && (forall ptr | ptr in read :: ptr in readTasks)
  }

  predicate DIInvGhost(v: PendingTaskSet, g: DIGhost)
  {
    && WriteMapInv(v.writeTasks, map_of(g.write))
    && ReadMapInv(v.readTasks, map_of(g.read))
  }

  predicate DIInv(di: DiskInterface<DIGhost>)
  {
    forall v, g ::
      disk_interface_inv(di, v, g) <==> DIInvGhost(v, g)
  }

  datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>,

    global_clockpointer: Atomic<uint32, NullGhostType>,

    io_slots: seq<IOSlot>,
    disk_interface: DiskInterface<DIGhost>
  )
  {
    function method key(i: int) : RWLock.Key
    requires 0 <= i < |this.data|
    requires 0 <= i < |this.disk_idx_of_entry|
    {
      RWLock.Key(this.data[i], this.disk_idx_of_entry[i], i)
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

  predicate Inv(c: Cache)
  {
    && |c.data| == CACHE_SIZE
    && |c.disk_idx_of_entry| == CACHE_SIZE
    && |c.status| == CACHE_SIZE
    && (forall i | 0 <= i < CACHE_SIZE ::
       atomic_status_inv(c.status[i], c.key(i)))
    && |c.read_refcounts| == NUM_THREADS
    && (forall j | 0 <= j < NUM_THREADS ::
        |c.read_refcounts[j]| == CACHE_SIZE)
    && (forall j, i | 0 <= j < NUM_THREADS && 0 <= i < CACHE_SIZE ::
        atomic_refcount_inv(c.read_refcounts[j][i], c.key(i), j))
    && |c.cache_idx_of_page| == NUM_DISK_PAGES
    && (forall d | 0 <= d < NUM_DISK_PAGES ::
        atomic_index_lookup_inv(c.cache_idx_of_page[d], d))
    && |c.io_slots| == NUM_IO_SLOTS
    && (forall i | 0 <= i < |c.io_slots| :: c.io_slots[i].WF())
    && DIInv(c.disk_interface)
  }
}
