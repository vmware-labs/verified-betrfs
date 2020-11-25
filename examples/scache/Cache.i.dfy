include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"
include "AtomicIndexLookup.i.dfy"
include "ArrayPtr.s.dfy"
include "DiskIO.i.dfy"

module CacheImpl {
  import opened Constants
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened AtomicSpec
  import opened LinearMaybe
  import opened Ptrs
  import opened NativeTypes
  import opened Options
  import DiskIO

  datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>,

    global_clockpointer: Atomic<uint32, NullGhostType>
  )

  predicate Inv(c: Cache)
  {
    && |c.data| == CACHE_SIZE
    && |c.disk_idx_of_entry| == CACHE_SIZE
    && |c.status| == CACHE_SIZE
    && (forall i | 0 <= i < CACHE_SIZE ::
       atomic_status_inv(c.status[i], c.data[i]))
    && |c.read_refcounts| == NUM_THREADS
    && (forall j | 0 <= j < NUM_THREADS ::
        |c.read_refcounts[j]| == CACHE_SIZE)
    && (forall j, i | 0 <= j < NUM_THREADS && 0 <= i < CACHE_SIZE ::
        atomic_refcount_inv(c.read_refcounts[j][i], c.data[i], j))
    && |c.cache_idx_of_page| == NUM_DISK_PAGES
    && (forall d | 0 <= d < NUM_DISK_PAGES ::
        atomic_index_lookup_inv(c.cache_idx_of_page[d], d))
  }

  linear datatype CacheEntryHandle = CacheEntryHandle(
      linear cache_entry: CacheResources.R,
      linear data: ArrayDeref<byte>,
      linear idx: Deref<int>
  )
  {
    predicate is_handle(c: Cache, cache_idx: int)
    requires Inv(c)
    {
      && 0 <= cache_idx < CACHE_SIZE
      && data.ptr == c.data[cache_idx]
      && idx.ptr == c.disk_idx_of_entry[cache_idx]
      && cache_entry == CacheResources.CacheEntry(Some(idx.v), cache_idx, data.s)
      && |data.s| == 4096
    }

    predicate is_page_handle(c: Cache, disk_idx: int)
    requires Inv(c)
    {
      && cache_entry.CacheEntry?
      && is_handle(c, cache_entry.cache_idx)
      && cache_entry.disk_idx_opt == Some(disk_idx)
    }
  }

  linear datatype CacheEntryReadOnlyHandle = CacheEntryReadOnlyHandle(
      linear cache_entry: CacheResources.R, // TODO should be readonly
      linear data: ConstArrayDeref<byte>,
      linear idx: ConstDeref<int>
  )
  {
    predicate is_handle(c: Cache, cache_idx: int)
    requires Inv(c)
    {
      && 0 <= cache_idx < CACHE_SIZE
      && data.ptr == c.data[cache_idx]
      && idx.ptr == c.disk_idx_of_entry[cache_idx]
      && cache_entry == CacheResources.CacheEntry(Some(idx.v), cache_idx, data.s)
      && |data.s| == 4096
    }

    predicate is_page_handle(c: Cache, disk_idx: int)
    requires Inv(c)
    {
      && cache_entry.CacheEntry?
      && is_handle(c, cache_entry.cache_idx)
      && cache_entry.disk_idx_opt == Some(disk_idx)
    }
  }


  method take_write_lock_on_cache_entry(c: Cache, cache_idx: int)
  returns (linear handle: CacheEntryHandle)
  requires Inv(c)
  requires 0 <= cache_idx < CACHE_SIZE
  ensures handle.is_handle(c, cache_idx)
  decreases *
  {
    linear var w_maybe := empty();
    var success := false;

    while !success 
    invariant success ==> w_maybe == give(
        ReadWriteLockResources.WritePendingAwaitBack(c.data[cache_idx]))
    invariant !success ==> !has(w_maybe)
    decreases *
    {
      var _ := discard(w_maybe);
      success, w_maybe := try_set_write_lock(
          c.status[cache_idx], c.data[cache_idx]);
    }

    linear var w;
    w := unwrap(w_maybe);

    success := false;

    while !success 
    invariant !success ==> w ==
        ReadWriteLockResources.WritePendingAwaitBack(c.data[cache_idx])
    invariant success ==> w ==
        ReadWriteLockResources.WritePending(c.data[cache_idx], 0)
    decreases *
    {
      success, w := try_check_writeback_isnt_set(
          c.status[cache_idx], c.data[cache_idx], w);
    }

    var j := 0;
    while j < NUM_THREADS
    invariant 0 <= j <= NUM_THREADS
    invariant w == 
        ReadWriteLockResources.WritePending(c.data[cache_idx], j)
    {
      success := false;

      while !success 
      invariant !success ==> w ==
          ReadWriteLockResources.WritePending(c.data[cache_idx], j)
      invariant success ==> w ==
          ReadWriteLockResources.WritePending(c.data[cache_idx], j+1)
      decreases *
      {
        success, w := is_refcount_zero(c.read_refcounts[j][cache_idx],
            c.data[cache_idx], j, w);
      }

      j := j + 1;
    }

    // TODO
    handle := AtomicRefcountImpl.unsafe_obtain();
    AtomicRefcountImpl.unsafe_dispose(w);
    assume false;
  }

  method release_write_lock_on_cache_entry(c: Cache, cache_idx: int,
      linear handle: CacheEntryHandle)
  requires Inv(c)
  requires 0 <= cache_idx < CACHE_SIZE
  requires handle.is_handle(c, cache_idx)

  /*method take_write_lock_on_disk_entry(c: Cache, disk_idx: int)
  requires 0 
  {
    
  }*/

  method get_next_chunk(c: Cache)
  requires Inv(c)
  {
    var l: uint32 := fetch_add(c.global_clockpointer, 1);
    l := l % (NUM_CHUNKS as uint32);
    var ci: uint32 := (l + CLEAN_AHEAD as uint32) % (NUM_CHUNKS as uint32);

    var i: uint32 := 0;
    while i < CHUNK_SIZE as uint32
    {
      var cache_idx := ci * (CHUNK_SIZE as uint32) + i;   

      linear var write_back_r;
      var do_write_back;
      do_write_back, write_back_r :=
          try_acquire_writeback(c.status[cache_idx], c.data[cache_idx]);

      if do_write_back {
        linear var readonly_handle: CacheEntryReadOnlyHandle :=
            AtomicRefcountImpl.unsafe_obtain(); // TODO
        assume readonly_handle.is_handle(c, cache_idx as int);

        linear var CacheEntryReadOnlyHandle(
            cache_entry, data, idx) := readonly_handle;

        var disk_idx := ptr_const_read(c.disk_idx_of_entry[cache_idx], idx);
        assume 0 <= disk_idx as int < NUM_DISK_PAGES;

        linear var wgs := DiskIO.WritebackGhostState(
            unwrap(write_back_r), cache_entry, idx);

        DiskIO.disk_writeback_async(disk_idx as uint64, c.data[cache_idx],
            data, wgs);
      } else {
        var _ := discard(write_back_r);
      }

      i := i + 1;
    }
  }

  method try_take_write_lock_disk_page(c: Cache, disk_idx: int)
  returns (success: bool, linear handle_out: maybe<CacheEntryHandle>)
  requires Inv(c)
  requires 0 <= disk_idx < NUM_DISK_PAGES
  ensures !success ==> handle_out == empty()
  ensures success ==> has(handle_out) &&
      peek(handle_out).is_page_handle(c, disk_idx)
  decreases *
  {
    var cache_idx := atomic_index_lookup_read(c.cache_idx_of_page[disk_idx], disk_idx);

    if cache_idx == NOT_MAPPED {
      // TODO
      success := false;
      handle_out := empty();
    } else {
      linear var handle := take_write_lock_on_cache_entry(c, cache_idx as int);
      var this_disk_idx := ptr_read(
          c.disk_idx_of_entry[cache_idx],
          handle.idx);
      if this_disk_idx == disk_idx {
        success := true;
        handle_out := give(handle);
      } else {
        release_write_lock_on_cache_entry(c, cache_idx as int, handle);
        success := false;
        handle_out := empty();
      }
    }
  }
}

