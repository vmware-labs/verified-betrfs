include "AtomicRefcount.i.dfy"
include "AtomicStatus.i.dfy"
include "AtomicIndexLookup.i.dfy"
include "ArrayPtr.s.dfy"

module CacheImpl {
  import opened Constants
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened LinearMaybe
  import opened Ptrs
  import opened NativeTypes
  import opened Options

  datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>
  )

  predicate Inv(c: Cache)
  {
    && |c.data| == CacheSize()
    && |c.disk_idx_of_entry| == CacheSize()
    && |c.status| == CacheSize()
    && (forall i | 0 <= i < CacheSize() ::
       atomic_status_inv(c.status[i], c.data[i]))
    && |c.read_refcounts| == NThreads()
    && (forall j | 0 <= j < NThreads() ::
        |c.read_refcounts[j]| == CacheSize())
    && (forall j, i | 0 <= j < NThreads() && 0 <= i < CacheSize() ::
        atomic_refcount_inv(c.read_refcounts[j][i], c.data[i], j))
    && |c.cache_idx_of_page| == NDiskPages()
    && (forall d | 0 <= d < NDiskPages() ::
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
      && 0 <= cache_idx < CacheSize()
      && data.ptr == c.data[cache_idx]
      && idx.ptr == c.disk_idx_of_entry[cache_idx]
      && cache_entry == CacheResources.CacheEntry(Some(idx.v), cache_idx, data.s)
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
  requires 0 <= cache_idx < CacheSize()
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
    while j < NThreads()
    invariant 0 <= j <= NThreads()
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
  requires 0 <= cache_idx < CacheSize()
  requires handle.is_handle(c, cache_idx)

  /*method take_write_lock_on_disk_entry(c: Cache, disk_idx: int)
  requires 0 
  {
    
  }*/

  method try_take_write_lock_disk_page(c: Cache, disk_idx: int)
  returns (success: bool, linear handle_out: maybe<CacheEntryHandle>)
  requires Inv(c)
  requires 0 <= disk_idx < NDiskPages()
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
