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
  import CacheResources

  datatype Cache = Cache(
    data: seq<Ptr>,
    disk_idx_of_entry: seq<Ptr>,

    status: seq<AtomicStatus>,
    read_refcounts: seq<seq<AtomicRefcount>>,

    cache_idx_of_page: seq<AtomicIndexLookup>,

    global_clockpointer: Atomic<uint32, NullGhostType>
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
    cur_chunk: uint64
  )
  {
    predicate WF()
    {
      && 0 <= this.cur_chunk as int < NUM_CHUNKS
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
  }

  predicate is_disk_page_handle(handle: RWLock.Handle, c: Cache, disk_idx: int)
  requires Inv(c)
  {
    && handle.cache_entry.CacheEntry?
    && handle.cache_entry.disk_idx == disk_idx
    && 0 <= handle.cache_entry.cache_idx < CACHE_SIZE
    && handle.is_handle(c.key(handle.cache_entry.cache_idx))
  }

  linear datatype PageHandle = PageHandle(
      linear w: RWLock.R,
      linear handle: RWLock.Handle)
  {
    predicate is_page_handle(c: Cache, disk_idx: int)
    requires Inv(c)
    {
      && is_disk_page_handle(this.handle, c, disk_idx)
      && w == RWLock.Internal(RWLock.ExcLockObtained(
          c.key(this.handle.cache_entry.cache_idx)))
    }
  }

  linear datatype ReadonlyPageHandle = ReadonlyPageHandle(
      linear w: RWLock.R,
      /*readonly*/ linear handle: RWLock.Handle)
  {
    predicate is_page_handle(c: Cache, disk_idx: int, t: int)
    requires Inv(c)
    {
      && is_disk_page_handle(this.handle, c, disk_idx)
      && w == RWLock.Internal(RWLock.SharedLockObtained(
          c.key(this.handle.cache_entry.cache_idx), t))
    }
  }

  /*method take_write_lock_on_cache_entry(c: Cache, cache_idx: int)
  returns (linear r: RWLock.R, linear handle: RWLock.Handle)
  requires Inv(c)
  requires 0 <= cache_idx < CACHE_SIZE
  ensures r == RWLock.Internal(RWLock.ExcLockObtained(c.key(cache_idx)))
  ensures handle.is_handle(c.key(cache_idx))
  decreases *
  {
    linear var w_maybe := empty();
    var success := false;

    while !success 
    invariant success ==> w_maybe == give(
        RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(c.key(cache_idx))))
    invariant !success ==> !has(w_maybe)
    decreases *
    {
      var _ := discard(w_maybe);
      success, w_maybe := try_set_write_lock(
          c.status[cache_idx], c.key(cache_idx));
    }

    linear var w;
    w := unwrap(w_maybe);

    success := false;

    while !success 
    invariant !success ==> w ==
        RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(c.key(cache_idx)))
    invariant success ==> w ==
        RWLock.Internal(RWLock.ExcLockPending(c.key(cache_idx), 0))
    decreases *
    {
      success, w := try_check_writeback_isnt_set(
          c.status[cache_idx], c.key(cache_idx), w);
    }

    var j := 0;
    while j < NUM_THREADS
    invariant 0 <= j <= NUM_THREADS
    invariant w == 
        RWLock.Internal(RWLock.ExcLockPending(c.key(cache_idx), j))
    {
      success := false;

      while !success 
      invariant !success ==> w ==
          RWLock.Internal(RWLock.ExcLockPending(c.key(cache_idx), j))
      invariant success ==> w ==
          RWLock.Internal(RWLock.ExcLockPending(c.key(cache_idx), j+1))
      decreases *
      {
        success, w := is_refcount_zero(c.read_refcounts[j][cache_idx],
            c.key(cache_idx), j, w);
      }

      j := j + 1;
    }

    r, handle := RWLock.transform_TakeWriteFinish(c.key(cache_idx), w);
  }*/

  method release_write_lock_on_cache_entry(c: Cache, cache_idx: int,
      linear r: RWLock.R,
      linear handle: RWLock.Handle)
  requires Inv(c)
  requires 0 <= cache_idx < CACHE_SIZE
  requires handle.is_handle(c.key(cache_idx))
  requires r == RWLock.Internal(RWLock.ExcLockObtained(c.key(cache_idx)))

  /*method take_write_lock_on_disk_entry(c: Cache, disk_idx: int)
  requires 0 
  {
    
  }*/

  method get_next_chunk(c: Cache)
  returns (new_chunk: uint64)
  requires Inv(c)
  ensures 0 <= new_chunk as int < NUM_CHUNKS
  {
    var l: uint32 := fetch_add_uint32(c.global_clockpointer, 1);
    l := l % (NUM_CHUNKS as uint32);
    var ci: uint32 := (l + CLEAN_AHEAD as uint32) % (NUM_CHUNKS as uint32);

    var i: uint32 := 0;
    while i < CHUNK_SIZE as uint32
    {
      var cache_idx := ci * (CHUNK_SIZE as uint32) + i;   

      linear var write_back_r, ticket;
      /*readonly*/ linear var readonly_handle_maybe: maybe<RWLock.Handle>;
      var do_write_back;
      do_write_back, write_back_r, readonly_handle_maybe, ticket :=
          try_acquire_writeback(
              c.status[cache_idx],
              c.key(cache_idx as int),
              false);

      if do_write_back {
        linear var readonly_handle: RWLock.Handle := unwrap(readonly_handle_maybe);
        /*readonly*/ linear var CacheEntryHandle(
            cache_entry, data, idx) := readonly_handle;

        var disk_idx := ptr_read(c.disk_idx_of_entry[cache_idx], idx);
        assert disk_idx != -1;

        linear var wgs := DiskIO.WritebackGhostState(
            unwrap(write_back_r), cache_entry, idx);

        DiskIO.disk_writeback_async(
            disk_idx as uint64,
            c.data[cache_idx],
            data, wgs, unwrap(ticket));

        /*} else {
          readonly_handle := RWLock.CacheEntryHandle(cache_entry, data, idx);
          release_writeback(c.status[cache_idx], c.key(cache_idx as int),
              unwrap(write_back_r), readonly_handle);
        }*/
      } else {
        var _ := discard(readonly_handle_maybe);
        var _ := discard(write_back_r);
        var _ := discard(ticket);
      }

      i := i + 1;
    }

    new_chunk := l as uint64;
  }

  method get_free_page(c: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint64,
    linear m: maybe<RWLock.R>,
    linear handle_maybe: maybe<RWLock.Handle>,
    linear status_maybe: maybe<CacheResources.R>
  )
  requires Inv(c)
  requires old_localState.WF()
  ensures localState.WF()
  ensures cache_idx == 0xffff_ffff ==> !has(m)
  ensures cache_idx == 0xffff_ffff ==> !has(handle_maybe)
  ensures cache_idx == 0xffff_ffff ==> !has(status_maybe)
  ensures cache_idx != 0xffff_ffff ==> 0 <= cache_idx as int < CACHE_SIZE
  ensures cache_idx != 0xffff_ffff ==> has(m)
      && read(m) == RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int)))
  ensures cache_idx != 0xffff_ffff ==> has(handle_maybe)
      && read(handle_maybe).is_handle(c.key(cache_idx as int))
      && read(handle_maybe).idx.v == -1
  ensures cache_idx != 0xffff_ffff ==> has(status_maybe)
      && read(status_maybe) == CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty)
  decreases *
  {
    var chunk: uint64 := localState.cur_chunk;

    var success := false;
    m := empty();
    handle_maybe := empty();
    status_maybe := empty();

    while !success
    decreases *
    invariant localState.WF()
    invariant !success ==> !has(m)
    invariant !success ==> !has(handle_maybe)
    invariant !success ==> !has(status_maybe)
    invariant success ==> 0 <= cache_idx as int < CACHE_SIZE
    invariant success ==> has(m)
        && read(m) == RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int)))
    invariant success ==> has(handle_maybe)
        && read(handle_maybe).is_handle(c.key(cache_idx as int))
        && read(handle_maybe).idx.v == -1
    invariant success ==> has(status_maybe)
        && read(status_maybe) == CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty)
    {
      var i: uint64 := 0; 
      while i < CHUNK_SIZE as uint64 && !success
      invariant 0 <= i as int <= CHUNK_SIZE
      invariant !success ==> !has(m)
      invariant !success ==> !has(handle_maybe)
      invariant !success ==> !has(status_maybe)
      invariant success ==> 0 <= cache_idx as int < CACHE_SIZE
      invariant success ==> has(m)
          && read(m) == RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int)))
      invariant success ==> has(handle_maybe)
          && read(handle_maybe).is_handle(c.key(cache_idx as int))
          && read(handle_maybe).idx.v == -1
      invariant success ==> has(status_maybe)
          && read(status_maybe) == CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty)
      {
        cache_idx := chunk * CHUNK_SIZE as uint64 + i;

        var _ := discard(m);
        var _ := discard(handle_maybe);
        var _ := discard(status_maybe);
        success, m, handle_maybe, status_maybe := try_alloc(
            c.status[cache_idx],
            c.key(cache_idx as int));

        i := i + 1;
      }

      if !success {
        var new_chunk := get_next_chunk(c);
        inout localState.cur_chunk := new_chunk;
      }
    }
  }

  method try_take_read_lock_disk_page(c: Cache, disk_idx: int,
      linear inout localState: LocalState)
  returns (success: bool, linear handle_out: maybe<ReadonlyPageHandle>)
  requires Inv(c)
  requires 0 <= disk_idx < NUM_DISK_PAGES
  requires old_localState.WF()
  ensures !success ==> handle_out == empty()
  ensures success ==> has(handle_out) &&
      peek(handle_out).is_page_handle(c, disk_idx, localState.t)
  ensures old_localState.WF()
  decreases *
  {
    var cache_idx := atomic_index_lookup_read(c.cache_idx_of_page[disk_idx], disk_idx);

    if cache_idx == NOT_MAPPED {
      linear var m, handle_maybe, status_maybe;
      cache_idx, m, handle_maybe, status_maybe := get_free_page(c, inout localState);

      if cache_idx == 0xffff_ffff {
        var _ := discard(m);
        var _ := discard(handle_maybe);
        var _ := discard(status_maybe);
        success := false;
        handle_out := empty();
      } else {
        linear var r := unwrap(m);
        linear var handle: RWLock.Handle := unwrap(handle_maybe);
        linear var status := unwrap(status_maybe);
        linear var read_stub;
        linear var read_ticket_maybe;

        linear var CacheEntryHandle(cache_entry, data, idx) := handle;

        success, cache_entry, status, read_ticket_maybe := 
            atomic_index_lookup_add_mapping(
              c.cache_idx_of_page[disk_idx],
              disk_idx as uint64,
              cache_idx as uint64,
              cache_entry,
              status);

        if !success {
          success := false;
          handle_out := empty();
          var _ := discard(read_ticket_maybe);
          AtomicStatusImpl.unsafe_dispose(r);
          AtomicStatusImpl.unsafe_dispose(status);
          AtomicStatusImpl.unsafe_dispose(cache_entry);
          AtomicStatusImpl.unsafe_dispose(data);
          AtomicStatusImpl.unsafe_dispose(idx);
        } else {
          r := inc_refcount_for_reading(
              c.read_refcounts[localState.t][cache_idx],
              c.key(cache_idx as int), localState.t, r);

          r := clear_exc_bit_during_load_phase(
              c.status[cache_idx],
              c.key(cache_idx as int), localState.t, r);

          read_stub := DiskIO.disk_read_sync(
              disk_idx as uint64, c.data[cache_idx], inout data, 
              unwrap(read_ticket_maybe));

          status, cache_entry := CacheResources.finish_page_in(
              cache_idx as int, disk_idx as uint64,
              status, cache_entry, read_stub);

          ptr_write(c.disk_idx_of_entry[cache_idx],
              inout idx, disk_idx);

          /*readonly*/ linear var readonly_handle;
          r, readonly_handle := load_phase_finish(
              c.status[cache_idx],
              c.key(cache_idx as int), localState.t, r,
              RWLock.CacheEntryHandle(cache_entry, data, idx),
              status);

          success := true;
          handle_out := give(ReadonlyPageHandle(r, readonly_handle));
        }
      }
    } else {
      // TODO
      success := false;
      handle_out := empty();

      /*linear var r, handle := take_write_lock_on_cache_entry(c, cache_idx as int);
      var this_disk_idx := ptr_read(
          c.disk_idx_of_entry[cache_idx],
          handle.idx);
      if this_disk_idx == disk_idx {
        success := true;
        handle_out := give(PageHandle(r, handle));
      } else {
        release_write_lock_on_cache_entry(c, cache_idx as int, r, handle);
        success := false;
        handle_out := empty();
      }*/
    }
  }
}
