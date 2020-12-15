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
  import opened LinearOption
  import opened Ptrs
  import opened NativeTypes
  import opened Options
  import DiskIO
  import CacheResources
  import RWLockMethods

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
  }

  predicate is_disk_page_handle(handle: RWLock.Handle, c: Cache, disk_idx: int)
  requires Inv(c)
  {
    && handle.cache_entry.CacheEntry?
    && handle.cache_entry.disk_idx == disk_idx
    && 0 <= handle.cache_entry.cache_idx < CACHE_SIZE
    && handle.is_handle(c.key(handle.cache_entry.cache_idx))
  }

  /*linear datatype PageHandle = PageHandle(
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
  }*/

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

  method try_take_read_lock_on_cache_entry(
      c: Cache, cache_idx: int,
      expected_disk_idx: int,
      shared localState: LocalState,
      linear client: RWLock.R)
  returns (
    success: bool,
    linear handle_out: lOption<ReadonlyPageHandle>,
    linear client_out: lOption<RWLock.R>
  )
  requires Inv(c)
  requires localState.WF()
  requires 0 <= cache_idx < CACHE_SIZE
  requires client == RWLock.Internal(RWLock.Client(localState.t))
  ensures !success ==> handle_out.lNone?
      && client_out == lSome(client)
  ensures success ==>
      && handle_out.lSome?
      && handle_out.value.is_page_handle(
          c, expected_disk_idx, localState.t)
      && client_out.lNone?
  decreases *
  {
    // 1. check if writelocked

    var is_exc_locked := quicktest_is_exc_locked(c.status[cache_idx]);
    if is_exc_locked {
      success := false;
      handle_out := lNone;
      client_out := lSome(client);
    } else {
      // 2. inc ref

      linear var r := inc_refcount_for_shared(
          c.read_refcounts[localState.t][cache_idx],
          c.key(cache_idx), localState.t,
          client);

      // 3. check not writelocked, not free
      //        otherwise, dec and abort

      var is_accessed: bool;
      success, is_accessed, r := is_exc_locked_or_free(
          c.status[cache_idx],
          c.key(cache_idx), localState.t,
          r);

      if !success {
        linear var client' := dec_refcount_for_shared_pending(
            c.read_refcounts[localState.t][cache_idx],
            c.key(cache_idx), localState.t,
            r);

        handle_out := lNone;
        client_out := lSome(client');
      } else {
        // 4. if !access, then mark accessed
        if !is_accessed {
          mark_accessed(c.status[cache_idx],
            c.key(cache_idx), localState.t, r);
        }

        // This is the ideal order:
        //
        // 5. check the disk_idx is correct
        //        otherwise, dec and abort
        // 6. if LOADING, then block until it's done
        //
        // but it's also a little annoying to set that up
        // (as it is, we currently don't have access to the disk_idx
        // field) so we do it in reverse. It ought to be an uncommon
        // race case, anyway.

        // Wait for loading to be done:

        linear var handle_opt: lOption<RWLock.Handle> := lNone;
        var is_done_reading := false;
        while !is_done_reading
        invariant !is_done_reading ==>
          && handle_opt.lNone?
          && r == RWLock.Internal(RWLock.SharedLockPending2(
              c.key(cache_idx), localState.t))
        invariant is_done_reading ==>
          && handle_opt.lSome?
          && handle_opt.value.is_handle(c.key(cache_idx))
          && r == RWLock.Internal(RWLock.SharedLockObtained(
              c.key(cache_idx), localState.t))
        decreases *
        {
          dispose_lnone(handle_opt);
          is_done_reading, r, handle_opt := is_reading(
              c.status[cache_idx],
              c.key(cache_idx),
              localState.t,
              r);

          // TODO
          // if !is_done_reading, then spend the time to handle
          // some IO responses
        }

        // Check the disk_idx

        var actual_disk_idx := ptr_read(
            c.disk_idx_of_entry[cache_idx],
            handle_opt.value.idx);

        if actual_disk_idx != expected_disk_idx {
          linear var client' := dec_refcount_for_shared_obtained(
              c.read_refcounts[localState.t][cache_idx],
              c.key(cache_idx), localState.t,
              r, unwrap_value(handle_opt));

          success := false;
          handle_out := lNone;
          client_out := lSome(client');
        } else {
          success := true;
          handle_out := lSome(
              ReadonlyPageHandle(r, unwrap_value(handle_opt)));
          client_out := lNone;
        }
      }
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
    linear var w_opt := lNone;
    var success := false;

    while !success 
    invariant success ==> w_opt == lSome(
        RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(c.key(cache_idx))))
    invariant !success ==> !has(w_opt)
    decreases *
    {
      dispose_lnone(w_opt);
      success, w_opt := try_set_write_lock(
          c.status[cache_idx], c.key(cache_idx));
    }

    linear var w;
    w := unwrap_value(w_opt);

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

  /*method release_write_lock_on_cache_entry(c: Cache, cache_idx: int,
      linear r: RWLock.R,
      linear handle: RWLock.Handle)
  requires Inv(c)
  requires 0 <= cache_idx < CACHE_SIZE
  requires handle.is_handle(c.key(cache_idx))
  requires r == RWLock.Internal(RWLock.ExcLockObtained(c.key(cache_idx)))*/

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
      /*readonly*/ linear var readonly_handle_opt: lOption<RWLock.Handle>;
      var do_write_back;
      do_write_back, write_back_r, readonly_handle_opt, ticket :=
          try_acquire_writeback(
              c.status[cache_idx],
              c.key(cache_idx as int),
              false);

      if do_write_back {
        linear var readonly_handle: RWLock.Handle := unwrap_value(readonly_handle_opt);
        /*readonly*/ linear var CacheEntryHandle(
            _, cache_entry, data, idx) := readonly_handle;

        var disk_idx := ptr_read(c.disk_idx_of_entry[cache_idx], idx);
        assert disk_idx != -1;

        linear var wgs := DiskIO.WritebackGhostState(
            unwrap_value(write_back_r), cache_entry, idx);

        DiskIO.disk_writeback_async(
            disk_idx as uint64,
            c.data[cache_idx],
            data, wgs, unwrap_value(ticket));

        /*} else {
          readonly_handle := RWLock.CacheEntryHandle(cache_entry, data, idx);
          release_writeback(c.status[cache_idx], c.key(cache_idx as int),
              unwrap_value(write_back_r), readonly_handle);
        }*/
      } else {
        dispose_lnone(readonly_handle_opt);
        dispose_lnone(write_back_r);
        dispose_lnone(ticket);
      }

      i := i + 1;
    }

    new_chunk := l as uint64;
  }

  method check_all_refcounts_dont_wait(c: Cache,
      cache_idx: uint64,
      linear r: RWLock.R)
  returns (success: bool, linear r': RWLock.R)
  requires Inv(c)
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires r.Internal? && r.q.ExcLockPending?
  requires r == RWLock.Internal(RWLock.ExcLockPending(
      c.key(cache_idx as int), -1, 0, r.q.clean))
  ensures r'.Internal?
  ensures r'.q.ExcLockPending?
  ensures r'.q.key == c.key(cache_idx as int)
  ensures r'.q.t == -1
  ensures r'.q.clean == r.q.clean
  ensures success ==> r'.q.visited == NUM_THREADS

  method try_evict_page(c: Cache, cache_idx: uint64)
  requires Inv(c)
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires 0 <= cache_idx as int < CACHE_SIZE
  {
    // 1. get status

    var status := atomic_read(c.status[cache_idx]);

    // 2. if accessed, then clear 'access'

    if bit_or(status, flag_accessed) != 0 {
      clear_accessed(c.status[cache_idx], c.key(cache_idx as int));
    }

    // 3. if status != CLEAN, abort

    if status != flag_clean {
      // no cleanup to do
    } else {
      // 4. inc ref count for shared lock
      // skipping this step, we don't need it
      //
      //linear var r := inc_refcount_for_shared(
      //    c.read_refcounts[localState.t][cache_idx],
      //    c.key(cache_idx), localState.t);

      // 5. get the exc lock (Clean -> Clean | Exc) (or bail)

      var success;
      linear var status, r, r_opt, status_opt, handle_opt;
      success, r_opt, status_opt, handle_opt := take_exc_if_eq_clean(
            c.status[cache_idx], 
            c.key(cache_idx as int));

      if !success {
        dispose_lnone(status_opt);
        dispose_lnone(r_opt);
        dispose_lnone(handle_opt);
      } else {
        // 6. try the rest of the read refcounts (or bail)

        status := unwrap_value(status_opt);
        r := unwrap_value(r_opt);

        success, r := check_all_refcounts_dont_wait(
            c, cache_idx, r);

        if !success {
          abandon_exc(
              c.status[cache_idx],
              c.key(cache_idx as int),
              status, r, unwrap_value(handle_opt));
        } else {
          linear var handle;
          var clean := r.q.clean;
          r, handle := RWLockMethods.transform_TakeExcLockFinish(
              c.key(cache_idx as int), -1, clean, r, unwrap_value(handle_opt));

          // 7. clear cache_idx_of_page lookup

          var disk_idx := ptr_read(
              c.disk_idx_of_entry[cache_idx],
              handle.idx);

          linear var CacheEntryHandle(key, cache_entry, data, idx) := handle;

          cache_entry, status := atomic_index_lookup_clear_mapping(
                c.cache_idx_of_page[disk_idx],
                disk_idx,
                cache_entry,
                status);

          // 8. set to FREE

          set_to_free(
              c.status[cache_idx],
              c.key(cache_idx as int),
              RWLock.CacheEntryHandle(key, cache_entry, data, idx),
              status,
              r);

          // no need to decrement a refcount
        }
      }
    }
  }

  method evict_chunk(c: Cache, chunk: uint64)
  requires Inv(c)
  requires 0 <= chunk as int < NUM_CHUNKS
  {
    var i: uint64 := 0;
    while i as int < CHUNK_SIZE
    {
      var j: uint64 := chunk * CHUNK_SIZE as uint64 + i;
      try_evict_page(c, j);
      i := i + 1;
    }
  }

  method get_free_page(c: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint64,
    linear m: lOption<RWLock.R>,
    linear handle_opt: lOption<RWLock.Handle>,
    linear status_opt: lOption<CacheResources.R>
  )
  requires Inv(c)
  requires old_localState.WF()
  ensures localState.WF()
  ensures cache_idx == 0xffff_ffff ==>
      && m.lNone?
      && handle_opt.lNone?
      && status_opt.lNone?
  ensures cache_idx != 0xffff_ffff ==>
      && 0 <= cache_idx as int < CACHE_SIZE
      && m == lSome(RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int))))
      && handle_opt.lSome?
      && handle_opt.value.is_handle(c.key(cache_idx as int))
      && status_opt == lSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
  ensures localState.t == old_localState.t
  decreases *
  {
    var chunk: uint64 := localState.chunk_idx;

    var success := false;
    m := lNone;
    handle_opt := lNone;
    status_opt := lNone;

    while !success
    decreases *
    invariant localState.WF()
    invariant 0 <= chunk as int < NUM_CHUNKS
    invariant !success ==>
        && m.lNone?
        && handle_opt.lNone?
        && status_opt.lNone?
    invariant success ==>
        && 0 <= cache_idx as int < CACHE_SIZE
        && m == lSome(RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int))))
        && handle_opt.lSome?
        && handle_opt.value.is_handle(c.key(cache_idx as int))
        && status_opt == lSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
    {
      var i: uint64 := 0;

      while i < CHUNK_SIZE as uint64 && !success
      invariant 0 <= i as int <= CHUNK_SIZE
      invariant 0 <= chunk as int < NUM_CHUNKS
      invariant !success ==>
          && m.lNone?
          && handle_opt.lNone?
          && status_opt.lNone?
      invariant success ==>
          && 0 <= cache_idx as int < CACHE_SIZE
          && m == lSome(RWLock.Internal(RWLock.ReadingPending(c.key(cache_idx as int))))
          && handle_opt.lSome?
          && handle_opt.value.is_handle(c.key(cache_idx as int))
          && status_opt == lSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
      {
        cache_idx := chunk * CHUNK_SIZE as uint64 + i;

        dispose_lnone(m);
        dispose_lnone(handle_opt);
        dispose_lnone(status_opt);
        success, m, handle_opt, status_opt := try_alloc(
            c.status[cache_idx],
            c.key(cache_idx as int));

        i := i + 1;
      }

      if !success {
        // TODO mark stuff as 'not accessed'
        chunk := get_next_chunk(c);
        evict_chunk(c, chunk);
      }
    }

    inout localState.chunk_idx := chunk;
  }

  // Top level method

  method try_take_read_lock_disk_page(c: Cache, disk_idx: int,
      linear client: RWLock.R,
      linear inout localState: LocalState)
  returns (
    success: bool,
    linear handle_out: lOption<ReadonlyPageHandle>,
    linear client_out: lOption<RWLock.R>)
  requires Inv(c)
  requires 0 <= disk_idx < NUM_DISK_PAGES
  requires old_localState.WF()
  requires client == RWLock.Internal(RWLock.Client(old_localState.t))
  ensures !success ==> handle_out.lNone?
      && client_out == lSome(client)
  ensures success ==>
      && handle_out.lSome?
      && handle_out.value.is_page_handle(c, disk_idx, localState.t)
      && client_out.lNone?
  ensures old_localState.WF()
  decreases *
  {
    var cache_idx := atomic_index_lookup_read(c.cache_idx_of_page[disk_idx], disk_idx);

    if cache_idx == NOT_MAPPED {
      linear var m, handle_opt, status_opt;
      cache_idx, m, handle_opt, status_opt := get_free_page(c, inout localState);

      if cache_idx == 0xffff_ffff {
        dispose_lnone(m);
        dispose_lnone(handle_opt);
        dispose_lnone(status_opt);
        success := false;
        handle_out := lNone;
        client_out := lSome(client);
      } else {
        linear var r := unwrap_value(m);
        linear var handle: RWLock.Handle := unwrap_value(handle_opt);
        linear var status := unwrap_value(status_opt);
        linear var read_stub;
        linear var read_ticket_opt;

        linear var CacheEntryHandle(_, cache_entry, data, idx) := handle;

        success, cache_entry, status, read_ticket_opt := 
            atomic_index_lookup_add_mapping(
              c.cache_idx_of_page[disk_idx],
              disk_idx as uint64,
              cache_idx as uint64,
              cache_entry,
              status);

        if !success {
          success := false;
          handle_out := lNone;
          dispose_lnone(read_ticket_opt);
          AtomicStatusImpl.unsafe_dispose(r);
          AtomicStatusImpl.unsafe_dispose(status);
          AtomicStatusImpl.unsafe_dispose(cache_entry);
          AtomicStatusImpl.unsafe_dispose(data);
          AtomicStatusImpl.unsafe_dispose(idx);
          client_out := lSome(client);
        } else {
          r := inc_refcount_for_reading(
              c.read_refcounts[localState.t][cache_idx],
              c.key(cache_idx as int), localState.t, client, r);

          r := clear_exc_bit_during_load_phase(
              c.status[cache_idx],
              c.key(cache_idx as int), localState.t, r);

          read_stub := DiskIO.disk_read_sync(
              disk_idx as uint64, c.data[cache_idx], inout data, 
              unwrap_value(read_ticket_opt));

          status, cache_entry := CacheResources.finish_page_in(
              cache_idx as int, disk_idx as uint64,
              status, cache_entry, read_stub);

          ptr_write(c.disk_idx_of_entry[cache_idx],
              inout idx, disk_idx);

          /*readonly*/ linear var readonly_handle;
          r, readonly_handle := load_phase_finish(
              c.status[cache_idx],
              c.key(cache_idx as int), localState.t, r,
              RWLock.CacheEntryHandle(c.key(cache_idx as int), cache_entry, data, idx),
              status);

          success := true;
          handle_out := lSome(ReadonlyPageHandle(r, readonly_handle));
          client_out := lNone;
        }
      }
    } else {
      success, handle_out, client_out := try_take_read_lock_on_cache_entry(
          c, cache_idx as int, disk_idx as int, localState, client);
    }
  }
}
