include "CacheIO.i.dfy"

module CacheOps(aio: AIO(CacheAIOParams, CacheIfc, CacheSSM)) {
  import opened Constants
  import opened AtomicStatusImpl
  import opened AtomicRefcountImpl
  import opened AtomicIndexLookupImpl
  import opened Atomics
  import opened GlinearOption
  import opened Ptrs
  import opened NativeTypes
  import opened Options
  import opened CIO = CacheIO(aio)
  import CacheResources
  import T = RwLockToken
  import opened CT = CacheTypes(aio)
  import opened CacheHandle
  import opened CacheStatusType

  linear datatype WriteablePageHandle = WriteablePageHandle(
    cache_idx: uint64,
    ptr: Ptr,
    glinear handle: Handle,
    glinear status: CacheResources.CacheStatus,
    glinear eo: T.Token
  )
  {
    predicate is_disk_page_handle(cache: Cache, t: int, disk_idx: int)
    requires cache.Inv()
    {
      && handle.CacheEntryHandle?
      && handle.cache_entry.disk_idx == disk_idx
      && 0 <= status.cache_idx < CACHE_SIZE
      && handle.is_handle(cache.key(status.cache_idx))
      && status.cache_idx == cache_idx as int
      && handle.data.ptr == ptr
      && eo.loc == cache.status[status.cache_idx].rwlock_loc
      && eo.val.M?
      && eo.val.exc.ExcObtained?
      && eo.val.exc.t == t
      && (eo.val.exc.clean ==> status.status == Clean)
      && (!eo.val.exc.clean ==> status.status == Dirty)
    }

    predicate is_clean()
    {
      status.status == Clean
    }
  }

  linear datatype ReadonlyPageHandle = ReadonlyPageHandle(
    cache_idx: uint64,
    ptr: Ptr,
    glinear so: T.SharedObtainedToken
  )
  {
    predicate is_disk_page_handle(cache: Cache, t: int, disk_idx: int)
    requires cache.Inv()
    {
      && so.b.CacheEntryHandle?
      && so.b.cache_entry.disk_idx == disk_idx
      && 0 <= cache_idx as int < CACHE_SIZE
      && so.is_handle(cache.key(cache_idx as int))
      && so.t == t
    }
  }

  method try_take_read_lock_on_cache_entry(
      shared cache: Cache,
      cache_idx: uint64,
      expected_disk_idx: uint64,
      shared localState: LocalState)
      //linear client: RWLock.R)
  returns (
    success: bool,
    glinear handle_out: glOption<ReadonlyPageHandle>
    //linear client_out: lOption<RWLock.R>
  )
  requires cache.Inv()
  requires localState.WF()
  requires 0 <= cache_idx as int < CACHE_SIZE
  //requires client == RWLock.Internal(RWLock.Client(localState.t))
  ensures !success ==> handle_out.glNone?
      //&& client_out == glSome(client)
  ensures success ==>
      && handle_out.glSome?
      && handle_out.value.is_disk_page_handle(
          cache, localState.t as int, expected_disk_idx as int)
      //&& client_out.glNone?
  decreases *
  {
    // 1. check if writelocked

    var is_exc_locked := cache.status[cache_idx].quicktest_is_exc_locked();
    if is_exc_locked {
      success := false;
      handle_out := glNone;
      //client_out := glSome(client);
    } else {
      // 2. inc ref

      linear var r := inc_refcount_for_shared(
          cache.read_refcounts[localState.t][cache_idx],
          localState.t);
          //client);

      // 3. check not writelocked, not free
      //        otherwise, dec and abort

      var is_accessed: bool;
      success, is_accessed, r := cache.status[cache_idx].is_exc_locked_or_free(
          localState.t, r);

      if !success {
        linear var client' := dec_refcount_for_shared_pending(
            cache.read_refcounts[localState.t][cache_idx],
            localState.t,
            r);

        handle_out := glNone;
        //client_out := glSome(client');
      } else {
        // 4. if !access, then mark accessed
        if !is_accessed {
          cache.status[cache_idx].mark_accessed(localState.t, r);
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

        linear var handle_opt: lOption<RWLock.Handle> := glNone;
        var is_done_reading := false;
        while !is_done_reading
        invariant !is_done_reading ==>
          && handle_opt.glNone?
          && r == RWLock.Internal(RWLock.SharedLockPending2(
              cache.key(cache_idx), localState.t))
        invariant is_done_reading ==>
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx))
          && r == RWLock.Internal(RWLock.SharedLockObtained(
              cache.key(cache_idx), localState.t))
        decreases *
        {
          dispose_lnone(handle_opt);
          is_done_reading, r, handle_opt := cache.status[cache_idx].is_reading(
              cache.key(cache_idx),
              localState.t,
              r);

          // TODO
          // if !is_done_reading, then spend the time to handle
          // some IO responses
        }

        // Check the disk_idx

        var actual_disk_idx := ptr_read(
            cache.disk_idx_of_entry[cache_idx],
            handle_opt.value.idx);

        if actual_disk_idx != expected_disk_idx {
          linear var client' := dec_refcount_for_shared_obtained(
              cache.read_refcounts[localState.t][cache_idx],
              cache.key(cache_idx), localState.t,
              r, unwrap_value(handle_opt));

          success := false;
          handle_out := glNone;
          //client_out := glSome(client');
        } else {
          success := true;
          handle_out := glSome(
              ReadonlyPageHandle(r, unwrap_value(handle_opt)));
          //client_out := glNone;
        }
      }
    }
  }

  /*

  /*method take_write_lock_on_cache_entry(cache: Cache, cache_idx: int)
  returns (linear r: RWLock.R, linear handle: RWLock.Handle)
  requires Inv(cache)
  requires 0 <= cache_idx < CACHE_SIZE
  ensures r == RWLock.Internal(RWLock.ExcLockObtained(cache.key(cache_idx)))
  ensures handle.is_handle(cache.key(cache_idx))
  decreases *
  {
    linear var w_opt := glNone;
    var success := false;

    while !success 
    invariant success ==> w_opt == glSome(
        RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(cache.key(cache_idx))))
    invariant !success ==> !has(w_opt)
    decreases *
    {
      dispose_lnone(w_opt);
      success, w_opt := cache.status[cache_idx].try_set_write_lock(
          cache.key(cache_idx));
    }

    linear var w;
    w := unwrap_value(w_opt);

    success := false;

    while !success 
    invariant !success ==> w ==
        RWLock.Internal(RWLock.ExcLockPendingAwaitWriteBack(cache.key(cache_idx)))
    invariant success ==> w ==
        RWLock.Internal(RWLock.ExcLockPending(cache.key(cache_idx), 0))
    decreases *
    {
      success, w := cache.status[cache_idx].try_check_writeback_isnt_set(
          cache.key(cache_idx), w);
    }

    var j := 0;
    while j < NUM_THREADS
    invariant 0 <= j <= NUM_THREADS
    invariant w == 
        RWLock.Internal(RWLock.ExcLockPending(cache.key(cache_idx), j))
    {
      success := false;

      while !success 
      invariant !success ==> w ==
          RWLock.Internal(RWLock.ExcLockPending(cache.key(cache_idx), j))
      invariant success ==> w ==
          RWLock.Internal(RWLock.ExcLockPending(cache.key(cache_idx), j+1))
      decreases *
      {
        success, w := is_refcount_zero(cache.read_refcounts[j][cache_idx],
            cache.key(cache_idx), j, w);
      }

      j := j + 1;
    }

    r, handle := RWLock.transform_TakeWriteFinish(cache.key(cache_idx), w);
  }*/

  /*method release_write_lock_on_cache_entry(cache: Cache, cache_idx: int,
      linear r: RWLock.R,
      linear handle: RWLock.Handle)
  requires Inv(cache)
  requires 0 <= cache_idx < CACHE_SIZE
  requires handle.is_handle(cache.key(cache_idx))
  requires r == RWLock.Internal(RWLock.ExcLockObtained(cache.key(cache_idx)))*/

  /*method take_write_lock_on_disk_entry(cache: Cache, disk_idx: int)
  requires 0 
  {
    
  }*/

  method get_next_chunk(cache: Cache)
  returns (new_chunk: uint64)
  requires Inv(cache)
  ensures 0 <= new_chunk as int < NUM_CHUNKS
  {
    var l: uint32 := fetch_add_uint32(cache.global_clockpointer, 1);
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
          cache.status[cache_idx].try_acquire_writeback(
              cache.key(cache_idx as int),
              false);

      if do_write_back {
        linear var readonly_handle: RWLock.Handle := unwrap_value(readonly_handle_opt);
        /*readonly*/ linear var CacheEntryHandle(
            _, cache_entry, data, idx) := readonly_handle;

        var disk_idx := ptr_read(cache.disk_idx_of_entry[cache_idx], idx);
        assert disk_idx != -1;

        linear var wgs := CacheIOImpl.WritebackGhostState(
            unwrap_value(write_back_r), cache_entry, idx);

        CacheIOImpl.disk_writeback_async(
            disk_idx as uint64,
            cache.data[cache_idx],
            data, wgs, unwrap_value(ticket));

        /*} else {
          readonly_handle := RWLock.CacheEntryHandle(cache_entry, data, idx);
          cache.status[cache_idx].release_writeback(cache.key(cache_idx as int),
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

  method check_all_refcounts_dont_wait(cache: Cache,
      cache_idx: uint64,
      linear r: RWLock.R)
  returns (success: bool, linear r': RWLock.R)
  requires Inv(cache)
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires r.Internal? && r.q.ExcLockPending?
  requires r == RWLock.Internal(RWLock.ExcLockPending(
      cache.key(cache_idx as int), -1, 0, r.q.clean))
  ensures r'.Internal?
  ensures r'.q.ExcLockPending?
  ensures r'.q.key == cache.key(cache_idx as int)
  ensures r'.q.t == -1
  ensures r'.q.clean == r.q.clean
  ensures success ==> r'.q.visited == NUM_THREADS

  method try_evict_page(cache: Cache, cache_idx: uint64)
  requires Inv(cache)
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires 0 <= cache_idx as int < CACHE_SIZE
  {
    // 1. get status

    var status := atomic_read(cache.status[cache_idx]);

    // 2. if accessed, then clear 'access'

    if bit_or(status, flag_accessed) != 0 {
      cache.status[cache_idx].clear_accessed(cache.key(cache_idx as int));
    }

    // 3. if status != CLEAN, abort

    if status != flag_clean {
      // no cleanup to do
    } else {
      // 4. inc ref count for shared lock
      // skipping this step, we don't need it
      //
      //linear var r := inc_refcount_for_shared(
      //    cache.read_refcounts[localState.t][cache_idx],
      //    cache.key(cache_idx), localState.t);

      // 5. get the exc lock (Clean -> Clean | Exc) (or bail)

      var success;
      linear var status, r, r_opt, status_opt, handle_opt;
      success, r_opt, status_opt, handle_opt := cache.status[cache_idx].take_exc_if_eq_clean(
            cache.key(cache_idx as int));

      if !success {
        dispose_lnone(status_opt);
        dispose_lnone(r_opt);
        dispose_lnone(handle_opt);
      } else {
        // 6. try the rest of the read refcounts (or bail)

        status := unwrap_value(status_opt);
        r := unwrap_value(r_opt);

        success, r := check_all_refcounts_dont_wait(
            cache, cache_idx, r);

        if !success {
          cache.status[cache_idx].abandon_exc(
              cache.key(cache_idx as int),
              status, r, unwrap_value(handle_opt));
        } else {
          linear var handle;
          var clean := r.q.clean;
          r, handle := RWLockMethods.transform_TakeExcLockFinish(
              cache.key(cache_idx as int), -1, clean, r, unwrap_value(handle_opt));

          // 7. clear cache_idx_of_page lookup

          var disk_idx := ptr_read(
              cache.disk_idx_of_entry[cache_idx],
              handle.idx);

          linear var CacheEntryHandle(key, cache_entry, data, idx) := handle;

          cache_entry, status := atomic_index_lookup_clear_mapping(
                cache.cache_idx_of_page[disk_idx],
                disk_idx,
                cache_entry,
                status);

          // 8. set to FREE

          cache.status[cache_idx].set_to_free(
              cache.key(cache_idx as int),
              RWLock.CacheEntryHandle(key, cache_entry, data, idx),
              status,
              r);

          // no need to decrement a refcount
        }
      }
    }
  }

  method evict_chunk(cache: Cache, chunk: uint64)
  requires Inv(cache)
  requires 0 <= chunk as int < NUM_CHUNKS
  {
    var i: uint64 := 0;
    while i as int < CHUNK_SIZE
    {
      var j: uint64 := chunk * CHUNK_SIZE as uint64 + i;
      try_evict_page(cache, j);
      i := i + 1;
    }
  }

  method get_free_page(cache: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint64,
    linear m: lOption<RWLock.R>,
    linear handle_opt: lOption<RWLock.Handle>,
    linear status_opt: lOption<CacheResources.R>
  )
  requires Inv(cache)
  requires old_localState.WF()
  ensures localState.WF()
  ensures cache_idx == 0xffff_ffff ==>
      && m.glNone?
      && handle_opt.glNone?
      && status_opt.glNone?
  ensures cache_idx != 0xffff_ffff ==>
      && 0 <= cache_idx as int < CACHE_SIZE
      && m == glSome(RWLock.Internal(RWLock.ReadingPending(cache.key(cache_idx as int))))
      && handle_opt.glSome?
      && handle_opt.value.is_handle(cache.key(cache_idx as int))
      && status_opt == glSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
  ensures localState.t == old_localState.t
  decreases *
  {
    var chunk: uint64 := localState.chunk_idx;

    var success := false;
    m := glNone;
    handle_opt := glNone;
    status_opt := glNone;

    while !success
    decreases *
    invariant localState.WF()
    invariant 0 <= chunk as int < NUM_CHUNKS
    invariant !success ==>
        && m.glNone?
        && handle_opt.glNone?
        && status_opt.glNone?
    invariant success ==>
        && 0 <= cache_idx as int < CACHE_SIZE
        && m == glSome(RWLock.Internal(RWLock.ReadingPending(cache.key(cache_idx as int))))
        && handle_opt.glSome?
        && handle_opt.value.is_handle(cache.key(cache_idx as int))
        && status_opt == glSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
    {
      var i: uint64 := 0;

      while i < CHUNK_SIZE as uint64 && !success
      invariant 0 <= i as int <= CHUNK_SIZE
      invariant 0 <= chunk as int < NUM_CHUNKS
      invariant !success ==>
          && m.glNone?
          && handle_opt.glNone?
          && status_opt.glNone?
      invariant success ==>
          && 0 <= cache_idx as int < CACHE_SIZE
          && m == glSome(RWLock.Internal(RWLock.ReadingPending(cache.key(cache_idx as int))))
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx as int))
          && status_opt == glSome(CacheResources.CacheStatus(cache_idx as int, CacheResources.Empty))
      {
        cache_idx := chunk * CHUNK_SIZE as uint64 + i;

        dispose_lnone(m);
        dispose_lnone(handle_opt);
        dispose_lnone(status_opt);
        success, m, handle_opt, status_opt := cache.status[cache_idx].try_alloc(
            cache.key(cache_idx as int));

        i := i + 1;
      }

      if !success {
        // TODO mark stuff as 'not accessed'
        chunk := get_next_chunk(cache);
        evict_chunk(cache, chunk);
      }
    }

    inout localState.chunk_idx := chunk;
  }

  // Top level method

  method try_take_read_lock_disk_page(cache: Cache, disk_idx: int,
      linear client: RWLock.R,
      linear inout localState: LocalState)
  returns (
    success: bool,
    linear handle_out: lOption<ReadonlyPageHandle>,
    linear client_out: lOption<RWLock.R>)
  requires Inv(cache)
  requires 0 <= disk_idx < NUM_DISK_PAGES
  requires old_localState.WF()
  requires client == RWLock.Internal(RWLock.Client(old_localState.t))
  ensures !success ==> handle_out.glNone?
      && client_out == glSome(client)
  ensures success ==>
      && handle_out.glSome?
      && handle_out.value.is_disk_page_handle(cache, localState.t, disk_idx)
      && client_out.glNone?
  ensures old_localState.WF()
  decreases *
  {
    var cache_idx := atomic_index_lookup_read(cache.cache_idx_of_page[disk_idx], disk_idx);

    if cache_idx == NOT_MAPPED {
      linear var m, handle_opt, status_opt;
      cache_idx, m, handle_opt, status_opt := get_free_page(cache, inout localState);

      if cache_idx == 0xffff_ffff {
        dispose_lnone(m);
        dispose_lnone(handle_opt);
        dispose_lnone(status_opt);
        success := false;
        handle_out := glNone;
        client_out := glSome(client);
      } else {
        linear var r := unwrap_value(m);
        linear var handle: RWLock.Handle := unwrap_value(handle_opt);
        linear var status := unwrap_value(status_opt);
        linear var read_stub;
        linear var read_ticket_opt;

        linear var CacheEntryHandle(_, cache_entry, data, idx) := handle;

        success, cache_entry, status, read_ticket_opt := 
            atomic_index_lookup_add_mapping(
              cache.cache_idx_of_page[disk_idx],
              disk_idx as uint64,
              cache_idx as uint64,
              cache_entry,
              status);

        if !success {
          success := false;
          handle_out := glNone;
          dispose_lnone(read_ticket_opt);
          client_out := glSome(client);
          cache.status[cache_idx].abandon_reading_pending(
              cache.key(cache_idx as int),
              status,
              r,
              RWLock.CacheEntryHandle(
                  cache.key(cache_idx as int),
                  cache_entry, data, idx));
        } else {
          r := inc_refcount_for_reading(
              cache.read_refcounts[localState.t][cache_idx],
              cache.key(cache_idx as int), localState.t, client, r);

          r := cache.status[cache_idx].clear_exc_bit_during_load_phase(
              cache.key(cache_idx as int), localState.t, r);

          read_stub := CacheIOImpl.disk_read_sync(
              disk_idx as uint64, cache.data[cache_idx], inout data, 
              unwrap_value(read_ticket_opt));

          status, cache_entry := CacheResources.finish_page_in(
              cache_idx as int, disk_idx as uint64,
              status, cache_entry, read_stub);

          ptr_write(cache.disk_idx_of_entry[cache_idx],
              inout idx, disk_idx);

          /*readonly*/ linear var readonly_handle;
          r, readonly_handle := cache.status[cache_idx].load_phase_finish(
              cache.key(cache_idx as int), localState.t, r,
              RWLock.CacheEntryHandle(cache.key(cache_idx as int), cache_entry, data, idx),
              status);

          success := true;
          handle_out := glSome(ReadonlyPageHandle(r, readonly_handle));
          client_out := glNone;
        }
      }
    } else {
      success, handle_out, client_out := try_take_read_lock_on_cache_entry(
          cache, cache_idx as int, disk_idx as int, localState, client);
    }
  }
  */
}
