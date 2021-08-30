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
  import RwLock
  import opened T = RwLockToken
  import opened CT = CacheTypes(aio)
  import opened CacheHandle
  import opened CacheStatusType
  import opened ClientCounter
  import opened BitOps

  datatype PageHandle = PageHandle(
    ptr: Ptr,
    cache_idx: uint64)

  glinear datatype WriteablePageHandle = WriteablePageHandle(
    ghost cache_idx: int,
    //ptr: Ptr,
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
      //&& handle.data.ptr == ptr
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

    predicate for_page_handle(ph: PageHandle)
    {
      && handle.data.ptr == ph.ptr
      && cache_idx == ph.cache_idx as int
    }
  }

  glinear datatype ReadonlyPageHandle = ReadonlyPageHandle(
    ghost cache_idx: int,
    //ptr: Ptr,
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
      && so.token.loc == cache.status[cache_idx].rwlock_loc
    }

    predicate for_page_handle(ph: PageHandle)
    {
      && so.b.data.ptr == ph.ptr
      && cache_idx == ph.cache_idx as int
    }
  }

  glinear datatype ClaimPageHandle = ClaimPageHandle(
    ghost cache_idx: int,
    //ptr: Ptr,
    glinear eo: T.Token
  )
  {
    predicate is_disk_page_handle(cache: Cache, t: int, disk_idx: int)
    requires cache.Inv()
    {
      && eo.val.M?
      && eo.val.exc.ExcClaim?
      && eo.val.exc.b.CacheEntryHandle?
      && eo.val.exc.b.cache_entry.disk_idx == disk_idx
      && 0 <= cache_idx as int < CACHE_SIZE
      && eo.val.exc.b.is_handle(cache.key(cache_idx as int))
      && eo.val.exc.t == t
      && eo.loc == cache.status[cache_idx].rwlock_loc
    }

    predicate for_page_handle(ph: PageHandle)
    {
      && eo.val.M?
      && eo.val.exc.ExcClaim?
      && eo.val.exc.b.data.ptr == ph.ptr
      && cache_idx == ph.cache_idx as int
    }
  }

  method try_take_read_lock_on_cache_entry(
      shared cache: Cache,
      cache_idx: uint64,
      expected_disk_idx: int64,
      shared localState: LocalState,
      glinear client: Client)
  returns (
    success: bool,
    glinear handle_out: glOption<ReadonlyPageHandle>,
    glinear client_out: glOption<Client>
  )
  requires cache.Inv()
  requires localState.WF()
  requires 0 <= cache_idx as int < CACHE_SIZE
  //requires client == RwLock.Internal(RwLock.Client(localState.t))
  ensures !success ==> handle_out.glNone?
      && client_out.glSome?
  ensures success ==>
      && handle_out.glSome?
      && handle_out.value.is_disk_page_handle(
          cache, localState.t as int, expected_disk_idx as int)
      && handle_out.value.cache_idx == cache_idx as int
      && client_out.glNone?
  decreases *
  {
    // 1. check if writelocked

    var is_exc_locked := cache.status[cache_idx].quicktest_is_exc_locked();
    if is_exc_locked {
      success := false;
      handle_out := glNone;
      client_out := glSome(client);
    } else {
      // 2. inc ref

      glinear var r := inc_refcount_for_shared(
          cache.read_refcounts[localState.t][cache_idx],
          localState.t as nat,
          client);

      // 3. check not writelocked, not free
      //        otherwise, dec and abort

      var is_accessed: bool;
      success, is_accessed, r := cache.status[cache_idx].is_exc_locked_or_free(
          localState.t as nat, r);

      if !success {
        glinear var client' := dec_refcount_for_shared_pending(
            cache.read_refcounts[localState.t][cache_idx],
            localState.t as nat,
            r);

        handle_out := glNone;
        client_out := glSome(client');
      } else {
        // 4. if !access, then mark accessed
        if !is_accessed {
          r := cache.status[cache_idx].mark_accessed(localState.t as nat, r);
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

        glinear var r_opt: glOption<T.Token> := glSome(r);

        glinear var handle_opt: glOption<T.SharedObtainedToken> := glNone;
        var is_done_reading := false;

        while !is_done_reading
        invariant !is_done_reading ==>
          && handle_opt.glNone?
          && r_opt.glSome?
          && r_opt.value.loc == cache.status[cache_idx].rwlock_loc
          && r_opt.value.val == RwLock.SharedHandle(RwLock.SharedPending2(localState.t as nat))
        invariant is_done_reading ==>
          && r_opt.glNone?
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx as nat))
          && handle_opt.value.t == localState.t as nat
          && handle_opt.value.b.CacheEntryHandle?
          && handle_opt.value.token.loc == cache.status[cache_idx].rwlock_loc
        decreases *
        {
          dispose_glnone(handle_opt);
          r := unwrap_value(r_opt);
          is_done_reading, r_opt, handle_opt := cache.status[cache_idx].is_reading(
              localState.t as nat,
              r);

          if !is_done_reading {
            io_cleanup(cache, DEFAULT_MAX_IO_EVENTS);
          }
        }

        dispose_glnone(r_opt);

        // Check the disk_idx

        var actual_disk_idx: int64 := cache.disk_idx_of_entry[cache_idx].read(
            T.borrow_sot(handle_opt.value).idx);

        if actual_disk_idx != expected_disk_idx {
          glinear var ho: T.SharedObtainedToken := unwrap_value(handle_opt);
          glinear var SharedObtainedToken(_, _, token) := ho;
          glinear var client' := dec_refcount_for_shared_obtained(
              cache.read_refcounts[localState.t][cache_idx],
              localState.t as nat, ho.b, token);

          success := false;
          handle_out := glNone;
          client_out := glSome(client');
        } else {
          success := true;
          handle_out := glSome(
              ReadonlyPageHandle(cache_idx as int, unwrap_value(handle_opt)));
          client_out := glNone;
        }
      }
    }
  }

  /*method take_write_lock_on_cache_entry(cache: Cache, cache_idx: int)
  returns (glinear r: T.Token, glinear handle: Handle)
  requires cache.Inv()
  requires 0 <= cache_idx < CACHE_SIZE
  ensures r == RwLock.Internal(RwLock.ExcLockObtained(cache.key(cache_idx)))
  ensures handle.is_handle(cache.key(cache_idx))
  decreases *
  {
    glinear var w_opt := glNone;
    var success := false;

    while !success 
    invariant success ==> w_opt == glSome(
        RwLock.Internal(RwLock.ExcPendingAwaitWriteBack(cache.key(cache_idx))))
    invariant !success ==> !has(w_opt)
    decreases *
    {
      dispose_glnone(w_opt);
      success, w_opt := cache.status[cache_idx].try_set_write_lock(
          cache.key(cache_idx));
    }

    glinear var w;
    w := unwrap_value(w_opt);

    success := false;

    while !success 
    invariant !success ==> w ==
        RwLock.Internal(RwLock.ExcPendingAwaitWriteBack(cache.key(cache_idx)))
    invariant success ==> w ==
        RwLock.Internal(RwLock.ExcPending(cache.key(cache_idx), 0))
    decreases *
    {
      success, w := cache.status[cache_idx].try_check_writeback_isnt_set(
          cache.key(cache_idx), w);
    }

    var j := 0;
    while j < NUM_THREADS
    invariant 0 <= j <= NUM_THREADS
    invariant w == 
        RwLock.Internal(RwLock.ExcPending(cache.key(cache_idx), j))
    {
      success := false;

      while !success 
      invariant !success ==> w ==
          RwLock.Internal(RwLock.ExcPending(cache.key(cache_idx), j))
      invariant success ==> w ==
          RwLock.Internal(RwLock.ExcPending(cache.key(cache_idx), j+1))
      decreases *
      {
        success, w := is_refcount_zero(cache.read_refcounts[j][cache_idx],
            cache.key(cache_idx), j, w);
      }

      j := j + 1;
    }

    r, handle := RwLock.transform_TakeWriteFinish(cache.key(cache_idx), w);
  }*/

  /*method release_write_lock_on_cache_entry(cache: Cache, cache_idx: int,
      glinear r: T.Token,
      glinear handle: Handle)
  requires cache.Inv()
  requires 0 <= cache_idx < CACHE_SIZE
  requires handle.is_handle(cache.key(cache_idx))
  requires r == RwLock.Internal(RwLock.ExcLockObtained(cache.key(cache_idx)))*/

  /*method take_write_lock_on_disk_entry(cache: Cache, disk_idx: int)
  requires 0 
  {
    
  }*/

  method get_next_chunk(shared cache: Cache, inout linear local: LocalState)
  returns (new_chunk: uint64)
  requires cache.Inv()
  requires old_local.WF()
  ensures 0 <= new_chunk as int < NUM_CHUNKS
  ensures local.WF()
  ensures local.t == old_local.t
  {
    atomic_block var l :=
        execute_atomic_fetch_add_uint32(cache.global_clockpointer, 1) { }

    l := l % (NUM_CHUNKS as uint32);
    var ci: uint32 := (l + CLEAN_AHEAD as uint32) % (NUM_CHUNKS as uint32);

    ghost var t := local.t;

    var i: uint32 := 0;
    while i < CHUNK_SIZE as uint32
    invariant local.WF()
    invariant t == local.t
    {
      var cache_idx := ci * (CHUNK_SIZE as uint32) + i;   

      glinear var write_back_r, ticket;
      var do_write_back;
      do_write_back, write_back_r, ticket :=
          cache.status[cache_idx].try_acquire_writeback(false);

      if do_write_back {
        var disk_idx := cache.disk_idx_of_entry[cache_idx].read(
            T.borrow_wb(write_back_r.value.token).idx);
        assert disk_idx != -1;

        disk_writeback_async(
            cache, inout local,
            disk_idx as uint64,
            cache_idx as uint64,
            unwrap_value(write_back_r),
            unwrap_value(ticket));
      } else {
        dispose_glnone(write_back_r);
        dispose_glnone(ticket);
      }

      i := i + 1;
    }

    new_chunk := l as uint64;
  }

  method check_all_refcounts_dont_wait(shared cache: Cache,
      cache_idx: uint64,
      glinear r: T.Token)
  returns (success: bool, glinear r': T.Token)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE
  requires r.loc == cache.status[cache_idx].rwlock_loc
  requires r.val.M?
  requires r.val.exc.ExcPending?
  requires r.val == RwLock.ExcHandle(RwLock.ExcPending(
      -1, 0, r.val.exc.clean, r.val.exc.b))
  ensures r'.loc == cache.status[cache_idx].rwlock_loc
  ensures r'.val.M?
  ensures r'.val.exc.ExcPending?
  ensures success ==> r'.val.exc.visited == NUM_THREADS
  ensures r'.val == RwLock.ExcHandle(RwLock.ExcPending(
      -1, r'.val.exc.visited, r.val.exc.clean, r.val.exc.b))
  {
    var i: uint64 := 0;
    success := true;
    r' := r;

    while i < (NUM_THREADS as uint64) && success
    invariant 0 <= i as int <= NUM_THREADS
    invariant r'.loc == cache.status[cache_idx].rwlock_loc
    invariant r'.val.M?
    invariant r'.val.exc.ExcPending?
    invariant success ==> r'.val.exc.visited == i as int
    invariant r'.val == RwLock.ExcHandle(RwLock.ExcPending(
        -1, r'.val.exc.visited, r.val.exc.clean, r.val.exc.b))

    {
      success, r' := is_refcount_eq(
          cache.read_refcounts[i][cache_idx],
          0, -1, i as nat, r');

      i := i + 1;
    }
    assert success ==> i as nat == NUM_THREADS;
  }

  method try_evict_page(shared cache: Cache, cache_idx: uint64)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE
  {
    // 1. get status

    atomic_block var status := execute_atomic_load(cache.status[cache_idx].atomic) { }

    // 2. if accessed, then clear 'access'

    if bit_or_uint8(status, flag_accessed) != 0 {
      cache.status[cache_idx].clear_accessed();
    }

    // 3. if status != CLEAN, abort

    if status != flag_clean {
      // no cleanup to do
    } else {
      // 4. inc ref count for shared lock
      // skipping this step, we don't need it
      //
      //glinear var r := inc_refcount_for_shared(
      //    cache.read_refcounts[localState.t][cache_idx],
      //    cache.key(cache_idx), localState.t);

      // 5. get the exc lock (Clean -> Clean | Exc) (or bail)

      var success;
      glinear var status, r, r_opt, status_opt;
      ghost var b;
      success, r_opt, b, status_opt := cache.status[cache_idx].take_exc_if_eq_clean();

      if !success {
        dispose_glnone(status_opt);
        dispose_glnone(r_opt);
      } else {
        // 6. try the rest of the read refcounts (or bail)

        status := unwrap_value(status_opt);
        r := unwrap_value(r_opt);

        success, r := check_all_refcounts_dont_wait(
            cache, cache_idx, r);

        if !success {
          cache.status[cache_idx].abandon_exc(r, status);
        } else {
          glinear var handle;
          var clean := r.val.exc.clean;
          r, handle := T.perform_Withdraw_TakeExcLockFinish(r);

          // 7. clear cache_idx_of_page lookup

          var disk_idx := cache.disk_idx_of_entry[cache_idx].read(handle.idx);

          glinear var CacheEntryHandle(key, cache_entry, data, idx) := handle;

          glinear var cache_empty := atomic_index_lookup_clear_mapping(
                cache.cache_idx_of_page[disk_idx],
                disk_idx as nat,
                cache_entry,
                status);

          handle := CacheEmptyHandle(key, cache_empty, data, idx);

          // 8. set to FREE

          cache.status[cache_idx].set_to_free(handle, r);

          // no need to decrement a refcount
        }
      }
    }
  }

  method evict_chunk(shared cache: Cache, chunk: uint64)
  requires cache.Inv()
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

  method get_free_page(shared cache: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint64,
    glinear m: glOption<T.Token>,
    glinear handle_opt: glOption<Handle>
  )
  requires cache.Inv()
  requires old_localState.WF()
  ensures localState.WF()
  ensures cache_idx == 0xffff_ffff ==>
      && m.glNone?
      && handle_opt.glNone?
  ensures cache_idx != 0xffff_ffff ==>
      && 0 <= cache_idx as int < CACHE_SIZE
      && m.glSome?
      && m.value.loc == cache.status[cache_idx].rwlock_loc
      && m.value.val == RwLock.ReadHandle(RwLock.ReadPending)
      && handle_opt.glSome?
      && handle_opt.value.is_handle(cache.key(cache_idx as int))
      && handle_opt.value.CacheEmptyHandle?
  ensures localState.t == old_localState.t
  decreases *
  {
    var chunk: uint64 := localState.chunk_idx;

    var success := false;
    m := glNone;
    handle_opt := glNone;

    ghost var t := localState.t;

    while !success
    decreases *
    invariant localState.WF()
    invariant localState.t == t
    invariant 0 <= chunk as int < NUM_CHUNKS
    invariant !success ==>
        && m.glNone?
        && handle_opt.glNone?
    invariant success ==>
        && 0 <= cache_idx as int < CACHE_SIZE
        && m.glSome?
        && m.value.loc == cache.status[cache_idx].rwlock_loc
        && m.value.val == RwLock.ReadHandle(RwLock.ReadPending)
        && handle_opt.glSome?
        && handle_opt.value.is_handle(cache.key(cache_idx as int))
        && handle_opt.value.CacheEmptyHandle?
    {
      var i: uint64 := 0;

      while i < CHUNK_SIZE as uint64 && !success
      invariant 0 <= i as int <= CHUNK_SIZE
      invariant 0 <= chunk as int < NUM_CHUNKS
      invariant !success ==>
          && m.glNone?
          && handle_opt.glNone?
      invariant success ==>
          && 0 <= cache_idx as int < CACHE_SIZE
          && m.glSome?
          && m.value.loc == cache.status[cache_idx].rwlock_loc
          && m.value.val == RwLock.ReadHandle(RwLock.ReadPending)
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx as int))
          && handle_opt.value.CacheEmptyHandle?
      {
        cache_idx := chunk * CHUNK_SIZE as uint64 + i;

        dispose_glnone(m);
        dispose_glnone(handle_opt);
        success, m, handle_opt := cache.status[cache_idx].try_alloc();

        i := i + 1;
      }

      if !success {
        // TODO mark stuff as 'not accessed'
        chunk := get_next_chunk(cache, inout localState);
        evict_chunk(cache, chunk);
      }
    }

    inout localState.chunk_idx := chunk;
  }

  // Top level method

  method try_take_read_lock_disk_page(shared cache: Cache, disk_idx: uint64,
      glinear client: Client,
      linear inout localState: LocalState)
  returns (
    ret_cache_idx: int64,
    glinear handle_out: glOption<ReadonlyPageHandle>,
    glinear client_out: glOption<Client>)
  requires cache.Inv()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES
  requires old_localState.WF()
  ensures ret_cache_idx == -1 ==> handle_out.glNone?
      && client_out.glSome?
  ensures ret_cache_idx != -1 ==>
      && handle_out.glSome?
      && handle_out.value.is_disk_page_handle(cache, localState.t as nat, disk_idx as nat)
      && client_out.glNone?
      && handle_out.value.cache_idx == ret_cache_idx as int
  ensures localState.WF()
  decreases *
  {
    var cache_idx := atomic_index_lookup_read(
        cache.cache_idx_of_page[disk_idx], disk_idx as nat);

    if cache_idx == NOT_MAPPED {
      glinear var m, handle_opt;
      cache_idx, m, handle_opt := get_free_page(cache, inout localState);

      if cache_idx == 0xffff_ffff {
        dispose_glnone(m);
        dispose_glnone(handle_opt);
        ret_cache_idx := -1;
        handle_out := glNone;
        client_out := glSome(client);
      } else {
        glinear var r := unwrap_value(m);
        glinear var handle: Handle := unwrap_value(handle_opt);
        glinear var read_stub;
        glinear var read_ticket_opt;

        glinear var CacheEmptyHandle(_, cache_empty, idx, data) := handle;

        glinear var cache_empty_opt, cache_reading_opt;
        var success;
        success, cache_empty_opt, cache_reading_opt, read_ticket_opt := 
            atomic_index_lookup_add_mapping(
              cache.cache_idx_of_page[disk_idx],
              disk_idx,
              cache_idx,
              cache_empty);

        if !success {
          ret_cache_idx := -1;
          handle_out := glNone;
          dispose_glnone(read_ticket_opt);
          dispose_glnone(cache_reading_opt);
          client_out := glSome(client);
          cache.status[cache_idx].abandon_reading_pending(
              r,
              CacheEmptyHandle(
                  cache.key(cache_idx as int),
                  unwrap_value(cache_empty_opt),
                  idx,
                  data));
        } else {
          dispose_glnone(cache_empty_opt);

          r := inc_refcount_for_reading(
              cache.read_refcounts[localState.t][cache_idx],
              localState.t as nat, client, r);

          r := cache.status[cache_idx].clear_exc_bit_during_load_phase(r);

          read_stub := disk_read_sync(
              disk_idx as uint64, cache.data[cache_idx], inout data, 
              unwrap_value(read_ticket_opt));

          glinear var cache_entry, status;

          status, cache_entry := CacheResources.finish_page_in(
              cache_idx as int, disk_idx as nat,
              unwrap_value(cache_reading_opt), read_stub);

          cache.disk_idx_of_entry[cache_idx].write(inout idx, disk_idx as int64);

          glinear var ceh := CacheEntryHandle(
              cache.key(cache_idx as int), cache_entry, idx, data);
          r := cache.status[cache_idx].load_phase_finish(
              r, ceh, status);

          ret_cache_idx := cache_idx as int64;
          handle_out := glSome(ReadonlyPageHandle(cache_idx as int,
              T.SharedObtainedToken(localState.t as int, ceh, r)));
          client_out := glNone;
        }
      }
    } else {
      var success;
      success, handle_out, client_out := try_take_read_lock_on_cache_entry(
          cache, cache_idx, disk_idx as int64, localState, client);
      if success {
        ret_cache_idx := cache_idx as int64;
      } else {
        ret_cache_idx := -1;
      }
    }
  }

  method take_read_lock_disk_page(
      shared cache: Cache,
      disk_idx: uint64,
      glinear client: Client,
      linear inout localState: LocalState)
  returns (
    ph: PageHandle,
    glinear handle_out: ReadonlyPageHandle
  )
  requires cache.Inv()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES
  requires old_localState.WF()
  ensures localState.WF()
  ensures handle_out.is_disk_page_handle(
      cache, localState.t as nat, disk_idx as nat)
  ensures handle_out.for_page_handle(ph)
  decreases *
  {
    var cache_idx: int64 := -1;

    glinear var handle_opt: glOption<ReadonlyPageHandle> := glNone;
    glinear var client_opt := glSome(client);

    while cache_idx == -1
    decreases *
    invariant cache_idx == -1 ==> client_opt.glSome?
    invariant localState.WF()
    invariant cache_idx != -1 ==>
      && handle_opt.glSome?
      && handle_opt.value.is_disk_page_handle(
            cache, localState.t as nat, disk_idx as nat)
      && handle_opt.value.cache_idx == cache_idx as int
    {
      dispose_anything(handle_opt);
      cache_idx, handle_opt, client_opt := try_take_read_lock_disk_page(
          cache, disk_idx, unwrap_value(client_opt), inout localState);
    }

    dispose_anything(client_opt);
    handle_out := unwrap_value(handle_opt);

    ph := PageHandle(cache.data[cache_idx], cache_idx as uint64);
  }

  method release_read_lock_disk_page(
      shared cache: Cache,
      shared localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear handle: ReadonlyPageHandle)
  returns (glinear client: Client)
  requires cache.Inv()
  requires localState.WF()
  requires handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires handle.for_page_handle(ph)
  {
    glinear var ReadonlyPageHandle(cache_idx, so) := handle;
    glinear var SharedObtainedToken(t, b, token) := so;
    client := dec_refcount_for_shared_obtained(
          cache.read_refcounts[localState.t][ph.cache_idx],
          localState.t as nat,
          b, token);
  }

  method claim(
      shared cache: Cache,
      shared localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear handle: ReadonlyPageHandle)
  returns (
    success: bool,
    glinear unclaim_handle: glOption<ReadonlyPageHandle>,
    glinear claim_handle: glOption<ClaimPageHandle>
  )
  requires cache.Inv()
  requires localState.WF()
  requires handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires handle.for_page_handle(ph)
  ensures !success ==> claim_handle.glNone?
  ensures !success ==> unclaim_handle == glSome(handle)
  {
    glinear var ReadonlyPageHandle(cache_idx, so) := handle;
    glinear var SharedObtainedToken(t, b, token) := so;
    glinear var token';
    success, token' := cache.status[ph.cache_idx].try_set_claim(token, RwLock.SharedObtained(t, b));

    var ghosty := true;
    if success {
      unclaim_handle := glNone;
      claim_handle := glSome(ClaimPageHandle(cache_idx, token'));
    } else {
      claim_handle := glNone;
      unclaim_handle := glSome(ReadonlyPageHandle(cache_idx, SharedObtainedToken(t, b, token')));
    }
  }
}
