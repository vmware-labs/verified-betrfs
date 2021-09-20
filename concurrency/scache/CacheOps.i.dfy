include "CacheIO.i.dfy"
include "../framework/ThreadUtils.s.dfy"

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
  import opened Cells
  import opened LinearSequence_i
  import opened ThreadUtils
  import opened PageSizeConstant

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
      && 0 <= status.cache_idx < CACHE_SIZE as int
      && handle.is_handle(cache.key(status.cache_idx))
      && status.cache_idx == cache_idx as int
      //&& handle.data.ptr == ptr
      && eo.loc == cache.status[status.cache_idx].rwlock_loc
      && eo.val.M?
      && eo.val.exc.ExcObtained?
      && eo.val == RwLock.ExcHandle(eo.val.exc)
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
      && 0 <= cache_idx as int < CACHE_SIZE as int
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
      && eo.val == RwLock.ExcHandle(eo.val.exc)
      && eo.val.exc.b.CacheEntryHandle?
      && eo.val.exc.b.cache_entry.disk_idx == disk_idx
      && 0 <= cache_idx as int < CACHE_SIZE as int
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
  requires 0 <= cache_idx as int < CACHE_SIZE as int
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

    var is_exc_locked := cache.status_atomic(cache_idx).quicktest_is_exc_locked();
    if is_exc_locked {
      success := false;
      handle_out := glNone;
      client_out := glSome(client);
    } else {
      // 2. inc ref

      glinear var r := inc_refcount_for_shared(
          cache.read_refcount_atomic(localState.t, cache_idx),
          localState.t as nat,
          client);

      // 3. check not writelocked, not free
      //        otherwise, dec and abort

      var is_accessed: bool;
      success, is_accessed, r := cache.status_atomic(cache_idx).is_exc_locked_or_free(
          localState.t as nat, r);

      if !success {
        glinear var client' := dec_refcount_for_shared_pending(
            cache.read_refcount_atomic(localState.t, cache_idx),
            localState.t as nat,
            r);

        handle_out := glNone;
        client_out := glSome(client');
      } else {
        // 4. if !access, then mark accessed
        if !is_accessed {
          r := cache.status_atomic(cache_idx).mark_accessed(localState.t as nat, r);
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
          is_done_reading, r_opt, handle_opt := cache.status_atomic(cache_idx).is_reading(
              localState.t as nat,
              r);

          if !is_done_reading {
            io_cleanup(cache, DEFAULT_MAX_IO_EVENTS);
          }
        }

        dispose_glnone(r_opt);

        // Check the disk_idx

        var actual_disk_idx: int64 := read_cell(
            cache.disk_idx_of_entry_ptr(cache_idx),
            T.borrow_sot(handle_opt.value).idx);

        if actual_disk_idx != expected_disk_idx {
          glinear var ho: T.SharedObtainedToken := unwrap_value(handle_opt);
          glinear var SharedObtainedToken(_, _, token) := ho;
          glinear var client' := dec_refcount_for_shared_obtained(
              cache.read_refcount_atomic(localState.t, cache_idx),
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

  method batch_start_writeback(shared cache: Cache, inout linear local: LocalState,
        batch_idx: uint64, is_urgent: bool)
  requires cache.Inv()
  requires old_local.WF()
  requires 0 <= batch_idx as int < NUM_CHUNKS as int
  ensures local.WF()
  ensures local.t == old_local.t
  decreases *
  {
    var i: uint32 := 0;
    while i < CHUNK_SIZE as uint32
    invariant local.WF()
    invariant local.t == old_local.t
    {
      var cache_idx := batch_idx * CHUNK_SIZE + i as uint64;

      glinear var write_back_r, ticket;
      var do_write_back;
      do_write_back, write_back_r, ticket :=
          cache.status_atomic(cache_idx as uint64).try_acquire_writeback(is_urgent);

      if do_write_back {
        var disk_idx := read_cell(
            cache.disk_idx_of_entry_ptr(cache_idx as uint64),
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
  }

  method move_hand(shared cache: Cache, inout linear local: LocalState, is_urgent: bool)
  requires cache.Inv()
  requires old_local.WF()
  ensures local.WF()
  ensures local.t == old_local.t
  ensures local.free_hand != 0xffff_ffff_ffff_ffff
  decreases *
  {
    var evict_hand: uint64 := local.free_hand;
    if evict_hand != 0xffff_ffff_ffff_ffff {
      //CAS(batch_busy[evict_hand], true, false)
      atomic_block var _ := execute_atomic_store(
          lseq_peek(cache.batch_busy, evict_hand),
          false) { }
    }

    var done := false;
    while !done
    invariant done ==> 0 <= evict_hand as int < NUM_CHUNKS as int
    invariant local.WF()
    invariant local.t == old_local.t
    decreases *
    {
      var l: uint32;
      atomic_block l :=
          execute_atomic_fetch_add_uint32(cache.global_clockpointer, 1) { }

      evict_hand := l as uint64 % NUM_CHUNKS;
      var cleaner_hand := (evict_hand + CLEAN_AHEAD as uint64) % NUM_CHUNKS;

      atomic_block var do_clean := execute_atomic_compare_and_set_strong(
            lseq_peek(cache.batch_busy, cleaner_hand), false, true) { }

      if do_clean {
        batch_start_writeback(cache, inout local, cleaner_hand, is_urgent);
        atomic_block var _ := execute_atomic_store(
            lseq_peek(cache.batch_busy, cleaner_hand), false) { }
      }

      atomic_block done := execute_atomic_compare_and_set_strong(
          lseq_peek(cache.batch_busy, evict_hand), false, true) { }
    }

    evict_batch(cache, evict_hand);
    inout local.free_hand := evict_hand;
  }

  method check_all_refcounts_dont_wait(shared cache: Cache,
      cache_idx: uint64,
      glinear r: T.Token)
  returns (success: bool, glinear r': T.Token)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  requires r.loc == cache.status[cache_idx].rwlock_loc
  requires r.val.M?
  requires r.val.exc.ExcPending?
  requires r.val == RwLock.ExcHandle(RwLock.ExcPending(
      -1, 0, r.val.exc.clean, r.val.exc.b))
  ensures r'.loc == cache.status[cache_idx].rwlock_loc
  ensures r'.val.M?
  ensures r'.val.exc.ExcPending?
  ensures success ==> r'.val.exc.visited == RC_WIDTH as int
  ensures r'.val == RwLock.ExcHandle(RwLock.ExcPending(
      -1, r'.val.exc.visited, r.val.exc.clean, r.val.exc.b))
  {
    var i: uint64 := 0;
    success := true;
    r' := r;

    while i < RC_WIDTH && success
    invariant 0 <= i as int <= RC_WIDTH as int
    invariant r'.loc == cache.status[cache_idx].rwlock_loc
    invariant r'.val.M?
    invariant r'.val.exc.ExcPending?
    invariant success ==> r'.val.exc.visited == i as int
    invariant r'.val == RwLock.ExcHandle(RwLock.ExcPending(
        -1, r'.val.exc.visited, r.val.exc.clean, r.val.exc.b))

    {
      success, r' := is_refcount_eq(
          cache.read_refcount_atomic(i, cache_idx),
          0, -1, i as nat, r');

      i := i + 1;
    }
    assert success ==> i as nat == RC_WIDTH as int;
  }

  method check_all_refcounts_with_t_block(shared cache: Cache,
      t: uint64,
      cache_idx: uint64,
      glinear r: T.Token)
  returns (glinear r': T.Token)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  requires r.loc == cache.status[cache_idx].rwlock_loc
  requires r.val.M?
  requires r.val.exc.ExcPending?
  requires r.val == RwLock.ExcHandle(RwLock.ExcPending(
      t as int, 0, r.val.exc.clean, r.val.exc.b))
  ensures r'.loc == cache.status[cache_idx].rwlock_loc
  ensures r'.val.M?
  ensures r'.val.exc.ExcPending?
  ensures r'.val.exc.visited == RC_WIDTH as int
  ensures r'.val == RwLock.ExcHandle(RwLock.ExcPending(
      t as int, r'.val.exc.visited, r.val.exc.clean, r.val.exc.b))
  decreases *
  {
    var i: uint64 := 0;
    r' := r;

    while i < RC_WIDTH
    invariant 0 <= i as int <= RC_WIDTH as int
    invariant r'.loc == cache.status[cache_idx].rwlock_loc
    invariant r'.val.M?
    invariant r'.val.exc.ExcPending?
    invariant r'.val == RwLock.ExcHandle(RwLock.ExcPending(
        t as int, i as int, r.val.exc.clean, r.val.exc.b))
    decreases *
    {
      var success;
      success, r' := is_refcount_eq(
          cache.read_refcount_atomic(i, cache_idx),
          (if i == t then 1 else 0), t as int, i as nat, r');

      if success {
        i := i + 1;
      } else {
        sleep(1);
      }
    }
  }

  method try_evict_page(shared cache: Cache, cache_idx: uint64)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  {
    // 1. get status

    atomic_block var status := execute_atomic_load(cache.status_atomic(cache_idx).atomic) { }

    // 2. if accessed, then clear 'access'

    if bit_or_uint8(status, flag_accessed) != 0 {
      cache.status_atomic(cache_idx).clear_accessed();
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
      success, r_opt, b, status_opt := cache.status_atomic(cache_idx).take_exc_if_eq_clean();

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
          cache.status_atomic(cache_idx).abandon_exc(r, status);
        } else {
          glinear var handle;
          var clean := r.val.exc.clean;
          r, handle := T.perform_Withdraw_TakeExcLockFinish(r);

          // 7. clear cache_idx_of_page lookup

          var disk_idx := read_cell(cache.disk_idx_of_entry_ptr(cache_idx), handle.idx);

          glinear var CacheEntryHandle(key, cache_entry, data, idx) := handle;

          glinear var cache_empty := atomic_index_lookup_clear_mapping(
                cache.cache_idx_of_page_atomic(disk_idx as uint64),
                disk_idx as nat,
                cache_entry,
                status);

          handle := CacheEmptyHandle(key, cache_empty, data, idx);

          // 8. set to FREE

          cache.status_atomic(cache_idx).set_to_free(handle, r);

          // no need to decrement a refcount
        }
      }
    }
  }

  method evict_batch(shared cache: Cache, chunk: uint64)
  requires cache.Inv()
  requires 0 <= chunk as int < NUM_CHUNKS as int
  {
    var i: uint64 := 0;
    while i < CHUNK_SIZE
    {
      var j: uint64 := chunk * CHUNK_SIZE + i;
      try_evict_page(cache, j);
      i := i + 1;
    }
  }

  method get_free_page(shared cache: Cache, linear inout localState: LocalState,
      new_status: uint8)
  returns (
    cache_idx: uint64,
    glinear m: T.Token,
    glinear handle: Handle
  )
  requires cache.Inv()
  requires old_localState.WF()
  requires new_status == flag_exc_accessed_reading_clean
        || new_status == flag_accessed_reading_clean
  ensures localState.WF()
  ensures
      && 0 <= cache_idx as int < CACHE_SIZE as int
      && m.loc == cache.status[cache_idx].rwlock_loc
      && (new_status == flag_exc_accessed_reading_clean ==>
           m.val == RwLock.ReadHandle(RwLock.ReadPending))
      && (new_status == flag_accessed_reading_clean ==>
           m.val == RwLock.ReadHandle(RwLock.ReadObtained(-1)))
      && handle.is_handle(cache.key(cache_idx as int))
      && handle.CacheEmptyHandle?
  ensures localState.t == old_localState.t
  decreases *
  {
    var success := false;
    glinear var m_opt: glOption<T.Token> := glNone;
    glinear var handle_opt: glOption<Handle> := glNone;

    ghost var t := localState.t;

    // XXX this logic is copied from splinter, but is it intentional
    // that we set this *before* the call to move_hand?
    var max_hand := localState.free_hand;

    if localState.free_hand == 0xffff_ffff_ffff_ffff {
      move_hand(cache, inout localState, false);
    }

    var num_passes: uint32 := 0;

    while !success
    decreases *
    invariant localState.WF()
    invariant localState.t == t
    invariant !success ==>
        && m_opt.glNone?
        && handle_opt.glNone?
    invariant localState.free_hand != 0xffff_ffff_ffff_ffff
    invariant success ==>
        && 0 <= cache_idx as int < CACHE_SIZE as int
        && m_opt.glSome?
        && m_opt.value.loc == cache.status[cache_idx].rwlock_loc
        && (new_status == flag_exc_accessed_reading_clean ==>
             m_opt.value.val == RwLock.ReadHandle(RwLock.ReadPending))
        && (new_status == flag_accessed_reading_clean ==>
             m_opt.value.val == RwLock.ReadHandle(RwLock.ReadObtained(-1)))
        && handle_opt.glSome?
        && handle_opt.value.is_handle(cache.key(cache_idx as int))
        && handle_opt.value.CacheEmptyHandle?
    {
      var chunk: uint64 := localState.free_hand; 

      var i: uint64 := 0;

      while i < CHUNK_SIZE && !success
      invariant 0 <= i as int <= CHUNK_SIZE as int
      invariant 0 <= chunk as int < NUM_CHUNKS as int
      invariant !success ==>
          && m_opt.glNone?
          && handle_opt.glNone?
      invariant success ==>
          && 0 <= cache_idx as int < CACHE_SIZE as int
          && m_opt.glSome?
          && m_opt.value.loc == cache.status[cache_idx].rwlock_loc
          && (new_status == flag_exc_accessed_reading_clean ==>
               m_opt.value.val == RwLock.ReadHandle(RwLock.ReadPending))
          && (new_status == flag_accessed_reading_clean ==>
               m_opt.value.val == RwLock.ReadHandle(RwLock.ReadObtained(-1)))
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx as int))
          && handle_opt.value.CacheEmptyHandle?
      {
        cache_idx := chunk * CHUNK_SIZE + i;

        dispose_glnone(m_opt);
        dispose_glnone(handle_opt);
        success, m_opt, handle_opt := cache.status_atomic(cache_idx).try_alloc(new_status);

        i := i + 1;
      }

      if !success {
        move_hand(cache, inout localState, num_passes != 0);
        if localState.free_hand < max_hand {
          if num_passes < 3 { num_passes := num_passes + 1; }
          if num_passes != 1 {
            thread_yield();
          }
          io_cleanup(cache, DEFAULT_MAX_IO_EVENTS);
        }
        max_hand := localState.free_hand;
      }
    }

    m := unwrap_value(m_opt);
    handle := unwrap_value(handle_opt);
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
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES as int
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
        cache.cache_idx_of_page_atomic(disk_idx), disk_idx as nat);

    if cache_idx == NOT_MAPPED {
      glinear var r, handle;
      cache_idx, r, handle := get_free_page(cache, inout localState,
          flag_exc_accessed_reading_clean);

      glinear var read_stub;
      glinear var read_ticket_opt;

      glinear var CacheEmptyHandle(_, cache_empty, idx, data) := handle;

      // TODO this seems to be done in a different order than the reference implementation
      // i.e., the ref impl first increments the refcount, then clears exc bit,
      // THEN checks the index mapping. Should make sure that's not a problem in the
      // reference impl.

      glinear var cache_empty_opt, cache_reading_opt;
      var success;
      success, cache_empty_opt, cache_reading_opt, read_ticket_opt := 
          atomic_index_lookup_add_mapping(
            cache.cache_idx_of_page_atomic(disk_idx),
            disk_idx,
            cache_idx,
            cache_empty);

      if !success {
        ret_cache_idx := -1;
        handle_out := glNone;
        dispose_glnone(read_ticket_opt);
        dispose_glnone(cache_reading_opt);
        client_out := glSome(client);
        cache.status_atomic(cache_idx).abandon_reading_pending(
            r,
            CacheEmptyHandle(
                cache.key(cache_idx as int),
                unwrap_value(cache_empty_opt),
                idx,
                data));
      } else {
        dispose_glnone(cache_empty_opt);

        r := inc_refcount_for_reading(
            cache.read_refcount_atomic(localState.t, cache_idx),
            localState.t as nat, client, r);

        r := cache.status_atomic(cache_idx).clear_exc_bit_during_load_phase(r);

        read_stub := disk_read_sync(
            disk_idx as uint64, cache.data_ptr(cache_idx), inout data, 
            unwrap_value(read_ticket_opt));

        glinear var cache_entry, status;

        status, cache_entry := CacheResources.finish_page_in(
            cache_idx as int, disk_idx as nat,
            unwrap_value(cache_reading_opt), read_stub);

        write_cell(
          cache.disk_idx_of_entry_ptr(cache_idx),
          inout idx,
          disk_idx as int64);

        glinear var ceh := CacheEntryHandle(
            cache.key(cache_idx as int), cache_entry, idx, data);
        r := cache.status_atomic(cache_idx).load_phase_finish(
            r, ceh, status);

        ret_cache_idx := cache_idx as int64;
        handle_out := glSome(ReadonlyPageHandle(cache_idx as int,
            T.SharedObtainedToken(localState.t as int, ceh, r)));
        client_out := glNone;
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

  method get(
      shared cache: Cache,
      linear inout localState: LocalState,
      disk_idx: uint64,
      glinear client: Client)
  returns (
    ph: PageHandle,
    glinear handle_out: ReadonlyPageHandle
  )
  requires cache.Inv()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES as int
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

    ph := PageHandle(cache.data_ptr(cache_idx as uint64), cache_idx as uint64);
  }

  method unget(
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
          cache.read_refcount_atomic(localState.t, ph.cache_idx),
          localState.t as nat,
          b, token);
  }

  // When this fails, the client needs to relinquish the read lock before trying again
  // (to avoid dead lock)
  method claim(
      shared cache: Cache,
      ghost localState: LocalState,
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
  ensures success ==> unclaim_handle.glNone?
  ensures success ==> claim_handle.glSome?
    && claim_handle.value.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
    && claim_handle.value.for_page_handle(ph)
  {
    glinear var ReadonlyPageHandle(cache_idx, so) := handle;
    glinear var SharedObtainedToken(t, b, token) := so;
    glinear var token';
    success, token' := cache.status_atomic(ph.cache_idx).try_set_claim(token, RwLock.SharedObtained(t, b));

    var ghosty := true;
    if success {
      unclaim_handle := glNone;
      claim_handle := glSome(ClaimPageHandle(cache_idx, token'));
    } else {
      claim_handle := glNone;
      unclaim_handle := glSome(ReadonlyPageHandle(cache_idx, SharedObtainedToken(t, b, token')));
    }
  }

  method unclaim(
      shared cache: Cache,
      ghost localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear handle: ClaimPageHandle)
  returns (glinear unclaim_handle: ReadonlyPageHandle)
  requires cache.Inv()
  requires localState.WF()
  requires handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires handle.for_page_handle(ph)
  ensures unclaim_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures unclaim_handle.for_page_handle(ph)
  {
    glinear var ClaimPageHandle(cache_idx, token) := handle;
    glinear var token';
    token' := cache.status_atomic(ph.cache_idx).unset_claim(token);
    unclaim_handle := ReadonlyPageHandle(cache_idx, SharedObtainedToken(localState.t as int, token.val.exc.b, token'));
  }
  
  // blocks until write lock is obtained
  method lock(
      shared cache: Cache,
      shared localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear claim_handle: ClaimPageHandle)
  returns (glinear write_handle: WriteablePageHandle)
  requires cache.Inv()
  requires localState.WF()
  requires claim_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires claim_handle.for_page_handle(ph)
  ensures write_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures write_handle.for_page_handle(ph)
  ensures write_handle.handle == claim_handle.eo.val.exc.b
  decreases *
  {
    var writeback_done := false;
    glinear var status_opt: glOption<CacheResources.CacheStatus> := glNone;

    glinear var ClaimPageHandle(cache_idx, token) := claim_handle;
    ghost var t := localState.t as int;
    ghost var rwlock_loc := cache.status_atomic(cache_idx as uint64).rwlock_loc;
    ghost var clean;

    token := cache.status_atomic(ph.cache_idx).set_exc(token);

    ghost var token_copy := token;
    while !writeback_done
    invariant !writeback_done ==> status_opt == glNone
    invariant !writeback_done ==> token == token_copy;
    invariant writeback_done ==>
      && token.val == RwLock.ExcHandle(RwLock.ExcPending(t, 0, clean, claim_handle.eo.val.exc.b))
      && token.loc == rwlock_loc
      && status_opt.glSome?
      && status_opt.value.cache_idx == cache_idx
      && status_opt.value.status == (if clean then Clean else Dirty)
    decreases *
    {
      dispose_glnone(status_opt);
      writeback_done, clean, token, status_opt :=
          cache.status_atomic(ph.cache_idx).try_check_writeback_isnt_set(t, token);
    }

    token := check_all_refcounts_with_t_block(cache, localState.t, ph.cache_idx, token);

    glinear var handle;
    token, handle := perform_Withdraw_TakeExcLockFinish(token);

    write_handle := WriteablePageHandle(cache_idx, handle, unwrap_value(status_opt), token);
  }

  method unlock(
      shared cache: Cache,
      ghost localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear write_handle: WriteablePageHandle)
  returns (glinear claim_handle: ClaimPageHandle)
  requires cache.Inv()
  requires localState.WF()
  requires write_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires write_handle.for_page_handle(ph)
  ensures claim_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures claim_handle.for_page_handle(ph)
  ensures write_handle.handle == claim_handle.eo.val.exc.b
  decreases *
  {
    glinear var WriteablePageHandle(cache_idx, handle, status, token) := write_handle;
    token := cache.status_atomic(ph.cache_idx).unset_exc(token, handle, status);
    claim_handle := ClaimPageHandle(cache_idx, token);
  }

  // runs get, claim, lock, retrying when necessary
  method get_claim_lock(
      shared cache: Cache,
      linear inout localState: LocalState,
      disk_idx: uint64,
      glinear client: Client)
  returns (ph: PageHandle, glinear write_handle: WriteablePageHandle)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES as int
  ensures localState.WF()
  ensures write_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures write_handle.for_page_handle(ph)
  decreases *
  {
    var success := false;
    glinear var write_handle_opt: glOption<WriteablePageHandle> := glNone;
    glinear var client_opt := glSome(client);

    ph := PageHandle(nullptr(), 0);

    while !success
    invariant !success ==> write_handle_opt == glNone
    invariant !success ==> client_opt.glSome?
    invariant success ==> client_opt.glNone?
    invariant success ==> write_handle_opt.glSome?
    invariant localState.WF()
    invariant success ==>
      && write_handle_opt.glSome?
      && write_handle_opt.value.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
      && write_handle_opt.value.for_page_handle(ph)
    decreases *
    {
      glinear var read_handle, read_handle_opt, claim_handle_opt;
      ph, read_handle := get(cache, inout localState, disk_idx, unwrap_value(client_opt));
      success, read_handle_opt, claim_handle_opt := claim(cache, localState, ph, disk_idx, read_handle);
      if !success {
        glinear var client';
        client' := unget(cache, localState, ph, disk_idx, unwrap_value(read_handle_opt));
        dispose_glnone(claim_handle_opt);
        client_opt := glSome(client');

        sleep(1); // TODO what's the best way to wait, here?
      } else {
        write_handle := lock(cache, localState, ph, disk_idx, unwrap_value(claim_handle_opt));
        dispose_glnone(write_handle_opt);
        dispose_glnone(read_handle_opt);
        write_handle_opt := glSome(write_handle);
        client_opt := glNone;
      }
    }

    write_handle := unwrap_value(write_handle_opt);
    dispose_glnone(client_opt);
  }

  method mark_dirty(
      shared cache: Cache,
      ghost localState: LocalState,
      ph: PageHandle,
      ghost disk_idx: uint64,
      glinear write_handle: WriteablePageHandle)
  returns (glinear write_handle': WriteablePageHandle)
  requires cache.Inv()
  requires localState.WF()
  requires write_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires write_handle.for_page_handle(ph)
  ensures write_handle'.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures write_handle'.for_page_handle(ph)
  ensures write_handle'.handle == write_handle.handle
  ensures !write_handle'.is_clean()
  {
    glinear var WriteablePageHandle(cache_idx, handle, status, eo) := write_handle;
    glinear var eo', status' := cache.status_atomic(ph.cache_idx).mark_dirty(eo, status);
    write_handle' := WriteablePageHandle(cache_idx, handle, status', eo');
  }

  method prefetch(
      shared cache: Cache,
      inout linear localState: LocalState,
      disk_idx: uint64)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as int < NUM_DISK_PAGES as int
  ensures localState.WF()
  decreases *
  {
    var done := false;
    while !done
    decreases *
    {
      var cache_idx := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(disk_idx), disk_idx as nat);
      if cache_idx == NOT_MAPPED {
      } else {
        glinear var m, handle;
        cache_idx, m, handle := get_free_page(cache, inout localState,
            flag_accessed_reading_clean);

        glinear var read_ticket_opt;
        glinear var CacheEmptyHandle(_, cache_empty, idx, data) := handle;

        glinear var cache_empty_opt, cache_reading_opt;
        var success;
        success, cache_empty_opt, cache_reading_opt, read_ticket_opt := 
            atomic_index_lookup_add_mapping(
              cache.cache_idx_of_page_atomic(disk_idx),
              disk_idx,
              cache_idx,
              cache_empty);

        if !success {
          dispose_glnone(read_ticket_opt);
          dispose_glnone(cache_reading_opt);
          cache.status_atomic(cache_idx).abandon_reading_pending(
              m,
              CacheEmptyHandle(
                  cache.key(cache_idx as int),
                  unwrap_value(cache_empty_opt),
                  idx,
                  data));
        } else {
          dispose_glnone(cache_empty_opt);

          disk_read_async(cache, inout localState,
              disk_idx, cache_idx, cache.data_ptr(cache_idx),
              unwrap_value(cache_reading_opt),
              m,
              data,
              idx,
              unwrap_value(read_ticket_opt));
          done := true;
        }
      }
    }
  }
}
