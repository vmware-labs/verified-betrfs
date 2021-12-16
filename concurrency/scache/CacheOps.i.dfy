include "CacheIO.i.dfy"
include "../framework/ThreadUtils.s.dfy"
include "CacheWritebackBatch.i.dfy"

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
  import CWB = CacheWritebackBatch(aio)
  import opened IocbStruct
  import opened CacheAIOParams
  import opened GlinearMap

  datatype PageHandleIdx = PageHandleIdx(
    ghost ptr: Ptr,
    cache_idx: uint32)

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

    predicate for_page_handle(ph: PageHandleIdx)
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

    predicate for_page_handle(ph: PageHandleIdx)
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

    predicate for_page_handle(ph: PageHandleIdx)
    {
      && eo.val.M?
      && eo.val.exc.ExcClaim?
      && eo.val.exc.b.data.ptr == ph.ptr
      && cache_idx == ph.cache_idx as int
    }
  }

  method {:cpp_inline} try_take_read_lock_on_cache_entry(
      shared cache: Cache,
      cache_idx: uint32,
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
  requires client.loc == cache.counter_loc
  ensures !success ==> handle_out.glNone?
      && client_out.glSome?
      && client_out.value.loc == cache.counter_loc
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
            io_cleanup(cache, DEFAULT_MAX_IO_EVENTS_64());
          }
        }

        dispose_glnone(r_opt);

        // Check the disk_idx

        var ph := read_cell(
            cache.page_handle_ptr(cache_idx),
            T.borrow_sot(handle_opt.value).idx);
        var actual_disk_idx: int64 := ph.disk_addr / PageSize64() as int64;

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

  /*
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
            cache.page_handle_ptr(cache_idx as uint64),
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
  */

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

      evict_hand := l as uint64 % NUM_CHUNKS_64();
      var cleaner_hand := (evict_hand + CLEAN_AHEAD_64()) % NUM_CHUNKS_64();

      atomic_block var do_clean := execute_atomic_compare_and_set_strong(
            lseq_peek(cache.batch_busy, cleaner_hand), false, true) { }

      if do_clean {
        CWB.batch_start_writeback(cache, inout local, cleaner_hand as uint32, is_urgent);
        atomic_block var _ := execute_atomic_store(
            lseq_peek(cache.batch_busy, cleaner_hand), false) { }
      }

      atomic_block done := execute_atomic_compare_and_set_strong(
          lseq_peek(cache.batch_busy, evict_hand), false, true) { }
    }

    evict_batch(cache, evict_hand as uint32);
    inout local.free_hand := evict_hand;
  }

  method check_all_refcounts_dont_wait(shared cache: Cache,
      cache_idx: uint32,
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

    while i < RC_WIDTH_64() && success
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
      cache_idx: uint32,
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

    while i < RC_WIDTH_64()
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
        pause();
      }
    }
  }

  method try_evict_page(shared cache: Cache, cache_idx: uint32)
  requires cache.Inv()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  {
    // 1. get status

    atomic_block var status := execute_atomic_load(cache.status_atomic(cache_idx).atomic) { }

    // 2. if accessed, then clear 'access'

    if bit_or_uint8(status, flag_accessed()) != 0 {
      cache.status_atomic(cache_idx).clear_accessed();
    }

    // 3. if status != CLEAN, abort

    if status != flag_clean() {
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

          var ph := read_cell(cache.page_handle_ptr(cache_idx), handle.idx);
          var disk_idx := ph.disk_addr / PageSize64() as int64;

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

  method evict_batch(shared cache: Cache, chunk: uint32)
  requires cache.Inv()
  requires 0 <= chunk as int < NUM_CHUNKS as int
  {
    var i: uint32 := 0;
    while i < CHUNK_SIZE_32()
    {
      var j: uint32 := chunk * CHUNK_SIZE_32() + i;
      try_evict_page(cache, j);
      i := i + 1;
    }
  }

  method get_free_page(shared cache: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint32,
    glinear m: T.Token,
    glinear handle: Handle
  )
  requires cache.Inv()
  requires old_localState.WF()
  ensures localState.WF()
  ensures
      && 0 <= cache_idx as int < CACHE_SIZE as int
      && m.loc == cache.status[cache_idx].rwlock_loc
      && m.val == RwLock.ReadHandle(RwLock.ReadPending)
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
        && m_opt.value.val == RwLock.ReadHandle(RwLock.ReadPending)
        && handle_opt.glSome?
        && handle_opt.value.is_handle(cache.key(cache_idx as int))
        && handle_opt.value.CacheEmptyHandle?
    {
      var chunk: uint32 := localState.free_hand as uint32;

      var i: uint32 := 0;

      while i < CHUNK_SIZE_32() && !success
      invariant 0 <= i as int <= CHUNK_SIZE as int
      invariant 0 <= chunk as int < NUM_CHUNKS as int
      invariant !success ==>
          && m_opt.glNone?
          && handle_opt.glNone?
      invariant success ==>
          && 0 <= cache_idx as int < CACHE_SIZE as int
          && m_opt.glSome?
          && m_opt.value.loc == cache.status[cache_idx].rwlock_loc
          && m_opt.value.val == RwLock.ReadHandle(RwLock.ReadPending)
          && handle_opt.glSome?
          && handle_opt.value.is_handle(cache.key(cache_idx as int))
          && handle_opt.value.CacheEmptyHandle?
      {
        cache_idx := chunk * CHUNK_SIZE_32() + i;

        dispose_glnone(m_opt);
        dispose_glnone(handle_opt);
        success, m_opt, handle_opt := cache.status_atomic(cache_idx).try_alloc();

        i := i + 1;
      }

      if !success {
        move_hand(cache, inout localState, num_passes != 0);
        if localState.free_hand < max_hand {
          if num_passes < 3 { num_passes := num_passes + 1; }
          if num_passes != 1 {
            //thread_yield();
          }
          io_cleanup(cache, DEFAULT_MAX_IO_EVENTS_64());
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
  requires client.loc == cache.counter_loc
  ensures ret_cache_idx == -1 ==> handle_out.glNone?
      && client_out.glSome?
      && client_out.value.loc == cache.counter_loc
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
      cache_idx, r, handle := get_free_page(cache, inout localState);

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

        var ph := read_cell(
          cache.page_handle_ptr(cache_idx),
          idx);
        write_cell(
          cache.page_handle_ptr(cache_idx),
          inout idx,
          PageHandle(ph.data_ptr, disk_idx as int64 * PageSize64() as int64));

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
    ph: PageHandleIdx,
    glinear handle_out: ReadonlyPageHandle
  )
  requires cache.Inv()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES as int
  requires old_localState.WF()
  requires client.loc == cache.counter_loc
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
      && client_opt.value.loc == cache.counter_loc
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

    ph := PageHandleIdx(cache.data_ptr(cache_idx as uint32), cache_idx as uint32);
  }

  method unget(
      shared cache: Cache,
      shared localState: LocalState,
      ph: PageHandleIdx,
      ghost disk_idx: uint64,
      glinear handle: ReadonlyPageHandle)
  returns (glinear client: Client)
  requires cache.Inv()
  requires localState.WF()
  requires handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  requires handle.for_page_handle(ph)
  ensures client.loc == cache.counter_loc
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
      ph: PageHandleIdx,
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
      ph: PageHandleIdx,
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
      ph: PageHandleIdx,
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
    ghost var rwlock_loc := cache.status_atomic(cache_idx as uint32).rwlock_loc;
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
      if !writeback_done {
        io_cleanup(cache, DEFAULT_MAX_IO_EVENTS_64());
      }
    }

    token := check_all_refcounts_with_t_block(cache, localState.t, ph.cache_idx, token);

    glinear var handle;
    token, handle := perform_Withdraw_TakeExcLockFinish(token);

    write_handle := WriteablePageHandle(cache_idx, handle, unwrap_value(status_opt), token);
  }

  method unlock(
      shared cache: Cache,
      ghost localState: LocalState,
      ph: PageHandleIdx,
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
  returns (ph: PageHandleIdx, glinear write_handle: WriteablePageHandle)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as nat < NUM_DISK_PAGES as int
  requires client.loc == cache.counter_loc
  ensures localState.WF()
  ensures write_handle.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
  ensures write_handle.for_page_handle(ph)
  decreases *
  {
    var success := false;
    glinear var write_handle_opt: glOption<WriteablePageHandle> := glNone;
    glinear var client_opt := glSome(client);

    ph := PageHandleIdx(nullptr(), 0);

    while !success
    invariant !success ==> write_handle_opt == glNone
    invariant !success ==> client_opt.glSome?
      && client_opt.value.loc == cache.counter_loc
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

        pause();
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
      ph: PageHandleIdx,
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

  /*
  method prefetch_one(
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
    invariant localState.WF()
    {
      var cache_idx := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(disk_idx), disk_idx as nat);
      if cache_idx == NOT_MAPPED {
      } else {
        glinear var m, handle;
        cache_idx, m, handle := get_free_page(cache, inout localState);

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

          m := cache.status_atomic(cache_idx).clear_exc_bit_during_load_phase(m);

          write_cell(
            cache.page_handle_ptr(cache_idx),
            inout idx,
            disk_idx as int64 * PageSize64() as int64);

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
  */

  // note: page_sync only makes sense if we're in read mode, NOT in write or even claim mode
  // (in which case it would fail silently)
  // In general though it effectively has no specification that can be useful for verifying
  // sync code, because there's no way to determine when the page_sync actually completes
  method page_sync_nonblocking(
      shared cache: Cache,
      inout linear localState: LocalState,
      ph: PageHandleIdx)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= ph.cache_idx as int < CACHE_SIZE
  decreases *
  {
    var cache_idx := ph.cache_idx;

    var do_write_back : bool;
    glinear var write_back_r, ticket;
    do_write_back, write_back_r, ticket :=
        cache.status_atomic(cache_idx).try_acquire_writeback(true);

    if do_write_back {
      var p := read_cell(
          cache.page_handle_ptr(cache_idx),
          T.borrow_wb(write_back_r.value.token).idx);
      var disk_idx := p.disk_addr / PageSize64() as int64;
      assert disk_idx != -1;

      disk_writeback_async(
          cache, inout localState,
          disk_idx as uint64,
          cache_idx,
          unwrap_value(write_back_r),
          unwrap_value(ticket));
    } else {
      dispose_glnone(write_back_r);
      dispose_glnone(ticket);
    }
  }

  // TODO could give this a stronger specification that ensures it is actually doing a sync
  method page_sync_blocking(
      shared cache: Cache,
      inout linear localState: LocalState,
      ph: PageHandleIdx)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= ph.cache_idx as int < CACHE_SIZE
  decreases *
  {
    var cache_idx := ph.cache_idx;

    var do_write_back : bool;
    glinear var write_back_r, ticket;
    do_write_back, write_back_r, ticket :=
        cache.status_atomic(cache_idx).try_acquire_writeback(true);

    if do_write_back {
      var p := read_cell(
          cache.page_handle_ptr(cache_idx),
          T.borrow_wb(write_back_r.value.token).idx);
      var disk_idx := p.disk_addr / PageSize64() as int64;
      assert disk_idx != -1;

      glinear var stub := disk_writeback_sync(
          cache,
          cache_idx as nat,
          disk_idx as uint64,
          cache.data_ptr(cache_idx),
          write_back_r.value,
          unwrap_value(ticket));

      cache.status_atomic(cache_idx).release_writeback(
          unwrap_value(write_back_r), stub);
    } else {
      dispose_glnone(write_back_r);
      dispose_glnone(ticket);
    }
  }

  method evict_all(shared cache: Cache)
  requires cache.Inv()
  {
    var i: uint32 := 0;
    while i < NUM_CHUNKS_64() as uint32 {
      evict_batch(cache, i);
      evict_batch(cache, i);
      i := i + 1;
    }
  }

  // TODO could give this a stronger specification that ensures it is actually doing a sync
  // (this will probably require a state machine change)
  method flush(shared cache: Cache, inout linear local: LocalState)
  requires cache.Inv()
  requires old_local.WF()
  decreases *
  {
    io_cleanup_all(cache);

    var flush_hand: uint32 := 0;
    while flush_hand < NUM_CHUNKS_64() as uint32
    invariant local.WF()
    {
      CWB.batch_start_writeback(cache, inout local, flush_hand, true);
      flush_hand := flush_hand + 1;   
    }

    io_cleanup_all(cache);
  }

  // try to get read lock and immediately release
  // mark access bit on success
  // return true if it was in the cache
  method try_get_read_and_release(
      shared cache: Cache,
      cache_idx: uint32,
      shared localState: LocalState,
      glinear client: Client)
  returns (
    in_cache: bool,
    glinear client_out: Client
  )
  requires cache.Inv()
  requires localState.WF()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  requires client.loc == cache.counter_loc
  ensures client_out.loc == cache.counter_loc
  //requires client == RwLock.Internal(RwLock.Client(localState.t))
  decreases *
  {
    // 1. check if writelocked

    var is_exc_locked := cache.status_atomic(cache_idx).quicktest_is_exc_locked();
    if is_exc_locked {
      in_cache := false;
      client_out := client;
    } else {
      // 2. inc ref

      // TODO I'm not sure incrementing the reference count is truly necessary

      glinear var r := inc_refcount_for_shared(
          cache.read_refcount_atomic(localState.t, cache_idx),
          localState.t as nat,
          client);

      // 3. check not writelocked, not free
      //        otherwise, dec and abort

      var is_accessed: bool;
      var succ;
      succ, is_accessed, r := cache.status_atomic(cache_idx).is_exc_locked_or_free(
          localState.t as nat, r);

      if !succ {
        glinear var client' := dec_refcount_for_shared_pending(
            cache.read_refcount_atomic(localState.t, cache_idx),
            localState.t as nat,
            r);

        client_out := client';
      } else {
        // 4. if !access, then mark accessed
        if !is_accessed {
          r := cache.status_atomic(cache_idx).mark_accessed(localState.t as nat, r);
        }

        glinear var client' := dec_refcount_for_shared_pending(
            cache.read_refcount_atomic(localState.t, cache_idx),
            localState.t as nat,
            r);

        client_out := client';
      }

      in_cache := true;
    }
  }

  predicate prefetch_loop_inv(cache: Cache, pages_in_req: int, addr: int,
      slot_idx: int,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      iovec_ptr: Ptr,
      keys: seq<Key>,
      cache_readings: map<nat, CacheResources.CacheReading>,
      idxs: map<nat, CellContents<PageHandle>>,
      ros: map<nat, T.Token>,
      wps: map<nat, PointsToArray<byte>>,
      tickets: map<nat, DT.Token>)
  {
    && 0 <= slot_idx < NUM_IO_SLOTS as int
    && |cache.io_slots| == NUM_IO_SLOTS as int
    && 0 <= addr - pages_in_req < NUM_DISK_PAGES as int
    && iovec.ptr == cache.io_slots[slot_idx].iovec_ptr == iovec_ptr
    && pages_in_req == |keys| <= |iovec.s| == PAGES_PER_EXTENT as int

    && (forall i | 0 <= i < |keys| ::
        && i in wps
        && i in cache_readings
        && i in idxs
        && i in ros
        && |wps[i].s| == PageSize as int
        && simpleReadGInv(cache.io_slots, cache.data, cache.page_handles, cache.status,
            addr - pages_in_req + i, wps[i], keys[i], cache_readings[i],
            idxs[i], ros[i])

    && (forall i | 0 <= i < |keys| ::
        && 0 <= keys[i].cache_idx < |cache.data|
        && iovec.s[i].iov_base() == cache.data[keys[i].cache_idx])
        && iovec.s[i].iov_len() as int == PageSize as int
    )

    && (forall i | 0 <= i < |keys| ::
        && i in tickets
        && tickets[i].val == CacheSSM.DiskReadReq(addr - pages_in_req + i)
       )
  }

  method prefetch_io(shared cache: Cache, pages_in_req: uint64,
      addr: uint64,
      slot_idx: uint64,
      glinear iocb: Iocb,
      glinear iovec: PointsToArray<Iovec>,
      iovec_ptr: Ptr,
      ghost keys: seq<Key>,
      glinear cache_readings: map<nat, CacheResources.CacheReading>,
      glinear idxs: map<nat, CellContents<PageHandle>>,
      glinear ros: map<nat, T.Token>,
      glinear wps: map<nat, PointsToArray<byte>>,
      glinear tickets: map<nat, DT.Token>)
  requires cache.Inv()
  requires 0 < pages_in_req <= addr
  requires prefetch_loop_inv(cache, pages_in_req as int, addr as int,
            slot_idx as int, iocb, iovec, iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets)
  {
    //reveal_prefetch_loop_inv();

    glinear var iocb' := iocb;
    var iocb_ptr := lseq_peek(cache.io_slots, slot_idx).iocb_ptr;
    iocb_prepare_readv(
        iocb_ptr,
        inout iocb',
        (addr - pages_in_req) as int64,
        iovec_ptr,
        pages_in_req);

    glinear var g := ReadvG(keys, cache_readings, idxs, ros, slot_idx as int);

    forall i | 0 <= i < iocb'.iovec_len
    ensures i in tickets
    ensures i in wps
    ensures aio.readv_valid_i(iovec.s[i], wps[i], tickets[i], iocb'.offset, i)
    {
    }

    assert ReadvGInv(cache.io_slots, cache.data, cache.page_handles, cache.status,
        iocb_ptr, iocb', iovec, wps, g);

    aio.async_readv(cache.ioctx,
        iocb_ptr,
        iocb',
        iovec,
        wps,
        g,
        tickets);
  }

  method prefetch(
      shared cache: Cache,
      inout linear localState: LocalState,
      base_addr: uint64,
      glinear client: Client)
  returns (glinear client_out: Client)
  requires cache.Inv()
  requires old_localState.WF()
  requires base_addr as int % PAGES_PER_EXTENT == 0
  requires 0 <= base_addr as int < NUM_DISK_PAGES as int
  requires client.loc == cache.counter_loc
  ensures client_out.loc == cache.counter_loc
  ensures localState.WF()
  decreases *
  {
    client_out := client;

    var pages_in_req: uint64 := 0;
    var slot_idx: uint64 := 0;
    glinear var iocb_opt : glOption<Iocb> := glNone;
    glinear var iovec_opt : glOption<PointsToArray<Iovec>> := glNone;
    var iovec_ptr : Ptr := nullptr();

    ghost var keys: seq<Key> := [];
    glinear var cache_readings: map<nat, CacheResources.CacheReading> := glmap_empty();
    glinear var idxs: map<nat, CellContents<PageHandle>> := glmap_empty();
    glinear var ros: map<nat, T.Token> := glmap_empty();
    glinear var wps: map<nat, PointsToArray<byte>> := glmap_empty();
    glinear var tickets: map<nat, DT.Token> := glmap_empty();

    var page_off: uint64 := 0;
    while page_off < PAGES_PER_EXTENT_64()
    invariant 0 <= page_off as int <= PAGES_PER_EXTENT
    invariant localState.WF()
    invariant pages_in_req as int <= page_off as int
    invariant 0 <= slot_idx as int < NUM_IO_SLOTS as int
    invariant client_out.loc == cache.counter_loc
    invariant pages_in_req == 0 ==>
        && keys == []
        && cache_readings == map[]
        && idxs == map[]
        && ros == map[]
        && wps == map[]
        && tickets == map[]
    invariant pages_in_req != 0 ==>
        && iocb_opt.glSome?
        && iovec_opt.glSome?
        && iovec_opt.glSome?
        && iovec_opt.value.ptr == cache.io_slots[slot_idx as int].iovec_ptr == iovec_ptr
        && |iovec_opt.value.s| == PAGES_PER_EXTENT as int
        && prefetch_loop_inv(cache, pages_in_req as int, base_addr as int + page_off as int,
            slot_idx as int, iocb_opt.value, iovec_opt.value, iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets)
    decreases *
    {
      var addr := base_addr + page_off;

      var cache_idx := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(addr), addr as nat);

      var already_in_cache: bool;
      if cache_idx == NOT_MAPPED {
        already_in_cache := false;
      } else {
        already_in_cache, client_out := try_get_read_and_release(
            cache, cache_idx, localState, client_out);
      }

      if already_in_cache {
        // contiguous chunk of stuff to read in ends here
        // do an I/O request if we have a nonempty range
        
        if pages_in_req != 0 {
          prefetch_io(cache, pages_in_req, addr, slot_idx,
              unwrap_value(iocb_opt), unwrap_value(iovec_opt),
              iovec_ptr,
              keys, cache_readings, idxs, ros, wps, tickets);
        } else {
          dispose_anything(iocb_opt);
          dispose_anything(iovec_opt);
          dispose_anything(cache_readings);
          dispose_anything(idxs);
          dispose_anything(ros);
          dispose_anything(wps);
          dispose_anything(tickets);
        }

        pages_in_req := 0;
        page_off := page_off + 1;

        keys := [];
        cache_readings := glmap_empty();
        idxs := glmap_empty();
        ros := glmap_empty();
        wps := glmap_empty();
        tickets := glmap_empty();
        iocb_opt := glNone;
        iovec_opt := glNone;
      } else {
        // append to the current range

        // first, grab a free page:

        glinear var r, handle;
        var cache_idx;
        cache_idx, r, handle := get_free_page(cache, inout localState);

        glinear var CacheEmptyHandle(_, cache_empty, idx, wp) := handle;

        glinear var cache_empty_opt, cache_reading_opt, read_ticket_opt;
        var success;
        success, cache_empty_opt, cache_reading_opt, read_ticket_opt := 
            atomic_index_lookup_add_mapping(
              cache.cache_idx_of_page_atomic(addr),
              addr,
              cache_idx,
              cache_empty);

        if !success {
          // oops, page is already in cache
          // release the free page and just try this iteration over again
          cache.status_atomic(cache_idx).abandon_reading_pending(
            r,
            CacheEmptyHandle(
                cache.key(cache_idx as int),
                unwrap_value(cache_empty_opt),
                idx,
                wp));

          dispose_anything(read_ticket_opt);
          dispose_anything(cache_reading_opt);
        } else {
          r := cache.status_atomic(cache_idx).clear_exc_bit_during_load_phase(r);

          var p := read_cell(
            cache.page_handle_ptr(cache_idx),
            idx);
          write_cell(
            cache.page_handle_ptr(cache_idx),
            inout idx,
            PageHandle(p.data_ptr, addr as int64 * PageSize64() as int64));

          if pages_in_req == 0 {
            glinear var access;
            var sidx;
            sidx, access := get_free_io_slot(cache, inout localState);
            iovec_ptr := lseq_peek(cache.io_slots, sidx).iovec_ptr;

            slot_idx := sidx;
            glinear var IOSlotAccess(iocb, iovec) := access;
            dispose_anything(iocb_opt);
            dispose_anything(iovec_opt);
            iocb_opt := glSome(iocb);
            iovec_opt := glSome(iovec);
          }

          glinear var iovec := unwrap_value(iovec_opt);
          var iov := new_iovec(cache.data_ptr(cache_idx), 4096);
          iovec_ptr.index_write(inout iovec, pages_in_req, iov);
          iovec_opt := glSome(iovec);

          keys := keys + [cache.key(cache_idx as int)];
          cache_readings := glmap_insert(cache_readings,
              pages_in_req as int,
              unwrap_value(cache_reading_opt));
          idxs := glmap_insert(idxs,
              pages_in_req as int,
              idx);
          ros := glmap_insert(ros,
              pages_in_req as int,
              r);
          wps := glmap_insert(wps,
              pages_in_req as int,
              wp);
          tickets := glmap_insert(tickets,
              pages_in_req as int,
              CacheResources.DiskReadTicket_unfold(unwrap_value(read_ticket_opt)));

          ghost var x := pages_in_req as int + 1;
          ghost var y := base_addr as int + page_off as int + 1;
          assert prefetch_loop_inv(cache, x, y,
            slot_idx as int, iocb_opt.value, iovec_opt.value, iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets)
          by {
            /*forall i | 0 <= i < |keys|
            ensures i in wps
            ensures i in cache_readings
            ensures i in idxs
            ensures i in ros
            ensures |wps[i].s| == PageSize as int
            ensures simpleReadGInv(cache.io_slots, cache.data, cache.page_handles, cache.status,
                  y - x + i, wps[i], keys[i], cache_readings[i],
                  idxs[i], ros[i])
            {
            }*/
          }

          dispose_anything(cache_empty_opt);

          pages_in_req := pages_in_req + 1;
          page_off := page_off + 1;
        }
      }
    }

    if pages_in_req != 0 {
      var addr := base_addr + page_off;
      prefetch_io(cache, pages_in_req, addr, slot_idx,
          unwrap_value(iocb_opt), unwrap_value(iovec_opt),
          iovec_ptr,
          keys, cache_readings, idxs, ros, wps, tickets);
    } else {
      dispose_anything(iocb_opt);
      dispose_anything(iovec_opt);
      dispose_anything(cache_readings);
      dispose_anything(idxs);
      dispose_anything(ros);
      dispose_anything(wps);
      dispose_anything(tickets);
    }
  }

  method alloc(
      shared cache: Cache,
      inout linear localState: LocalState,
      disk_idx: uint64,
      gshared havoc: CacheResources.HavocPermission,
      glinear client: Client
      )
  returns (success: bool, ph: PageHandleIdx,
      glinear write_handle_out: glOption<WriteablePageHandle>,
      glinear client_out: glOption<Client>)
  requires cache.Inv()
  requires old_localState.WF()
  requires 0 <= disk_idx as int < NUM_DISK_PAGES as int
  requires havoc.disk_idx == disk_idx as nat
  requires client.loc == cache.counter_loc
  ensures localState.WF()
  ensures success ==> write_handle_out.glSome?
    && write_handle_out.value.is_disk_page_handle(cache, localState.t as int, disk_idx as int)
    && write_handle_out.value.for_page_handle(ph)
    && !write_handle_out.value.is_clean()
  ensures !success ==> client_out.glSome?
    && client_out.value.loc == cache.counter_loc
  decreases *
  {
    var cache_idx;
    glinear var r, handle;
    cache_idx, r, handle := get_free_page(cache, inout localState);

    glinear var CacheEmptyHandle(_, cache_empty, idx, data) := handle;

    glinear var cache_empty_opt, cache_entry_opt, status_opt;
    success, cache_empty_opt, cache_entry_opt, status_opt :=
        atomic_index_lookup_add_mapping_instant(
          cache.cache_idx_of_page_atomic(disk_idx),
          disk_idx,
          cache_idx,
          havoc,
          cache_empty,
          handle.data.s);

    if !success {
      write_handle_out := glNone;
      dispose_glnone(cache_entry_opt);
      dispose_glnone(status_opt);
      client_out := glSome(client);
      cache.status_atomic(cache_idx).abandon_reading_pending(
          r,
          CacheEmptyHandle(
              cache.key(cache_idx as int),
              unwrap_value(cache_empty_opt),
              idx,
              data));

      ph := PageHandleIdx(nullptr(), 0);
    } else {
      r := inc_refcount_for_reading(
          cache.read_refcount_atomic(localState.t, cache_idx),
          localState.t as nat,
          client,
          r);

      dispose_glnone(cache_empty_opt);

      var p := read_cell(
        cache.page_handle_ptr(cache_idx),
        idx);
      write_cell(
        cache.page_handle_ptr(cache_idx),
        inout idx,
        PageHandle(p.data_ptr, disk_idx as int64 * PageSize64() as int64));

      glinear var ce := CacheEntryHandle(
          cache.key(cache_idx as int), unwrap_value(cache_entry_opt), idx, data);

      r := cache.status_atomic(cache_idx).read2exc_noop(r, ce);

      write_handle_out := glSome(WriteablePageHandle(
          cache_idx as int,
          ce, unwrap_value(status_opt), r));
      client_out := glNone;

      ph := PageHandleIdx(cache.data_ptr(cache_idx), cache_idx);
    }
  }

  method try_dealloc_page(
      shared cache: Cache,
      shared localState: LocalState,
      disk_idx: uint64,
      gshared havoc: CacheResources.HavocPermission,
      glinear client: Client
    )
  returns (glinear client': Client)
  requires cache.Inv()
  requires localState.WF()
  requires 0 <= disk_idx as int < NUM_DISK_PAGES as int
  requires havoc.disk_idx == disk_idx as nat
  requires client.loc == cache.counter_loc
  ensures client'.loc == cache.counter_loc
  decreases *
  {
    client' := client;

    var done := false;
    while !done
    invariant client'.loc == cache.counter_loc
    decreases *
    {
      var cache_idx: uint32 := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(disk_idx), disk_idx as nat);

      if cache_idx == NOT_MAPPED {
        done := true;
      } else {
        var success;
        glinear var handle_opt, client_opt;
        success, handle_opt, client_opt := try_take_read_lock_on_cache_entry(
            cache, cache_idx, disk_idx as int64, localState, client');
        if !success {
          client' := unwrap_value(client_opt);
          dispose_glnone(handle_opt);
        } else {
          dispose_glnone(client_opt);
          glinear var ReadonlyPageHandle(_, so) := unwrap_value(handle_opt);
          glinear var SharedObtainedToken(t, b, token) := so;

          success, token := cache.status_atomic(cache_idx).try_set_claim(token, RwLock.SharedObtained(t, b));
          if !success {
            client' := dec_refcount_for_shared_obtained(
                  cache.read_refcount_atomic(localState.t, cache_idx),
                  localState.t as nat,
                  b, token);
          } else {
            token := cache.status_atomic(cache_idx).set_exc(token);

            glinear var status_opt: glOption<CacheResources.CacheStatus> := glNone;
            var writeback_done := false;
            ghost var token_copy := token;
            ghost var rwlock_loc := cache.status_atomic(cache_idx).rwlock_loc;
            ghost var clean;
            while !writeback_done
            invariant !writeback_done ==> status_opt == glNone
            invariant !writeback_done ==> token == token_copy;
            invariant writeback_done ==>
              && token.val == RwLock.ExcHandle(RwLock.ExcPending(t, 0, clean, token_copy.val.exc.b))
              && token.loc == rwlock_loc
              && status_opt.glSome?
              && status_opt.value.cache_idx == cache_idx as int
              && status_opt.value.status == (if clean then Clean else Dirty)
            decreases *
            {
              dispose_glnone(status_opt);
              writeback_done, clean, token, status_opt :=
                  cache.status_atomic(cache_idx).try_check_writeback_isnt_set(t, token);
              if !writeback_done {
                io_cleanup(cache, DEFAULT_MAX_IO_EVENTS_64());
              }
            }

            token := check_all_refcounts_with_t_block(cache, localState.t, cache_idx, token);

            glinear var handle;
            token, handle := perform_Withdraw_TakeExcLockFinish(token);

            glinear var CacheEntryHandle(key, cache_entry, data, idx) := handle;

            glinear var cache_empty := atomic_index_lookup_clear_mapping_havoc(
                  cache.cache_idx_of_page_atomic(disk_idx as uint64),
                  disk_idx as nat,
                  havoc,
                  cache_entry,
                  unwrap_value(status_opt));

            glinear var empty_handle := CacheEmptyHandle(key, cache_empty, data, idx);

            token := cache.status_atomic(cache_idx).set_to_free2(empty_handle, token);

            client' := dec_refcount_for_shared_pending(
                  cache.read_refcount_atomic(localState.t, cache_idx),
                  localState.t as nat,
                  token);

            done := true;
          }
        }
      }
    }
  }

  method wait(shared cache: Cache)
  requires cache.Inv()
  {
    io_cleanup(cache, DEFAULT_MAX_IO_EVENTS_64());
  }
}
