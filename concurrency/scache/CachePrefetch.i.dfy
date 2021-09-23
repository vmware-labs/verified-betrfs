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

  // try to get read lock and immediately release
  // mark access bit on success
  // return true if it was in the cache
  method try_get_read_and_release(
      shared cache: Cache,
      cache_idx: uint64,
      shared localState: LocalState,
      glinear client: Client)
  returns (
    in_cache: bool,
    glinear client_out: Client
  )
  requires cache.Inv()
  requires localState.WF()
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  //requires client == RwLock.Internal(RwLock.Client(localState.t))
  decreases *
  {
    // 1. check if writelocked

    var is_exc_locked := cache.status_atomic(cache_idx).quicktest_is_exc_locked();
    if is_exc_locked {
      success := false;
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

      success := true;
    }
  }

  method prefetch(
      shared cache: Cache,
      inout linear localState: LocalState,
      base_addr: uint64,
      glinear client: Client)
  returns (client_out: Client)
  requires cache.Inv()
  requires old_localState.WF()
  requires base_addr % PAGES_PER_EXTENT == 0
  requires 0 <= base_addr as int < NUM_DISK_PAGES as int
  ensures localState.WF()
  decreases *
  {
    client_out := client;

    var pages_in_req: uint64 := 0;

    var page_off: uint64 := 0;
    while page_off < PAGES_PER_EXTENT
    invariant pages_in_req as int <= page_off as int
    {
      var addr := base_addr + page_off;

      var cache_idx := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(disk_idx), disk_idx as nat);

      var already_in_cache := try_get_and_release(
          cache, cache_idx, addr as int64, localState, client_out);

      if already_in_cache {
        // contiguous chunk of stuff to read in ends here
        // do an I/O request if we have a nonempty range
      } else {
        // append to the current range
      }
    }
  }
