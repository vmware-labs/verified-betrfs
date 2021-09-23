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
  import opened IocbStruct
  import opened GlinearMap
  import DT = DiskSSMTokens(CacheIfc, CacheSSM)
  import opened CacheAIOParams

  method get_free_page(shared cache: Cache, linear inout localState: LocalState)
  returns (
    cache_idx: uint64,
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

  predicate prefetch_loop_inv(cache: Cache, pages_in_req: int,
      slot_Idx: int,
      iocb: Iocb,
      iovec: PointsToArray<Iovec>,
      iovec_ptr: Ptr,
      keys: seq<Key>,
      cache_readings: map<nat, CacheResources.CacheReading>,
      idxs: map<nat, CellContents<int64>>,
      ros: map<nat, T.Token>,
      wps: map<nat, PointsToArray<byte>>,
      tickets: map<nat, DT.Token>)
  {
    true
  }

  method prefetch_io(shared cache: Cache, pages_in_req: uint64,
      addr: uint64,
      slot_idx: uint64,
      glinear iocb: Iocb,
      glinear iovec: PointsToArray<Iovec>,
      iovec_ptr: Ptr,
      ghost keys: seq<Key>,
      glinear cache_readings: map<nat, CacheResources.CacheReading>,
      glinear idxs: map<nat, CellContents<int64>>,
      glinear ros: map<nat, T.Token>,
      glinear wps: map<nat, PointsToArray<byte>>,
      glinear tickets: map<nat, DT.Token>)
  requires cache.Inv()
  requires pages_in_req < addr
  requires prefetch_loop_inv(cache, pages_in_req as int,
            slot_idx as int, iocb, iovec, iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets)
  {
    glinear var iocb' := iocb;
    var iocb_ptr := lseq_peek(cache.io_slots, slot_idx).iocb_ptr;
    iocb_prepare_writev(
        iocb_ptr,
        inout iocb',
        (addr - pages_in_req) as int64,
        iovec_ptr,
        pages_in_req);

    glinear var g := ReadvG(keys, cache_readings, idxs, ros, slot_idx as int);

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
  requires base_addr % PAGES_PER_EXTENT == 0
  requires 0 <= base_addr as int < NUM_DISK_PAGES as int
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
    glinear var idxs: map<nat, CellContents<int64>> := glmap_empty();
    glinear var ros: map<nat, T.Token> := glmap_empty();
    glinear var wps: map<nat, PointsToArray<byte>> := glmap_empty();
    glinear var tickets: map<nat, DT.Token> := glmap_empty();

    var page_off: uint64 := 0;
    while page_off < PAGES_PER_EXTENT
    invariant pages_in_req as int <= page_off as int
    invariant pages_in_req != 0 ==>
        && iocb_opt.glSome?
        && iovec_opt.glSome?
        && iovec_opt.glSome?
        && prefetch_loop_inv(cache, pages_in_req as int,
            slot_idx as int, iocb_opt.value, iovec_opt.value, iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets)
    decreases *
    {
      var addr := base_addr + page_off;

      var cache_idx := atomic_index_lookup_read(
          cache.cache_idx_of_page_atomic(addr), addr as nat);

      var already_in_cache;
      already_in_cache, client_out := try_get_read_and_release(
          cache, cache_idx, localState, client_out);

      if already_in_cache {
        // contiguous chunk of stuff to read in ends here
        // do an I/O request if we have a nonempty range
        
        prefetch_io(cache, pages_in_req, addr, slot_idx,
            unwrap_value(iocb_opt), unwrap_value(iovec_opt),
            iovec_ptr,
            keys, cache_readings, idxs, ros, wps, tickets);

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
          write_cell(
            cache.disk_idx_of_entry_ptr(cache_idx),
            inout idx,
            addr as int64);

          if pages_in_req == 0 {
            glinear var access;
            var sidx;
            sidx, access := get_free_io_slot(cache, inout localState);
            iovec_ptr := lseq_peek(cache.io_slots, sidx).iocb_ptr;

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
}
