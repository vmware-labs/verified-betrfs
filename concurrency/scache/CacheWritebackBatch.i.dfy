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
  import opened GlinearSeq
  import DT = DiskSSMTokens(CacheIfc, CacheSSM)

  predicate ktw(cache: Cache, disk_idx: nat, key: Key, ticket: DT.Token,
      wbo: WritebackObtainedToken)
  {
    && 0 <= key.cache_idx < CACHE_SIZE as nat
    && |cache.data| == CACHE_SIZE as nat
    && |cache.disk_idx_of_entry| == CACHE_SIZE as nat
    && key == cache.key(key.cache_idx)
    && wbo.is_handle(key)
    && wbo.b.idx.v as nat == disk_idx
    && ticket.val == CacheSSM.DiskWriteReq(disk_idx, wbo.b.data.s)
  }

  predicate {:opaque} fwd_lists(cache: Cache, start: nat, end: nat,
      keys: seq<Key>,
      tickets: glseq<DT.Token>,
      wbos: glseq<WritebackObtainedToken>)
  {
    && |keys| == tickets.len() == wbos.len() == end - start
    && forall i | 0 <= i < |keys| ::
        && tickets.has(i)
        && wbos.has(i)
        && ktw(cache, start + i, keys[i], tickets.get(i), wbos.get(i))
  }

  glinear method make_empty(ghost cache: Cache, ghost disk_addr: nat)
  returns (
      ghost keys: seq<Key>,
      glinear tickets: glseq<DT.Token>,
      glinear wbos: glseq<WritebackObtainedToken>
     )
  ensures fwd_lists(cache, disk_addr, disk_addr, keys, tickets, wbos)

  glinear method list_push_back(
      ghost cache: Cache,
      ghost start: nat,
      ghost end: nat,
      ghost keys: seq<Key>,
      glinear tickets: glseq<DT.Token>,
      glinear wbos: glseq<WritebackObtainedToken>,
      ghost key: Key,
      glinear ticket: DT.Token,
      glinear wbo: WritebackObtainedToken)
  returns (
      ghost keys': seq<Key>,
      glinear tickets': glseq<DT.Token>,
      glinear wbos': glseq<WritebackObtainedToken>
     )
  requires fwd_lists(cache, start, end, keys, tickets, wbos)
  requires ktw(cache, end, key, ticket, wbo)
  ensures fwd_lists(cache, start, end + 1, keys', tickets', wbos')

  glinear method list_push_front(
      ghost cache: Cache,
      ghost start: nat,
      ghost end: nat,
      ghost keys: seq<Key>,
      glinear tickets: glseq<DT.Token>,
      glinear wbos: glseq<WritebackObtainedToken>,
      ghost key: Key,
      glinear ticket: DT.Token,
      glinear wbo: WritebackObtainedToken)
  returns (
      ghost keys': seq<Key>,
      glinear tickets': glseq<DT.Token>,
      glinear wbos': glseq<WritebackObtainedToken>
     )
  requires fwd_lists(cache, start, end, keys, tickets, wbos)
  requires ktw(cache, start - 1, key, ticket, wbo)
  ensures fwd_lists(cache, start - 1, end, keys', tickets', wbos')


  predicate method pages_share_extent(a: uint64, b: uint64)
  {
    a / PAGES_PER_EXTENT == b / PAGES_PER_EXTENT
  }

  method walk_forward(shared cache: Cache, inout linear local: LocalState,
        disk_addr: uint64, is_urgent: bool)
  returns (end_addr: uint64,
      ghost keys: seq<Key>,
      glinear tickets: glseq<DT.Token>,
      glinear wbos: glseq<WritebackObtainedToken>
     )
  decreases *
  requires cache.Inv()
  requires old_local.WF()
  requires 0 <= disk_addr < NUM_DISK_PAGES
  ensures 0 <= disk_addr < end_addr <= NUM_DISK_PAGES
  ensures fwd_lists(cache, disk_addr as nat + 1, end_addr as nat, keys, tickets, wbos)
  ensures local.WF()
  {
    end_addr := disk_addr + 1;
    var done := false;

    keys, tickets, wbos := make_empty(cache, disk_addr as nat + 1);

    while end_addr < NUM_DISK_PAGES && !done
    invariant disk_addr < end_addr <= NUM_DISK_PAGES
    invariant fwd_lists(cache, disk_addr as nat + 1, end_addr as nat, keys, tickets, wbos)
    invariant local.WF()
    decreases NUM_DISK_PAGES as int - end_addr as int,
        if !done then 1 else 0
    {
      var next := end_addr;
      if !pages_share_extent(next, disk_addr) {
        done := true;
      } else {
        var cache_idx := atomic_index_lookup_read(
            cache.cache_idx_of_page_atomic(next), next as nat);
        if cache_idx == NOT_MAPPED {
          done := true;
        } else {
          glinear var write_back_r, ticket;
          var do_write_back;
          do_write_back, write_back_r, ticket :=
              cache.status_atomic(cache_idx as uint64).try_acquire_writeback(is_urgent);

          if !do_write_back {
            dispose_anything(write_back_r);
            dispose_anything(ticket);
            done := true;
          } else {
            var disk_idx := read_cell(
                cache.disk_idx_of_entry_ptr(cache_idx as uint64),
                T.borrow_wb(write_back_r.value.token).idx);

            if disk_idx == next as int64 {
              keys, tickets, wbos := list_push_back(
                  cache, disk_addr as nat + 1, end_addr as nat,
                  keys, tickets, wbos,
                  cache.key(cache_idx as nat),
                  CacheResources.DiskWriteTicket_unfold(unwrap_value(ticket)),
                  unwrap_value(write_back_r));

              end_addr := next + 1;
            } else {
              // Presumably rare case.
              // Oops, this isn't the disk address we thought it was going to be!
              // Write this one on its own and stop trying to extend the page range.
              disk_writeback_async(
                  cache, inout local,
                  disk_idx as uint64,
                  cache_idx as uint64,
                  unwrap_value(write_back_r),
                  unwrap_value(ticket));
              
              done := true;
            }
          }
        }
      }
    }
  }

  method walk_backward(shared cache: Cache, inout linear local: LocalState,
        disk_addr: uint64, is_urgent: bool)
  returns (start_addr: uint64,
      ghost keys: seq<Key>,
      glinear tickets: glseq<DT.Token>,
      glinear wbos: glseq<WritebackObtainedToken>
     )
  decreases *
  requires cache.Inv()
  requires old_local.WF()
  requires 0 <= disk_addr < NUM_DISK_PAGES
  ensures 0 <= start_addr <= disk_addr
  ensures fwd_lists(cache, start_addr as nat, disk_addr as nat, keys, tickets, wbos)
  ensures local.WF()
  {
    start_addr := disk_addr;
    var done := false;

    keys, tickets, wbos := make_empty(cache, disk_addr as nat);

    while start_addr > 0 && !done
    invariant 0 <= start_addr <= disk_addr
    invariant fwd_lists(cache, start_addr as nat, disk_addr as nat, keys, tickets, wbos)
    invariant local.WF()
    decreases start_addr, if !done then 1 else 0
    {
      var next := start_addr - 1;
      if !pages_share_extent(next, disk_addr) {
        done := true;
      } else {
        var cache_idx := atomic_index_lookup_read(
            cache.cache_idx_of_page_atomic(next), next as nat);
        if cache_idx == NOT_MAPPED {
          done := true;
        } else {
          glinear var write_back_r, ticket;
          var do_write_back;
          do_write_back, write_back_r, ticket :=
              cache.status_atomic(cache_idx as uint64).try_acquire_writeback(is_urgent);

          if !do_write_back {
            dispose_anything(write_back_r);
            dispose_anything(ticket);
            done := true;
          } else {
            var disk_idx := read_cell(
                cache.disk_idx_of_entry_ptr(cache_idx as uint64),
                T.borrow_wb(write_back_r.value.token).idx);

            if disk_idx == next as int64 {
              keys, tickets, wbos := list_push_front(
                  cache, start_addr as nat, disk_addr as nat,
                  keys, tickets, wbos,
                  cache.key(cache_idx as nat),
                  CacheResources.DiskWriteTicket_unfold(unwrap_value(ticket)),
                  unwrap_value(write_back_r));

              start_addr := next;
            } else {
              // Presumably rare case.
              // Oops, this isn't the disk address we thought it was going to be!
              // Write this one on its own and stop trying to extend the page range.
              disk_writeback_async(
                  cache, inout local,
                  disk_idx as uint64,
                  cache_idx as uint64,
                  unwrap_value(write_back_r),
                  unwrap_value(ticket));
              
              done := true;
            }
          }
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
      glinear var write_back_r, ticket;
      var do_write_back;
      do_write_back, write_back_r, ticket :=
          cache.status_atomic(cache_idx as uint64).try_acquire_writeback(is_urgent);

      if do_write_back {
        var disk_idx := read_cell(
            cache.disk_idx_of_entry_ptr(cache_idx as uint64),
            T.borrow_wb(write_back_r.value.token).idx);
        assert disk_idx != -1;

        var start_addr, end_addr;
        ghost keys1, keys2;
        glinear var tickets1, tickets2;
        glinear var wbos1, wbos2;
        start_addr, key1, tickets1, wbos1 :=
            walk_backward(cache, inout local, disk_idx, is_urgent);
        end_addr, keys2, tickets2, wbos2 :=
            walk_forward(cache, inout local, disk_idx, is_urgent);

        keys1, tickets1, wbos1 := list_push_front(
            cache, start_addr as nat, disk_idx as nat,
            keys1, tickets1, wbos1,
            cache.key(cache_idx),
            unwrap_value(ticket),
            unwrap_value(write_back_r));

        keys1, tickets1, wbos1 := list_concat(
            cache,
            start_addr as nat, disk_idx as nat + 1, end_addr as nat,
            keys1, tickets1, wbos1,
            keys2, tickets2, wbos2);


      } else {
        dispose_glnone(write_back_r);
        dispose_glnone(ticket);
      }

      i := i + 1;
    }
  }
}
