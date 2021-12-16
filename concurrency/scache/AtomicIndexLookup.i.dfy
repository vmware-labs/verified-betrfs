include "../framework/Atomic.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../framework/GlinearOption.s.dfy"
include "cache/CacheResources.i.dfy"
include "Constants.i.dfy"
include "../framework/Ptrs.s.dfy"

module AtomicIndexLookupImpl {
  import opened NativeTypes
  import opened Ptrs
  import opened Atomics
  import opened Constants
  import opened CacheResources
  import opened Options
  import opened GlinearOption
  import opened CacheStatusType

  type AtomicIndexLookup = Atomic<uint32, CacheResources.DiskPageMap>

  const NOT_MAPPED : uint64 := 0xffff_ffff;

  predicate state_inv(v: uint32, g: CacheResources.DiskPageMap, disk_idx: nat)
  {
    && (0 <= v as int < CACHE_SIZE as int || v == 0xffff_ffff)
    && g == CacheResources.DiskPageMap(disk_idx,
        (if v == 0xffff_ffff then None else Some(v as nat)))
  }

  predicate atomic_index_lookup_inv(a: AtomicIndexLookup, disk_idx: nat)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, disk_idx)
  }

  method read_known_cache_idx(
      shared a: AtomicIndexLookup,
      ghost disk_idx: nat,
      gshared cache_entry: CacheEntry)
  returns (cache_idx: uint64)
  requires atomic_index_lookup_inv(a, disk_idx)
  requires cache_entry.disk_idx == disk_idx
  ensures cache_idx as int == cache_entry.cache_idx
  {
    atomic_block var ci := execute_atomic_load(a) {
      ghost_acquire g;
      inv_map_agrees(cache_entry, inout g);
      ghost_release g;
    }
    cache_idx := ci as uint64;
  }

  method atomic_index_lookup_read(
      shared a: AtomicIndexLookup,
      ghost disk_idx: nat)
  returns (cache_idx: uint64)
  requires atomic_index_lookup_inv(a, disk_idx)
  ensures 0 <= cache_idx as int < CACHE_SIZE as int || cache_idx == NOT_MAPPED
  {
    atomic_block var ci := execute_atomic_load(a) { }
    cache_idx := ci as uint64;
  }

  method atomic_index_lookup_clear_mapping(
      shared a: AtomicIndexLookup,
      ghost disk_idx: nat,
      glinear cache_entry: CacheResources.CacheEntry,
      glinear status: CacheResources.CacheStatus
  )
  returns (
      glinear cache_empty': CacheResources.CacheEmpty
  )
  requires atomic_index_lookup_inv(a, disk_idx)
  requires status.CacheStatus?
  requires status.status == Clean
  requires cache_entry.CacheEntry?
  requires cache_entry.cache_idx == status.cache_idx
  requires cache_entry.disk_idx == disk_idx
  ensures cache_empty' == CacheEmpty(cache_entry.cache_idx)
  {
    atomic_block var _ := execute_atomic_store(a, NOT_MAPPED as uint32) {
      ghost_acquire g;

      cache_empty', g := CacheResources.unassign_page(
          status.cache_idx, disk_idx,
          status, cache_entry, g);

      ghost_release g;
    }
  }

  method atomic_index_lookup_clear_mapping_havoc(
      shared a: AtomicIndexLookup,
      ghost disk_idx: nat,
      gshared havoc: HavocPermission,
      glinear cache_entry: CacheResources.CacheEntry,
      glinear status: CacheResources.CacheStatus
  )
  returns (
      glinear cache_empty': CacheResources.CacheEmpty
  )
  requires atomic_index_lookup_inv(a, disk_idx)
  requires status.CacheStatus?
  requires cache_entry.CacheEntry?
  requires cache_entry.cache_idx == status.cache_idx
  requires status.status != Writeback
  requires cache_entry.disk_idx == disk_idx
  requires havoc.disk_idx == disk_idx as int
  ensures cache_empty' == CacheEmpty(cache_entry.cache_idx)
  {
    atomic_block var _ := execute_atomic_store(a, NOT_MAPPED as uint32) {
      ghost_acquire g;

      cache_empty', g := CacheResources.unassign_page_havoc(
          status.cache_idx, disk_idx,
          status, cache_entry, g, havoc);

      ghost_release g;
    }
  }

  method atomic_index_lookup_add_mapping(
      shared a: AtomicIndexLookup,
      disk_idx: uint64,
      cache_idx: uint64,
      glinear cache_empty: CacheResources.CacheEmpty)
  returns (
    success: bool,
    glinear cache_empty': glOption<CacheResources.CacheEmpty>,
    glinear cache_reading': glOption<CacheResources.CacheReading>,
    glinear read_ticket: glOption<CacheResources.DiskReadTicket>
  )
  requires atomic_index_lookup_inv(a, disk_idx as int)
  requires cache_empty.cache_idx == cache_idx as int
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  ensures !success ==> cache_empty' == glSome(cache_empty)
  ensures !success ==> cache_reading' == glNone
  ensures !success ==> read_ticket == glNone

  ensures success ==> cache_empty' == glNone
  ensures success ==> cache_reading' ==
    glSome(CacheReading(cache_idx as nat, disk_idx as nat))
  ensures success ==>
      && read_ticket == glSome(DiskReadTicket(disk_idx as int))
  {
    atomic_block var did_set :=
      execute_atomic_compare_and_set_strong(a, NOT_MAPPED as uint32, cache_idx as uint32)
    {
      ghost_acquire old_g;
      glinear var new_g;

      if did_set {
        glinear var ticket, cr;
        cr, new_g, ticket := CacheResources.initiate_page_in(
            cache_idx as int, disk_idx as int, cache_empty, old_g);
        read_ticket := glSome(ticket);
        cache_reading' := glSome(cr);
        cache_empty' := glNone;
      } else {
        cache_empty' := glSome(cache_empty);
        cache_reading' := glNone;
        read_ticket := glNone;
        new_g := old_g;
      }
      assert state_inv(new_value, new_g, disk_idx as int);

      ghost_release new_g;
    }

    success := did_set;
  }

  method atomic_index_lookup_add_mapping_instant(
      shared a: AtomicIndexLookup,
      disk_idx: uint64,
      cache_idx: uint64,
      gshared havoc: HavocPermission,
      glinear cache_empty: CacheResources.CacheEmpty,
      ghost data: DiskIfc.Block)
  returns (
    success: bool,
    glinear cache_empty': glOption<CacheResources.CacheEmpty>,
    glinear cache_entry': glOption<CacheResources.CacheEntry>,
    glinear status': glOption<CacheResources.CacheStatus>
  )
  requires atomic_index_lookup_inv(a, disk_idx as int)
  requires cache_empty.cache_idx == cache_idx as int
  requires 0 <= cache_idx as int < CACHE_SIZE as int
  requires havoc.disk_idx == disk_idx as int
  ensures !success ==> cache_empty' == glSome(cache_empty)
  ensures !success ==> cache_entry' == glNone
  ensures !success ==> status' == glNone

  ensures success ==> cache_empty' == glNone
  ensures success ==> cache_entry' ==
      glSome(CacheEntry(cache_idx as nat, disk_idx as nat, data))
  ensures success ==> status' == glSome(CacheStatus(cache_idx as nat, Dirty))
  {
    atomic_block var did_set :=
      execute_atomic_compare_and_set_strong(a, NOT_MAPPED as uint32, cache_idx as uint32)
    {
      ghost_acquire old_g;
      glinear var new_g;

      if did_set {
        glinear var cr, status;
        cr, new_g, status := CacheResources.havoc_page_in(
            cache_idx as int, disk_idx as int, cache_empty, old_g, havoc, data);
        cache_entry' := glSome(cr);
        cache_empty' := glNone;
        status' := glSome(status);
      } else {
        cache_empty' := glSome(cache_empty);
        cache_entry' := glNone;
        status' := glNone;
        new_g := old_g;
      }
      assert state_inv(new_value, new_g, disk_idx as int);

      ghost_release new_g;
    }

    success := did_set;
  }

}
