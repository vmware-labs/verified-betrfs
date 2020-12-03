include "Atomic.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Lang/LinearMaybe.s.dfy"
include "CacheResources.i.dfy"
include "Constants.i.dfy"
include "ArrayPtr.s.dfy"

module AtomicIndexLookupImpl {
  import opened NativeTypes
  import opened Ptrs
  import opened AtomicSpec
  import opened LinearMaybe
  import opened Constants
  import opened CacheResources
  import opened Options

  type AtomicIndexLookup = Atomic<uint64, CacheResources.R>

  const NOT_MAPPED : uint64 := 0xffff_ffff_ffff_ffff;

  predicate state_inv(v: uint64, g: CacheResources.R, disk_idx: int)
  {
    && (0 <= v as int < CACHE_SIZE || v == NOT_MAPPED)
    && g == CacheResources.DiskPageMap(disk_idx,
        (if v == NOT_MAPPED then None else Some(v as int)))
  }

  predicate atomic_index_lookup_inv(a: AtomicIndexLookup, disk_idx: int)
  {
    forall v, g :: atomic_inv(a, v, g) <==> state_inv(v, g, disk_idx)
  }

  method unsafe_obtain<Q>() returns (linear r: Q)
  method unsafe_dispose<Q>(linear r: Q)

  method atomic_index_lookup_read(
      a: AtomicIndexLookup,
      disk_idx: int)
  returns (cache_idx: uint64)
  requires atomic_index_lookup_inv(a, disk_idx)
  ensures 0 <= cache_idx as int < CACHE_SIZE || cache_idx == NOT_MAPPED

  method atomic_index_lookup_add_mapping(
      a: AtomicIndexLookup,
      disk_idx: uint64,
      cache_idx: uint64,
      linear cache_entry: CacheResources.R,
      linear status: CacheResources.R)
  returns (
    success: bool,
    linear cache_entry': CacheResources.R,
    linear status': CacheResources.R,
    linear read_ticket: maybe<CacheResources.R>
  )
  requires atomic_index_lookup_inv(a, disk_idx as int)
  requires cache_entry.CacheEntry?
  requires cache_entry.cache_idx == cache_idx as int
  requires status == CacheStatus(cache_idx as int, Empty)
  requires 0 <= cache_idx as int < CACHE_SIZE
  ensures !success ==> cache_entry' == cache_entry
  ensures success ==> cache_entry' ==
      cache_entry.(disk_idx := disk_idx as int)
  ensures !success ==> status' == status
  ensures success ==> status' == CacheStatus(cache_idx as int, Reading)
  ensures success ==> has(read_ticket)
      && read(read_ticket) == DiskReadTicket(disk_idx)
  ensures !success ==> !has(read_ticket)
  {
    var did_set := compare_and_set(a, NOT_MAPPED, cache_idx);

    ///// Begin jank
    ///// Setup:
    var v1 := NOT_MAPPED;
    var v2 := cache_idx;
    var old_v: uint64;
    var new_v: uint64;
    linear var old_g: CacheResources.R := unsafe_obtain();
    assume old_v == v1 ==> new_v == v2 && did_set;
    assume old_v != v1 ==> new_v == old_v && !did_set;
    assume atomic_inv(a, old_v, old_g);
    linear var new_g;
    ///// Transfer:
    if did_set {
      linear var ticket;
      status', cache_entry', new_g, ticket :=
        initiate_page_in(cache_idx as int, disk_idx, status, cache_entry, old_g);
      read_ticket := give(ticket);
    } else {
      cache_entry' := cache_entry;
      status' := status;
      read_ticket := empty();
      new_g := old_g;
    }
    assert state_inv(new_v, new_g, disk_idx as int);
    ///// Teardown:
    assert atomic_inv(a, new_v, new_g);
    unsafe_dispose(new_g);
    ///// End jank

    success := did_set;
  }
}
