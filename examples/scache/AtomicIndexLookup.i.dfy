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

  method atomic_index_lookup_read(
      a: AtomicIndexLookup,
      disk_idx: int)
  returns (cache_idx: uint64)
  requires atomic_index_lookup_inv(a, disk_idx)
  ensures 0 <= cache_idx as int < CACHE_SIZE || cache_idx == NOT_MAPPED

  method atomic_index_lookup_add_mapping(
      a: AtomicIndexLookup,
      disk_idx: int,
      cache_idx: int,
      linear m: CacheResources.R)
  returns (
    success: bool,
    linear m': CacheResources.R
  )
  requires m.CacheEntry?
  requires m.disk_idx_opt == None
  requires m.cache_idx == cache_idx
  ensures !success ==> m' == m
  ensures success ==> m' == m.(disk_idx_opt := Some(disk_idx))

}
