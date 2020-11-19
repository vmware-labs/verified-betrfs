include "ResourceSpec.s.dfy"
include "../../lib/Base/Multisets.i.dfy"
include "../../lib/Base/Option.s.dfy"

module CacheResource refines ResourceSpec {
  import opened Options

  datatype R =
    | DiskPageMap(disk_idx: int, cache_idx: Option<int>)
    | CacheEntry(disk_idx: Option<int>, cache_idx: int, data: seq<byte>)
}
