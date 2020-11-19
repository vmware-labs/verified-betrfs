include "ResourceSpec.s.dfy"
include "../../lib/Base/Multisets.i.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

module CacheResources refines ResourceSpec {
  import opened Options
  import opened NativeTypes

  datatype R =
    | DiskPageMap(disk_idx: int, cache_idx_opt: Option<int>)
    | CacheEntry(disk_idx_opt: Option<int>, cache_idx: int, data: seq<byte>)
}
