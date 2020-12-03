include "ResourceSpec.s.dfy"
include "../../lib/Base/Multisets.i.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

module CacheResources refines ResourceSpec {
  import opened Options
  import opened NativeTypes

  datatype Status = Empty | Reading | Clean | Dirty | WriteBack

  datatype R =
    | DiskPageMap(disk_idx: int, cache_idx_opt: Option<int>)
    | CacheEntry(disk_idx_opt: Option<int>,
        cache_idx: int, data: seq<byte>)

    | CacheStatus(cache_idx: int, status: Status)

    | DiskReadTicket(addr: uint64)
    | DiskReadStub(addr: uint64, contents: seq<byte>)

  method initiate_page_in(
      cache_idx: int,
      disk_idx: uint64,
      linear s1: R,
      linear s2: R,
      linear s3: R
  )
  returns (
      linear t1: R,
      linear t2: R,
      linear t3: R,
      linear t4: R
  )
  requires s1 == CacheStatus(cache_idx, Empty)
  requires s2.CacheEntry? && s2.cache_idx == cache_idx
      && s2.disk_idx_opt == None
  requires s3 == DiskPageMap(disk_idx as int, None)
  ensures t1 == CacheStatus(cache_idx, Reading)
  ensures t2 == s2.(disk_idx_opt := Some(disk_idx as int))
  ensures t3 == DiskPageMap(disk_idx as int, Some(cache_idx))
  ensures t4 == DiskReadTicket(disk_idx)

  method finish_page_in(
      cache_idx: int,
      disk_idx: uint64,
      linear s1: R,
      linear s2: R,
      linear s3: R
  )
  returns (
      linear t1: R,
      linear t2: R
  )
  requires s1 == CacheStatus(cache_idx, Reading)
  requires s2.CacheEntry? && s2.disk_idx_opt == Some(disk_idx as int)
      && s2.cache_idx == cache_idx
  requires s3.DiskReadStub? && s3.addr == disk_idx
  ensures t1 == CacheStatus(cache_idx, Clean)
  ensures t2 == s2.(data := s3.contents)
}
