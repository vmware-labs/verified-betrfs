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
    | CacheEntry(
        // this field is meaningless if status == Empty
        disk_idx: int,
        cache_idx: int, data: seq<byte>)

    | CacheStatus(cache_idx: int, status: Status)

    | DiskReadTicket(addr: uint64)
    | DiskReadStub(addr: uint64, contents: seq<byte>)

    | DiskWriteTicket(addr: uint64, contents: seq<byte>)
    | DiskWriteStub(addr: uint64)

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
  requires s3 == DiskPageMap(disk_idx as int, None)
  ensures t1 == CacheStatus(cache_idx, Reading)
  ensures t2 == s2.(disk_idx := disk_idx as int)
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
  requires s2.CacheEntry? && s2.disk_idx == disk_idx as int
      && s2.cache_idx == cache_idx
  requires s3.DiskReadStub? && s3.addr == disk_idx
  ensures t1 == CacheStatus(cache_idx, Clean)
  ensures t2 == s2.(data := s3.contents)

  method initiate_writeback(
      shared cache_entry: R,
      linear status: R
  )
  returns (
      linear status': R,
      linear ticket: R
  )
  requires cache_entry.CacheEntry?
  requires status == CacheStatus(cache_entry.cache_idx, Dirty)
  ensures status' == CacheStatus(cache_entry.cache_idx, WriteBack)
  ensures 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  ensures ticket == DiskWriteTicket(
      cache_entry.disk_idx as uint64,
      cache_entry.data)

  method finish_writeback(
      shared cache_entry: R,
      linear status: R,
      linear stub: R
  )
  returns (
      linear status': R
  )
  requires cache_entry.CacheEntry?
  requires status == CacheStatus(cache_entry.cache_idx, WriteBack)
  requires 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  requires stub == DiskWriteStub(cache_entry.disk_idx as uint64)
  ensures status' == CacheStatus(cache_entry.cache_idx, Clean)
}
