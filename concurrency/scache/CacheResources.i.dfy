include "../../lib/Base/Option.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../framework/PCM.s.dfy"

module CacheResources {
  import opened Options
  import opened NativeTypes
  import opened GhostLoc

  datatype Status = Empty | Reading | Clean | Dirty | Writeback

  datatype M = M(
    statuses: map<int, Status>
  )

  type Token
  {
    function get() : M
    function loc() : Loc
  }

  function unit() : M

  function DiskPageMap(disk_idx: int, cache_idx_opt: Option<int>) : M

  /*function CacheEntry(
        // this field is meaningless if status == Empty
        disk_idx: int,
        cache_idx: int, data: seq<byte>) : M*/

  datatype CacheStatus = CacheStatus(ghost cache_idx: int, ghost status: Status)
  {
    predicate is_status(cache_idx: int, status: Status) {
      this.cache_idx == cache_idx && this.status == status
    }
  }

  glinear datatype CacheEntry = CacheEntry(
      ghost loc: Loc,
      ghost disk_idx: int, ghost cache_idx: int, ghost data: seq<byte>)

  datatype DiskWriteTicket = DiskWriteTicket(ghost addr: uint64, ghost contents: seq<byte>)
  {
    predicate writes(addr: uint64, contents: seq<byte>) {
      this.addr == addr && this.contents == contents
    }
  }

    /*| DiskReadTicket(addr: uint64)
    | DiskReadStub(addr: uint64, contents: seq<byte>)

    | DiskWriteTicket(addr: uint64, contents: seq<byte>)
    | DiskWriteStub(addr: uint64)*/

  /*method initiate_page_in(
      cache_idx: int,
      disk_idx: uint64,
      glinear s1: R,
      glinear s2: R,
      glinear s3: R
  )
  returns (
      glinear t1: R,
      glinear t2: R,
      glinear t3: R,
      glinear t4: DiskReadTicket
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
      glinear s1: R,
      glinear s2: R,
      glinear s3: DiskReadStub
  )
  returns (
      glinear t1: R,
      glinear t2: R
  )
  requires s1 == CacheStatus(cache_idx, Reading)
  requires s2.CacheEntry? && s2.disk_idx == disk_idx as int
      && s2.cache_idx == cache_idx
  requires s3.addr == disk_idx
  ensures t1 == CacheStatus(cache_idx, Clean)
  ensures t2 == s2.(data := s3.contents)
  */

  method initiate_writeback(
      gshared cache_entry: CacheEntry,
      glinear status: CacheStatus
  )
  returns (
      glinear status': CacheEntry,
      glinear ticket: DiskWriteTicket
  )
  requires status.cache_idx == cache_entry.cache_idx
  requires status.status == Dirty
  ensures status.cache_idx == cache_entry.cache_idx
  ensures status.status == Writeback
  ensures 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  ensures ticket == DiskWriteTicket(
      cache_entry.disk_idx as uint64,
      cache_entry.data)

  /*
  method finish_writeback(
      gshared cache_entry: R,
      glinear status: R,
      glinear stub: DiskWriteStub
  )
  returns (
      glinear status': R
  )
  requires cache_entry.CacheEntry?
  requires status == CacheStatus(cache_entry.cache_idx, WriteBack)
  requires 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  requires stub == DiskWriteStub(cache_entry.disk_idx as uint64)
  ensures status' == CacheStatus(cache_entry.cache_idx, Clean)*/
}
