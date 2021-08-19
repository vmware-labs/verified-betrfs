include "../../../lib/Base/Option.s.dfy"
include "../../../lib/Lang/NativeTypes.s.dfy"
include "CacheSM.i.dfy"

module CacheResources {
  import opened Options
  import opened NativeTypes
  import opened GhostLoc
  import opened CacheStatusType
  import DiskIfc
  import T = DiskSSMTokens(CacheIfc, CacheSSM)
  import CacheSSM

  datatype DiskPageMap = DiskPageMap(ghost disk_idx: int, ghost cache_idx_opt: Option<int>)

  /*function CacheEntry(
        // this field is meaningless if status == Empty
        disk_idx: int,
        cache_idx: int, data: DiskIfc.Block) : M*/

  datatype CacheStatus = CacheStatus(ghost cache_idx: int, ghost status: Status)
  {
    predicate is_status(cache_idx: int, status: Status) {
      this.cache_idx == cache_idx && this.status == status
    }
  }

  datatype CacheEmpty = CacheEmpty(
      ghost cache_idx: nat)

  datatype CacheReading = CacheReading(
      ghost cache_idx: nat, ghost disk_idx: nat)

  datatype CacheEntry = CacheEntry(
      ghost cache_idx: nat, ghost disk_idx: nat, ghost data: DiskIfc.Block)

  datatype DiskWriteTicket = DiskWriteTicket(
      ghost addr: nat, ghost contents: DiskIfc.Block)
  {
    predicate writes(addr: nat, contents: DiskIfc.Block) {
      this.addr == addr && this.contents == contents
    }

    function defn() : T.Token {
      T.Token(CacheSSM.DiskWriteReq(addr, contents))
    }
  }

  function method DiskWriteTicket_unfold(glinear disk_write_ticket: DiskWriteTicket)
      : (glinear t: T.Token)
  ensures t == disk_write_ticket.defn()

  datatype DiskWriteStub = DiskWriteStub(ghost disk_idx: nat)
  {
    predicate written(disk_idx: uint64) {
      this.disk_idx == disk_idx as nat
    }

    function defn() : T.Token {
      T.Token(CacheSSM.DiskWriteResp(disk_idx))
    }
  }

  datatype DiskReadTicket = DiskReadTicket(ghost addr: nat)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.DiskReadReq(addr))
    }
  }

  function method DiskReadTicket_unfold(glinear disk_read_ticket: DiskReadTicket)
      : (glinear t: T.Token)
  ensures t == disk_read_ticket.defn()

  datatype DiskReadStub = DiskReadStub(ghost addr: nat, ghost data: DiskIfc.Block)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.DiskReadResp(addr, data))
    }
  }

  function method DiskReadStub_fold(ghost addr: nat, ghost data: DiskIfc.Block,
          glinear t: T.Token)
      : (glinear disk_read_stub: DiskReadStub)
  requires DiskReadStub(addr, data).defn() == t
  ensures disk_read_stub == DiskReadStub(addr, data)

    /*| DiskReadTicket(addr: uint64)
    | DiskReadStub(addr: uint64, contents: DiskIfc.Block)

    | DiskWriteTicket(addr: uint64, contents: DiskIfc.Block)
    | DiskWriteStub(addr: uint64)*/

  glinear method initiate_page_in(
      ghost cache_idx: nat,
      ghost disk_idx: nat,
      glinear s2: CacheEmpty,
      glinear s3: DiskPageMap
  )
  returns (
      glinear t2: CacheReading,
      glinear t3: DiskPageMap,
      glinear t4: DiskReadTicket
  )
  requires s2.cache_idx == cache_idx
  requires s3 == DiskPageMap(disk_idx, None)
  ensures t2.cache_idx == cache_idx
  ensures t2.disk_idx == disk_idx
  ensures t3 == DiskPageMap(disk_idx, Some(cache_idx))
  ensures t4 == DiskReadTicket(disk_idx)

/*
  glinear method finish_page_in(
      ghost cache_idx: nat,
      ghost disk_idx: uint64,
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

  glinear method initiate_writeback(
      gshared cache_entry: CacheEntry,
      glinear status: CacheStatus
  )
  returns (
      glinear status': CacheStatus,
      glinear ticket: DiskWriteTicket
  )
  requires status.cache_idx == cache_entry.cache_idx
  requires status.status == Dirty
  ensures status.cache_idx == cache_entry.cache_idx
  ensures status.status == Writeback
  ensures 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  ensures ticket == DiskWriteTicket(
      cache_entry.disk_idx,
      cache_entry.data)

  glinear method finish_writeback(
      gshared cache_entry: CacheEntry,
      glinear status: CacheStatus,
      glinear stub: DiskWriteStub
  )
  returns (
      glinear status': CacheStatus
  )
  requires status.is_status(cache_entry.cache_idx, Writeback)
  requires 0 <= cache_entry.disk_idx < 0x1_0000_0000_0000_0000
  requires stub.written(cache_entry.disk_idx as uint64)
  ensures status'.is_status(cache_entry.cache_idx, Clean)
}
