include "../../../lib/Base/Option.s.dfy"
include "../../../lib/Lang/NativeTypes.s.dfy"
include "CacheSM.i.dfy"
include "../Constants.i.dfy"

module CacheResources {
  import opened Options
  import opened NativeTypes
  import opened GhostLoc
  import opened RequestIds
  import opened CacheStatusType
  import opened Constants
  import DiskIfc
  import CacheIfc
  import T = DiskSSMTokens(CacheIfc, CacheSSM)
  import CacheSSM

  datatype DiskPageMap = DiskPageMap(ghost disk_idx: int, ghost cache_idx_opt: Option<int>)

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

  datatype {:glinear_fold} DiskWriteTicket = DiskWriteTicket(
      ghost addr: nat, ghost contents: DiskIfc.Block)
  {
    predicate writes(addr: nat, contents: DiskIfc.Block) {
      this.addr == addr && this.contents == contents
    }

    function defn() : T.Token {
      T.Token(CacheSSM.DiskWriteReq(addr, contents))
    }
  }

  datatype {:glinear_fold} DiskWriteStub = DiskWriteStub(ghost disk_idx: nat)
  {
    predicate written(disk_idx: uint64) {
      this.disk_idx == disk_idx as nat
    }

    function defn() : T.Token {
      T.Token(CacheSSM.DiskWriteResp(disk_idx))
    }
  }

  datatype {:glinear_fold} DiskReadTicket = DiskReadTicket(ghost addr: nat)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.DiskReadReq(addr))
    }
  }

  datatype {:glinear_fold} DiskReadStub = DiskReadStub(ghost addr: nat, ghost data: DiskIfc.Block)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.DiskReadResp(addr, data))
    }
  }

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

  glinear method inv_map_agrees(
      gshared cache_entry: CacheEntry,
      glinear inout dpm: DiskPageMap
  )
  requires old_dpm.disk_idx == cache_entry.disk_idx
  ensures old_dpm == dpm
  ensures dpm.cache_idx_opt == Some(cache_entry.cache_idx)

  glinear method unassign_page(
      ghost cache_idx: nat,
      ghost disk_idx: nat,
      glinear status: CacheStatus,
      glinear cache_entry: CacheEntry,
      glinear dpm: DiskPageMap
  )
  returns (
      glinear cache_empty: CacheEmpty,
      glinear dpm': DiskPageMap
  )
  requires status == CacheStatus(cache_idx, Clean)
  requires cache_entry == CacheEntry(cache_idx, disk_idx, cache_entry.data)
  requires dpm == DiskPageMap(disk_idx, dpm.cache_idx_opt)
  ensures cache_empty == CacheEmpty(cache_idx)
  ensures dpm' == DiskPageMap(disk_idx, None)

  glinear method finish_page_in(
      ghost cache_idx: nat,
      ghost disk_idx: nat,
      glinear s2: CacheReading,
      glinear s3: DiskReadStub
  )
  returns (
      glinear t1: CacheStatus,
      glinear t2: CacheEntry
  )
  requires s2.CacheReading? && s2.disk_idx == disk_idx as int
      && s2.cache_idx == cache_idx
  requires s3.addr == disk_idx
  ensures t1 == CacheStatus(cache_idx, Clean)
  ensures t2 == CacheEntry(s2.cache_idx, s2.disk_idx, s3.data)

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

  glinear method status_mark_dirty(glinear status: CacheStatus)
  returns (glinear status': CacheStatus)
  requires status.status == Clean
  ensures status' == status.(status := Dirty)

  glinear method app_read_block(
      ghost rid: RequestId,
      gshared cache_entry: CacheEntry,
      glinear ticket: T.Token)
  returns (glinear stub: T.Token)
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.ReadInput(cache_entry.disk_idx))
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.ReadOutput(cache_entry.data))

  glinear method app_write_block(
      ghost rid: RequestId,
      ghost new_data: DiskIfc.Block,
      glinear cache_entry: CacheEntry,
      glinear ticket: T.Token)
  returns (glinear cache_entry': CacheEntry, glinear stub: T.Token)
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.WriteInput(cache_entry.disk_idx, new_data))
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.WriteOutput)
  ensures cache_entry' == cache_entry.(data := new_data)

  function IdxsSeq(a: nat, b: nat) : T.Token
  requires a <= b

  function EmptySeq(a: nat, b: nat) : T.Token
  requires a <= b

  glinear method pop_IdxSeq(glinear t: T.Token, ghost a: nat, ghost b: nat)
  returns (glinear x: DiskPageMap, glinear t': T.Token)
  requires a < b
  requires t == IdxsSeq(a, b)
  ensures t' == IdxsSeq(a+1, b)
  ensures x == DiskPageMap(a, None)

  glinear method pop_EmptySeq(glinear t: T.Token, ghost a: nat, ghost b: nat)
  returns (glinear x: CacheEmpty, glinear t': T.Token)
  requires a < b
  requires t == EmptySeq(a, b)
  ensures t' == EmptySeq(a+1, b)
  ensures x == CacheEmpty(a)

  glinear method split_init(glinear t: T.Token)
  returns (glinear idxs: T.Token, glinear empties: T.Token)
  requires CacheSSM.Init(t.val)
  ensures idxs == IdxsSeq(0, NUM_DISK_PAGES as int)
  ensures empties == EmptySeq(0, CACHE_SIZE as int)
}
