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
  import T = DiskToken(CacheIfc, CacheSSM)
  import CacheSSM

  datatype {:glinear_fold} DiskPageMap = DiskPageMap(ghost disk_idx: nat, ghost cache_idx_opt: Option<nat>)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.DiskIdxToCacheIdx(disk_idx, cache_idx_opt))
    }
  }

  datatype {:glinear_fold} HavocPermission = HavocPermission(ghost rid: RequestId, ghost disk_idx: int)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.Havoc(rid, disk_idx))
    }
  }

  datatype {:glinear_fold} CacheStatus = CacheStatus(ghost cache_idx: nat, ghost status: Status)
  {
    predicate is_status(cache_idx: int, status: Status) {
      this.cache_idx == cache_idx && this.status == status
    }

    function defn() : T.Token {
      T.Token(CacheSSM.CacheStatus(cache_idx, status))
    }
  }

  datatype {:glinear_fold} CacheEmpty = CacheEmpty(
      ghost cache_idx: nat)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.CacheEmpty(cache_idx))
    }
  }

  datatype {:glinear_fold} CacheReading = CacheReading(
      ghost cache_idx: nat, ghost disk_idx: nat)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.CacheReading(cache_idx, disk_idx))
    }
  }

  datatype {:glinear_fold} CacheEntry = CacheEntry(
      ghost cache_idx: nat, ghost disk_idx: nat, ghost data: DiskIfc.Block)
  {
    function defn() : T.Token {
      T.Token(CacheSSM.CacheEntry(cache_idx, disk_idx, data))
    }
  }

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
  {
    glinear var a_token := CacheEmpty_unfold(s2);
    glinear var b_token := DiskPageMap_unfold(s3);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheReading(cache_idx, disk_idx);
    ghost var out1_token_expect := CacheReading_unfold(out1_expect);

    ghost var out2_expect := DiskPageMap(disk_idx, Some(cache_idx));
    ghost var out2_token_expect := DiskPageMap_unfold(out2_expect);

    ghost var out3_expect := DiskReadTicket(disk_idx);
    ghost var out3_token_expect := DiskReadTicket_unfold(out3_expect);

    // Explain what transition we're going to do
    assert CacheSSM.StartRead(
        CacheSSM.dot(a_token.val, b_token.val),
        CacheSSM.dot(CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
            out3_token_expect.val),
        cache_idx, disk_idx);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(a_token.val, b_token.val),
        CacheSSM.dot(CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
            out3_token_expect.val),
        CacheSSM.StartReadStep(cache_idx, disk_idx));

    // Perform the transition
    glinear var out1_token, out2_token, out3_token := T.transition_2_3(a_token, b_token,
        out1_token_expect.val,
        out2_token_expect.val,
        out3_token_expect.val);

    t2 := CacheReading_fold(out1_expect, out1_token);
    t3 := DiskPageMap_fold(out2_expect, out2_token);
    t4 := DiskReadTicket_fold(out3_expect, out3_token);
  }

  glinear method havoc_page_in(
      ghost cache_idx: nat,
      ghost disk_idx: nat,
      glinear s2: CacheEmpty,
      glinear s3: DiskPageMap,
      gshared havoc: HavocPermission,
      ghost data: DiskIfc.Block
  )
  returns (
      glinear t2: CacheEntry,
      glinear t3: DiskPageMap,
      glinear status: CacheStatus
  )
  requires s2.cache_idx == cache_idx
  requires s3 == DiskPageMap(disk_idx, None)
  requires havoc.disk_idx == disk_idx
  ensures t2.cache_idx == cache_idx
  ensures t2.disk_idx == disk_idx
  ensures t2.data == data
  ensures t3 == DiskPageMap(disk_idx, Some(cache_idx))
  ensures status == CacheStatus(cache_idx, Dirty)
  {
    glinear var a_token := CacheEmpty_unfold(s2);
    glinear var b_token := DiskPageMap_unfold(s3);
    gshared var s_token := HavocPermission_unfold_borrow(havoc);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheEntry(cache_idx, disk_idx, data);
    ghost var out1_token_expect := CacheEntry_unfold(out1_expect);

    ghost var out2_expect := DiskPageMap(disk_idx, Some(cache_idx));
    ghost var out2_token_expect := DiskPageMap_unfold(out2_expect);

    ghost var out3_expect := CacheStatus(cache_idx, Dirty);
    ghost var out3_token_expect := CacheStatus_unfold(out3_expect);

    // Explain what transition we're going to do
    assert CacheSSM.HavocNew(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(CacheSSM.dot(out1_token_expect.val, out2_token_expect.val), out3_token_expect.val)),
        cache_idx, havoc.rid, data);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(CacheSSM.dot(out1_token_expect.val, out2_token_expect.val), out3_token_expect.val)),
        CacheSSM.HavocNewStep(cache_idx, havoc.rid, data));

    // Perform the transition
    glinear var out1_token, out2_token, out3_token := T.transition_1_2_3(s_token, a_token, b_token,
        out1_token_expect.val,
        out2_token_expect.val,
        out3_token_expect.val);

    t2 := CacheEntry_fold(out1_expect, out1_token);
    t3 := DiskPageMap_fold(out2_expect, out2_token);
    status := CacheStatus_fold(out3_expect, out3_token);
  }

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
  {
    glinear var a_token := CacheStatus_unfold(status);
    glinear var b_token := CacheEntry_unfold(cache_entry);
    glinear var c_token := DiskPageMap_unfold(dpm);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheEmpty(cache_idx);
    ghost var out1_token_expect := CacheEmpty_unfold(out1_expect);

    ghost var out2_expect := DiskPageMap(disk_idx, None);
    ghost var out2_token_expect := DiskPageMap_unfold(out2_expect);

    // Explain what transition we're going to do
    assert CacheSSM.Evict(
        CacheSSM.dot(CacheSSM.dot(a_token.val, b_token.val), c_token.val),
        CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
        cache_idx);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(CacheSSM.dot(a_token.val, b_token.val), c_token.val),
        CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
        CacheSSM.EvictStep(cache_idx));

    // Perform the transition
    glinear var out1_token, out2_token := T.transition_3_2(a_token, b_token, c_token,
        out1_token_expect.val,
        out2_token_expect.val);

    cache_empty := CacheEmpty_fold(out1_expect, out1_token);
    dpm' := DiskPageMap_fold(out2_expect, out2_token);
  }

  glinear method unassign_page_havoc(
      ghost cache_idx: nat,
      ghost disk_idx: nat,
      glinear status: CacheStatus,
      glinear cache_entry: CacheEntry,
      glinear dpm: DiskPageMap,
      gshared havoc: HavocPermission
  )
  returns (
      glinear cache_empty: CacheEmpty,
      glinear dpm': DiskPageMap
  )
  requires status.cache_idx == cache_idx
  requires status.status != Writeback
  requires cache_entry == CacheEntry(cache_idx, disk_idx, cache_entry.data)
  requires dpm == DiskPageMap(disk_idx, dpm.cache_idx_opt)
  requires havoc.disk_idx == disk_idx
  ensures cache_empty == CacheEmpty(cache_idx)
  ensures dpm' == DiskPageMap(disk_idx, None)
  {
    glinear var a_token := CacheStatus_unfold(status);
    glinear var b_token := CacheEntry_unfold(cache_entry);
    glinear var c_token := DiskPageMap_unfold(dpm);
    gshared var s_token := HavocPermission_unfold_borrow(havoc);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheEmpty(cache_idx);
    ghost var out1_token_expect := CacheEmpty_unfold(out1_expect);

    ghost var out2_expect := DiskPageMap(disk_idx, None);
    ghost var out2_token_expect := DiskPageMap_unfold(out2_expect);

    // Explain what transition we're going to do
    assert CacheSSM.HavocEvict(
        CacheSSM.dot(s_token.val, CacheSSM.dot(CacheSSM.dot(a_token.val, b_token.val), c_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_token_expect.val)),
        cache_idx, havoc.rid);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, CacheSSM.dot(CacheSSM.dot(a_token.val, b_token.val), c_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_token_expect.val)),
        CacheSSM.HavocEvictStep(cache_idx, havoc.rid));

    // Perform the transition
    glinear var out1_token, out2_token := T.transition_1_3_2(s_token, a_token, b_token, c_token,
        out1_token_expect.val,
        out2_token_expect.val);

    cache_empty := CacheEmpty_fold(out1_expect, out1_token);
    dpm' := DiskPageMap_fold(out2_expect, out2_token);
  }

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
  {
    glinear var a_token := CacheReading_unfold(s2);
    glinear var b_token := DiskReadStub_unfold(s3);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheStatus(cache_idx, Clean);
    ghost var out1_token_expect := CacheStatus_unfold(out1_expect);

    ghost var out2_expect := CacheEntry(s2.cache_idx, s2.disk_idx, s3.data);
    ghost var out2_token_expect := CacheEntry_unfold(out2_expect);

    // Explain what transition we're going to do
    assert CacheSSM.FinishRead(
        CacheSSM.dot(a_token.val, b_token.val),
        CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
        cache_idx, disk_idx);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(a_token.val, b_token.val),
        CacheSSM.dot(out1_token_expect.val, out2_token_expect.val),
        CacheSSM.FinishReadStep(cache_idx, disk_idx));

    // Perform the transition
    glinear var out1_token, out2_token := T.transition_2_2(a_token, b_token,
        out1_token_expect.val,
        out2_token_expect.val);

    t1 := CacheStatus_fold(out1_expect, out1_token);
    t2 := CacheEntry_fold(out2_expect, out2_token);
  }

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
  ensures status'.cache_idx == cache_entry.cache_idx
  ensures status'.status == Writeback
  ensures ticket == DiskWriteTicket(
      cache_entry.disk_idx,
      cache_entry.data)
  {
    gshared var s_token := CacheEntry_unfold_borrow(cache_entry);
    glinear var a_token := CacheStatus_unfold(status);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheStatus(cache_entry.cache_idx, Writeback);
    ghost var out1_token_expect := CacheStatus_unfold(out1_expect);

    ghost var out2_expect := DiskWriteTicket(cache_entry.disk_idx, cache_entry.data);
    ghost var out2_token_expect := DiskWriteTicket_unfold(out2_expect);

    // Explain what transition we're going to do
    assert CacheSSM.StartWriteback(
        CacheSSM.dot(s_token.val, a_token.val),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_token_expect.val)),
        cache_entry.cache_idx);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, a_token.val),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_token_expect.val)),
        CacheSSM.StartWritebackStep(cache_entry.cache_idx));

    // Perform the transition
    glinear var out1_token, out2_token := T.transition_1_1_2(s_token, a_token,
        out1_token_expect.val,
        out2_token_expect.val);

    status' := CacheStatus_fold(out1_expect, out1_token);
    ticket := DiskWriteTicket_fold(out2_expect, out2_token);
  }

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
  {
    gshared var s_token := CacheEntry_unfold_borrow(cache_entry);
    glinear var a_token := CacheStatus_unfold(status);
    glinear var b_token := DiskWriteStub_unfold(stub);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := CacheStatus(cache_entry.cache_idx, Clean);
    ghost var out1_token_expect := CacheStatus_unfold(out1_expect);

    // Explain what transition we're going to do
    assert CacheSSM.FinishWriteback(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, out1_token_expect.val),
        cache_entry.cache_idx);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, out1_token_expect.val),
        CacheSSM.FinishWritebackStep(cache_entry.cache_idx));

    // Perform the transition
    glinear var out1_token := T.transition_1_2_1(s_token, a_token, b_token,
        out1_token_expect.val);

    status' := CacheStatus_fold(out1_expect, out1_token);
  }

  glinear method status_mark_dirty(glinear status: CacheStatus)
  returns (glinear status': CacheStatus)
  requires status.status == Clean
  ensures status' == status.(status := Dirty)
  {
    glinear var a_token := CacheStatus_unfold(status);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := status.(status := Dirty);
    ghost var out1_token_expect := CacheStatus_unfold(out1_expect);

    // Explain what transition we're going to do
    assert CacheSSM.MarkDirty(
        a_token.val,
        out1_token_expect.val,
        status.cache_idx);
    assert CacheSSM.InternalStep(
        a_token.val,
        out1_token_expect.val,
        CacheSSM.MarkDirtyStep(status.cache_idx));

    // Perform the transition
    glinear var out1_token := T.transition_1_1(a_token,
        out1_token_expect.val);

    status' := CacheStatus_fold(out1_expect, out1_token);
  }

  glinear method app_read_block(
      ghost rid: RequestId,
      gshared cache_entry: CacheEntry,
      glinear ticket: T.Token)
  returns (glinear stub: T.Token)
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.ReadInput(cache_entry.disk_idx))
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.ReadOutput(cache_entry.data))
  {
    gshared var s_token := CacheEntry_unfold_borrow(cache_entry);
    glinear var a_token := ticket;

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_token_expect := CacheSSM.Stub(rid, CacheIfc.ReadOutput(cache_entry.data));

    // Explain what transition we're going to do
    assert CacheSSM.ApplyRead(
        CacheSSM.dot(s_token.val, a_token.val),
        CacheSSM.dot(s_token.val, out1_token_expect),
        cache_entry.cache_idx, rid);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, a_token.val),
        CacheSSM.dot(s_token.val, out1_token_expect),
        CacheSSM.ApplyReadStep(cache_entry.cache_idx, rid));

    // Perform the transition
    glinear var out1_token := T.transition_1_1_1(s_token, a_token,
        out1_token_expect);

    stub := out1_token;
  }

  glinear method app_write_block(
      ghost rid: RequestId,
      ghost new_data: DiskIfc.Block,
      glinear cache_entry: CacheEntry,
      glinear ticket: T.Token,
      gshared status: CacheStatus)
  returns (glinear cache_entry': CacheEntry, glinear stub: T.Token)
  requires status.cache_idx == cache_entry.cache_idx
  requires status.status == Dirty
  requires ticket.val == CacheSSM.Ticket(rid, CacheIfc.WriteInput(cache_entry.disk_idx, new_data))
  ensures stub.val == CacheSSM.Stub(rid, CacheIfc.WriteOutput)
  ensures cache_entry' == cache_entry.(data := new_data)
  {
    glinear var a_token := CacheEntry_unfold(cache_entry);
    glinear var b_token := ticket;
    gshared var s_token := CacheStatus_unfold_borrow(status);

    // Compute the things we want to output (as ghost, _not_ glinear constructs)
    ghost var out1_expect := cache_entry.(data := new_data);
    ghost var out1_token_expect := CacheEntry_unfold(out1_expect);

    ghost var out2_expect := CacheSSM.Stub(rid, CacheIfc.WriteOutput);

    // Explain what transition we're going to do
    assert CacheSSM.ApplyWrite(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_expect)),
        cache_entry.cache_idx, rid);
    assert CacheSSM.InternalStep(
        CacheSSM.dot(s_token.val, CacheSSM.dot(a_token.val, b_token.val)),
        CacheSSM.dot(s_token.val, CacheSSM.dot(out1_token_expect.val, out2_expect)),
        CacheSSM.ApplyWriteStep(cache_entry.cache_idx, rid));

    // Perform the transition
    glinear var out1_token, out2_token := T.transition_1_2_2(s_token, a_token, b_token,
        out1_token_expect.val,
        out2_expect);

    cache_entry' := CacheEntry_fold(out1_expect, out1_token);
    stub := out2_token;
  }

  function IdxsRange(a: nat, b: nat) : map<nat, Option<nat>>
  requires a <= b
  {
    map i : nat | a <= i < b :: None
  }

  function EmptyRange(a: nat, b: nat) : map<nat, CacheSSM.Entry>
  requires a <= b
  {
    map i : nat | a <= i < b :: CacheSSM.Empty
  }

  function IdxsSeq(a: nat, b: nat) : T.Token
  requires a <= b
  {
    T.Token(
      CacheSSM.M(IdxsRange(a, b),
        map[], map[], map[], {}, {}, map[], map[], map[], map[], map[]))
  }

  function EmptySeq(a: nat, b: nat) : T.Token
  requires a <= b
  {
    T.Token(
      CacheSSM.M(map[],
        EmptyRange(a, b),
        map[], map[], {}, {}, map[], map[], map[], map[], map[]))
  }

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
