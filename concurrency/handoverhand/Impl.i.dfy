include "../framework/GhostLinearSequence.i.dfy"
include "../framework/Mutex.s.dfy"
include "ShardedHashTableTokens.i.dfy"
include "ShardedHashTable.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"
include "../../lib/Base/sequences.i.dfy"

module Impl {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened GhostLinearMaybe
  import opened GhostLinearSequence_s
  import opened GhostLinearSequence_i
  import opened Mutexes

  import opened Limits
  import opened KeyValueType
  import MapIfc
  // import SSM = HashTableStubSSM

  import opened LinearSequence_i
  import opened LinearSequence_s

  import opened SSM = ShardedHashTable
  // import TST = ShardedHashTableTokens 
  // import T = TST.T
  import PCM = TicketStubPCM(MapIfc, SSM)
  import T = Tokens(PCM)
  import TST = TicketStubToken(MapIfc, SSM) 

  import opened GhostLoc

  type Token = T.Token

  linear datatype Cap = Cap(
    remaining: nat,
    glinear resource: Token)
  {
    predicate Inv(loc: Loc)
    {
      && remaining <= Capacity()
      && resource == T.Token(loc, unit()
        .(insert_capacity := remaining))
    }
  }

  linear datatype Row = Row(
    entry: Entry,
    glinear resource: Token)

  predicate RowInv(loc: Loc, index: nat, row: Row)
  {
    && 0 <= index as nat < FixedSize()
    && row.resource == T.Token(loc, oneRowResource(index as nat, Info(row.entry, Free), 0))
  }

  type RowMutex = Mutex<Row>

  type RowMutexTable = lseq<RowMutex>
  
  predicate RowMutexTablePartialInv(row_mutexes: RowMutexTable, loc: Loc, index: nat)
    requires index <= |row_mutexes| == FixedSize()
  {
    && (forall i | 0 <= i < index ::
      (i in row_mutexes) && (row_mutexes[i].inv == ((row: Row) => RowInv(loc, i, row))))
    && (forall i | index <= i < |row_mutexes| ::
      (i !in row_mutexes))
  }

  predicate RowMutexTableInv(row_mutexes: RowMutexTable, loc: Loc)
    requires |row_mutexes| == FixedSize()
  {
    RowMutexTablePartialInv(row_mutexes, loc, |row_mutexes|)
  }

  linear datatype IVariables = IVariables(
    linear row_mutexes: RowMutexTable,
    linear cap_mutex: Mutex<Cap>)
  {
    predicate Inv(loc: Loc)
    {
      && |row_mutexes| == FixedSize()
      && RowMutexTableInv(row_mutexes, loc)
      && (cap_mutex.inv == ((cap: Cap) => cap.Inv(loc)))
    }
  }

  datatype Splitted = Splitted(expected:SSM.M, ri:SSM.M)

  function {:opaque} InitResoucePartial(i: nat): SSM.M
    requires i <= FixedSize()
  {
    var table := seq(FixedSize(), j => if j >= i then Some(Info(Empty, Free)) else None);
    SSM.M(table, Capacity(), multiset{}, multiset{})
  }

  function Split(r:SSM.M, i:nat) : (splt:Splitted)
    requires i < FixedSize()
    requires r == InitResoucePartial(i)
    ensures SSM.dot(splt.expected, splt.ri) == r
  {
    var expected := InitResoucePartial(i+1);
    var ri := oneRowResource(i as nat, Info(Empty, Free), 0);
    reveal InitResoucePartial();
    Splitted(expected, ri)
  }

  method init(glinear in_token: Token)
  returns (glinear token: Token, linear iv: IVariables)
    requires in_token.val == SSM.Init()
    // ensures Inv(v)
    ensures token.val == SSM.unit()
  {
    var loc := in_token.loc;

    token := in_token;
    linear var row_mutexes :RowMutexTable := lseq_alloc(FixedSizeImpl() as uint64);

    var i:uint32 := 0;

    assert token.val == InitResoucePartial(0) by {
      reveal InitResoucePartial();
    }

    while i < FixedSizeImpl()
      invariant token.loc == loc
      invariant i as int <= |row_mutexes| == FixedSize()
      invariant token.val == InitResoucePartial(i as nat)
      invariant RowMutexTablePartialInv(row_mutexes, loc, i as nat)
    {
      ghost var splitted := Split(token.val, i as int);
      glinear var mutex_token := T.inout_split(inout token, splitted.expected, splitted.ri);
      linear var m := new_mutex<Row>(Row(Empty, mutex_token),
        (row: Row) => RowInv(loc, i as nat, row));
  
      lseq_give_inout(inout row_mutexes, i as uint64, m);

      i := i + 1;
    }

    assert token.val == SSM.unit().(insert_capacity := Capacity()) by {
      reveal InitResoucePartial();
    }

    glinear var mutex_token := T.inout_split(inout token, SSM.unit(), SSM.unit().(insert_capacity := Capacity()));

    linear var cap_mutex := new_mutex<Cap>(Cap(CapacityImpl() as nat, mutex_token),
      (cap: Cap) => cap.Inv(loc));
    
    iv := IVariables.IVariables(row_mutexes, cap_mutex);
  }

  predicate method shouldHashGoBefore(search_h: uint32, slot_h: uint32, slot_idx: uint32) 
    ensures shouldHashGoBefore(search_h, slot_h, slot_idx) 
      == ShouldHashGoBefore(search_h as int, slot_h as int, slot_idx as int)
  {
    || search_h < slot_h <= slot_idx // normal case
    || slot_h <= slot_idx < search_h // search_h wraps around the end of array
    || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  }

  function method getNextIndex(slot_idx: uint32) : uint32
    requires slot_idx < FixedSizeImpl()
  {
    if slot_idx == FixedSizeImpl() - 1 then 0 else slot_idx + 1
  }

  method acquireRow(shared iv: IVariables, index: uint32, glinear in_token: Token)
  returns (entry: Entry, glinear handle: MutexHandle<Row>, glinear out_token: Token)
    requires iv.Inv(in_token.loc)
    requires index < FixedSizeImpl();
    ensures handle.m == iv.row_mutexes[index as nat];
    ensures out_token.loc == in_token.loc;
    ensures out_token.val == dot(in_token.val, oneRowResource(index as nat, Info(entry, Free), 0))
  {
    linear var row; 
    row, handle := lseq_peek(iv.row_mutexes, index as uint64).acquire();
    linear var Row(out_entry, row_token) := row;

    entry := out_entry;

    out_token := T.join(in_token, row_token);
  }

  method releaseRow(
    shared iv: IVariables,
    index: uint32,
    entry: Entry,
    glinear handle: MutexHandle<Row>,
    glinear in_token: Token)
  returns (glinear out_token: Token)
    requires iv.Inv(in_token.loc);
    requires index < FixedSizeImpl();
    requires handle.m == iv.row_mutexes[index as nat];
    requires in_token.val.M?;
    requires in_token.val.table[index as nat] == Some(Info(entry, Free));
    ensures out_token.loc == in_token.loc;
    ensures out_token.val == in_token.val.(table := in_token.val.table[index := None]);
  {
    glinear var mutex_token;
    ghost var left := in_token.val.(table := in_token.val.table[index := None]);
    ghost var right := oneRowResource(index as nat, Info(entry, Free), 0);

    out_token, mutex_token := T.split(in_token, left, right);

    lseq_peek(iv.row_mutexes, index as uint64).release(Row(entry, mutex_token), handle);
  }

  linear method acquireCapacity(shared iv: IVariables, glinear in_token: Token)
  returns (glinear out_token: Token)
    decreases *
    requires iv.Inv(in_token.loc)
    requires in_token.val.M?;

    ensures out_token ==
      in_token.(val := in_token.val.(insert_capacity := in_token.val.insert_capacity + 1))
  {
    ghost var old_token := in_token;
    ghost var old_cap := in_token.val.insert_capacity;
    out_token := in_token;
    var continue := true;

    while continue
      invariant iv.Inv(old_token.loc)
      invariant continue ==> out_token == old_token
      invariant !continue ==> out_token == old_token.(val := old_token.val.(insert_capacity := old_cap + 1))
      decreases *
    {
      linear var cap; glinear var handle: MutexHandle<Cap>;
      cap, handle := iv.cap_mutex.acquire();

      linear var Cap(count, cap_token) := cap;

      if count >= 1 {
        count := count - 1;
        ghost var left := SSM.unit().(insert_capacity := count);
        ghost var right := SSM.unit().(insert_capacity := 1);
        assert SSM.dot(left, right) == cap_token.val; 
        glinear var temp_token := T.inout_split(inout cap_token, left, right);
        T.inout_join(inout out_token, temp_token);
        continue := false;
      }

      iv.cap_mutex.release(Cap(count, cap_token), handle);
    }
  }

  linear method releaseCapacity(shared iv: IVariables, glinear in_token: Token)
  returns (glinear out_token: Token)
    requires iv.Inv(in_token.loc)
    requires in_token.val.M?;
    requires in_token.val.insert_capacity == 1

    ensures out_token ==
      in_token.(val := in_token.val.(insert_capacity := in_token.val.insert_capacity - 1))
  {
    linear var cap; glinear var handle: MutexHandle<Cap>;
    cap, handle := iv.cap_mutex.acquire();

    linear var Cap(count, cap_token) := cap;

    count := count + 1;
    ghost var left := in_token.val.(insert_capacity := 0);
    ghost var right := SSM.unit().(insert_capacity := 1);
    assert SSM.dot(left, right) == in_token.val; 
    out_token := in_token;
    glinear var temp_token := T.inout_split(inout out_token, left, right);
    T.inout_join(inout cap_token, temp_token);

    iv.cap_mutex.release(Cap(count, cap_token), handle);
  }

  method doQuery(shared iv: IVariables, input: MapIfc.Input, rid: nat, glinear in_token: Token)
  returns (output: MapIfc.Output, glinear out_token: Token)
    requires iv.Inv(in_token.loc)
    requires input.QueryInput?
    requires in_token.val == SSM.Ticket(rid, input)
    ensures out_token.val == SSM.Stub(rid, output)
    decreases *
  {
    ghost var loc := in_token.loc;
    var query_ticket := SSM.Request(rid, input);
    var key, hash_idx := input.key, hash(input.key);
    var slot_idx := hash_idx;

    var entry; glinear var handle;
    entry, handle, out_token := acquireRow(iv, hash_idx, in_token);

    var step := ProcessQueryTicketStep(query_ticket);
    var expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    while true 
      invariant iv.Inv(loc);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant out_token.loc == loc;
      invariant out_token.val == oneRowResource(slot_idx as nat, Info(entry, Querying(rid, key)), 0);
      invariant handle.m == iv.row_mutexes[slot_idx as nat];
      decreases *
    {
      var next_slot_idx := getNextIndex(slot_idx);

      match entry {
        case Empty => {
          output := MapIfc.QueryOutput(NotFound);
          step := QueryNotFoundStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            step := QueryDoneStep(slot_idx as nat);
            output := MapIfc.QueryOutput(Found(value));
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);
            if !should_go_before {
              step := QuerySkipStep(slot_idx as nat);
            } else {
              output := MapIfc.QueryOutput(NotFound);
              step := QueryNotFoundStep(slot_idx as nat);
            }
          }
        }
      }

      if !step.QuerySkipStep? {
        // this test is required for termination, but is not enforced by verification
        // because we are using decreases *
        break;
      }
    
      var next_entry; glinear var next_handle;
      next_entry, next_handle, out_token := acquireRow(iv, next_slot_idx, out_token);

      expected := SSM.GetTransition(out_token.val, step);
      out_token := TST.transition_1_1(out_token, expected);

      out_token := releaseRow(iv, slot_idx, entry, handle, out_token);

      slot_idx, entry := next_slot_idx, next_entry;
      handle := next_handle;
    }
    
    assert step.QueryNotFoundStep? || step.QueryDoneStep?;
    expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);
    out_token := releaseRow(iv, slot_idx, entry, handle, out_token);
  }

  method doInsert(shared iv: IVariables, input: MapIfc.Input, rid: nat, thread_id: uint32, glinear in_token: Token)
  returns (output: MapIfc.Output, glinear out_token: Token)
    requires iv.Inv(in_token.loc)
    requires input.InsertInput?
    requires in_token.val == SSM.Ticket(rid, input)
    ensures out_token.val == SSM.Stub(rid, output)
    decreases *
  {
    ghost var loc := in_token.loc;

    var key, inital_key := input.key, input.key;
    var kv := KV(key, input.value);
    output := MapIfc.InsertOutput(true);

    var hash_idx := hash(key);
    var slot_idx := hash_idx;

    out_token := acquireCapacity(iv, in_token);

    var entry; glinear var handle;
    entry, handle, out_token := acquireRow(iv, slot_idx, out_token);

    var step := ProcessInsertTicketStep(SSM.Request(rid, input));
    var expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    while true 
      invariant iv.Inv(loc)
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant out_token.loc == loc;
      invariant out_token.val == oneRowResource(slot_idx as nat, Info(entry, Inserting(rid, kv, inital_key)), 0)
      invariant kv.key == key
      invariant hash_idx == hash(key)
      invariant handle.m == iv.row_mutexes[slot_idx as nat];
      decreases *
    {
      var next_slot_idx := getNextIndex(slot_idx);
      var new_kv;

      match entry {
        case Empty => {
          step := InsertDoneStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          new_kv := KV(entry_key, value);
          if entry_key == key {
            step := InsertUpdateStep(slot_idx as nat);
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);
            if !should_go_before {
              step := InsertSkipStep(slot_idx as nat);
            } else {
              step := InsertSwapStep(slot_idx as nat);
            }
          }
        }
      }

      if step.InsertDoneStep? || step.InsertUpdateStep? {
        break;
      }

      glinear var next_handle; var next_entry;
      next_entry, next_handle, out_token := acquireRow(iv, next_slot_idx, out_token);

      if step.InsertSwapStep? {
        entry := Full(kv);
        kv := new_kv;
        key := new_kv.key;
      }
  
      expected := SSM.GetTransition(out_token.val, step);
      out_token := TST.transition_1_1(out_token, expected);
      out_token := releaseRow(iv, slot_idx, entry, handle, out_token);

      slot_idx, entry, hash_idx := next_slot_idx, next_entry, hash(key);
      handle := next_handle;
    }

    // assert step.InsertDoneStep? || step.InsertUpdateStep?;
    expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    out_token := releaseRow(iv, slot_idx, Full(kv), handle, out_token);

    if step.InsertUpdateStep? {
      out_token := releaseCapacity(iv, out_token);
      assert out_token.val.insert_capacity == 0;
    }
  }

  method doRemoveFound(shared iv: IVariables, rid: nat, 
    slot_idx: uint32,
    hash_idx: uint32,
    inital_key: Key,
    entry: SSM.Entry,
    glinear handle: MutexHandle<Row>,
    glinear in_token: Token)
  
    returns (output: MapIfc.Output, glinear out_token: Token)
    decreases *
    requires iv.Inv(in_token.loc)
    requires 0 <= slot_idx < FixedSizeImpl()
    requires 0 <= hash_idx < FixedSizeImpl()
    requires in_token.val == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, inital_key)), 0);
    requires entry.Full? && entry.kv.key == inital_key
    requires hash(inital_key) == hash_idx
    requires handle.m == iv.row_mutexes[slot_idx as nat]
    ensures out_token.val == SSM.Stub(rid, output)
  {
    ghost var loc := in_token.loc;
    var found_value := entry.kv.val;

    var slot_idx := slot_idx;
    var next_slot_idx := getNextIndex(slot_idx);

    glinear var handle := handle;
    glinear var next_handle; var next_entry;
    out_token := in_token;
    next_entry, next_handle, out_token := acquireRow(iv, next_slot_idx, out_token);

    var step := RemoveFoundItStep(slot_idx as nat);

    var expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    while true
      invariant iv.Inv(loc)
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant out_token.loc == loc
      invariant out_token.val == twoRowsResource(
        slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
        NextPos(slot_idx as nat), Info(next_entry, Free),
        0)
      invariant handle.m == iv.row_mutexes[slot_idx as nat]
      invariant next_handle.m == iv.row_mutexes[NextPos(slot_idx as nat)]
      decreases *
    {
      next_slot_idx := getNextIndex(slot_idx);

      if next_entry.Empty? || (next_entry.Full? && hash(next_entry.kv.key) == next_slot_idx) {
        assert DoneTidying(out_token.val, slot_idx as nat);
        break;
      }

      expected := SSM.GetTransition(out_token.val, RemoveTidyStep(slot_idx as nat));
      out_token := TST.transition_1_1(out_token, expected);
      out_token := releaseRow(iv, slot_idx, next_entry, handle, out_token);

      slot_idx := next_slot_idx;
      next_slot_idx := getNextIndex(slot_idx);
      handle := next_handle;

      next_entry, next_handle, out_token := acquireRow(iv, next_slot_idx, out_token);
    }
    assert DoneTidying(out_token.val, slot_idx as nat);

    next_slot_idx := getNextIndex(slot_idx);
    output := MapIfc.RemoveOutput(true);

    step := RemoveDoneStep(slot_idx as nat);
    expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    out_token := releaseRow(iv, slot_idx, Empty, handle, out_token);
    out_token := releaseRow(iv, next_slot_idx, next_entry, next_handle, out_token);

    out_token := releaseCapacity(iv, out_token);
    assert out_token.val.insert_capacity == 0;
  }

  method doRemove(shared iv: IVariables, input: MapIfc.Input, rid: nat, thread_id: uint32, glinear in_token: Token)
    returns (output: MapIfc.Output, glinear out_token: Token)
    decreases *

    requires iv.Inv(in_token.loc)
    requires input.RemoveInput?
    requires in_token.val == SSM.Ticket(rid, input)
    ensures out_token.val == SSM.Stub(rid, output)
  {
    ghost var loc := in_token.loc;

    var query_ticket := SSM.Request(rid, input);
    var key := input.key;
    var hash_idx := hash(key);
    var slot_idx := hash_idx;

    var entry; glinear var handle;
    entry, handle, out_token := acquireRow(iv, slot_idx, in_token);

    var step : Step := ProcessRemoveTicketStep(query_ticket);
    // r := easy_transform_step(r, step);
    var expected := SSM.GetTransition(out_token.val, step);
    out_token := TST.transition_1_1(out_token, expected);

    while true 
      invariant iv.Inv(loc)
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant out_token.loc == loc
      invariant out_token.val == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, key)), 0)
      invariant step.RemoveNotFoundStep? ==> 
        (entry.Full? && shouldHashGoBefore(hash_idx, hash(entry.kv.key), slot_idx))
      invariant step.RemoveTidyStep? ==> (
        && TidyEnable(out_token.val, slot_idx as nat)
        && KnowRowIsFree(out_token.val, NextPos(slot_idx as nat)))
      invariant handle.m == iv.row_mutexes[slot_idx as nat]
      decreases *
    {
      var next_slot_idx := getNextIndex(slot_idx);

      match entry {
        case Empty => {
          step := RemoveNotFoundStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            step := RemoveFoundItStep(slot_idx as nat);
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);

            if !should_go_before {
              step := RemoveSkipStep(slot_idx as nat);
            } else {
              step := RemoveNotFoundStep(slot_idx as nat);
            }
          }
        }
      }

      if step.RemoveNotFoundStep? || step.RemoveFoundItStep? {
        break;
      }

      glinear var next_handle; var next_entry;
      next_entry, next_handle, out_token := acquireRow(iv, next_slot_idx, out_token);

      expected := SSM.GetTransition(out_token.val, step);
      out_token := TST.transition_1_1(out_token, expected);

      out_token := releaseRow(iv, slot_idx, entry, handle, out_token);

      slot_idx, entry := next_slot_idx, next_entry;
      handle := next_handle;
    }

    if step.RemoveNotFoundStep? {
      output := MapIfc.RemoveOutput(false);

      expected := SSM.GetTransition(out_token.val, step);
      out_token := TST.transition_1_1(out_token, expected);
      out_token := releaseRow(iv, slot_idx, entry, handle, out_token);
    } else {
      output, out_token := doRemoveFound(iv, rid, slot_idx, hash_idx, key, entry, handle, out_token);
    }
  }
}