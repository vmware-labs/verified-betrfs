include "CapacityAllocator.i.dfy"
include "ConcurrencyTools.s.dfy"
include "ShardedHashTable.i.dfy"
include "VerificationObligation.s.dfy"

module Impl refines VerificationObligation {
  import opened Options
  import SSM = ShardedHashTable
  import opened ShardedHashTable
  import opened KeyValueType
  import opened Mutexes
  import opened CapacityAllocatorTypes
  import CAP = CapacityAllocator
  import opened Limits

  linear datatype Row = Row(
    entry: SSM.Entry,
    glinear resource: SSM.Variables)

  function RowInv(index: nat, row: Row): bool
  {
    && 0 <= index as nat < FixedSize()
    && row.resource == oneRowResource(index as nat, Info(row.entry, Free), 0)
  }

  type RowMutex = Mutex<Row>

  type RowMutexTable = seq<RowMutex>

  predicate RowMutexTableInv(row_mutexes: RowMutexTable)
  {
    (forall i | 0 <= i < |row_mutexes| 
      :: row_mutexes[i].inv == ((row) => RowInv(i, row)))
  }

  datatype Variables = Variables(
    row_mutexes: RowMutexTable,
    allocator: CAP.AllocatorMutexTable)

  predicate Inv(v: Variables)
  {
    && CAP.Inv(v.allocator)
    && |v.row_mutexes| == FixedSize()
    && RowMutexTableInv(v.row_mutexes)
  
    // && SSM.Inv
  }

  datatype Splitted = Splitted(r':SSM.Variables, ri:SSM.Variables)

  function {:opaque} InitResoucePartial(i: nat): SSM.Variables
    requires i <= FixedSize()
  {
    var table := seq(FixedSize(), j => if j >= i then Some(Info(Empty, Free)) else None);
    SSM.Variables(table, Count.Variables(Capacity()), multiset{}, multiset{})
  }

  function Split(r:SSM.Variables, i:nat) : (splt:Splitted)
    requires i < FixedSize()
    requires r == InitResoucePartial(i)
    ensures add(splt.r', splt.ri) == r
  {
    var r' := InitResoucePartial(i+1);
    var ri := oneRowResource(i as nat, Info(Empty, Free), 0);
    reveal InitResoucePartial();
    Splitted(r', ri)
  }

  method init(glinear in_sv: SSM.Variables)
  returns (v: Variables, glinear out_sv: SSM.Variables)
  // requires SSM.Init(in_sv)
    ensures Inv(v)
    ensures out_sv == unit()
  {
    glinear var remaining_r := in_sv;
    var row_mutexes : RowMutexTable:= [];
    var i:uint32 := 0;

    assert remaining_r == InitResoucePartial(0) by {
      reveal InitResoucePartial();
    }

    while i < FixedSizeImpl()
      invariant i as int == |row_mutexes| <= FixedSize()
      invariant remaining_r == InitResoucePartial(i as nat)
      invariant RowMutexTableInv(row_mutexes)
    {
      ghost var splitted := Split(remaining_r, i as int);
      
      glinear var ri;
      remaining_r, ri := SSM.split(remaining_r, splitted.r', splitted.ri);

      var m := new_mutex<Row>(Row(Empty, ri), (row) => RowInv(i as nat, row));
      row_mutexes := row_mutexes + [m];
      i := i + 1;
    }

    reveal InitResoucePartial();
    assert remaining_r.table == unitTable();
    glinear var cap := declose(remaining_r);

    var allocator; glinear var remaining_cap;
    assert cap.value == Capacity();
    allocator, remaining_cap := CAP.init(cap);
    assert Count.Inv(Count.add(remaining_cap, remaining_cap));
    out_sv := enclose(remaining_cap);

    v := Variables.Variables(row_mutexes, allocator);
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

  function SubStub(s: SSM.Variables, t: SSM.Variables) : (s': SSM.Variables)
  requires SSM.le(t, s)
  ensures SSM.add(t, s') == s

  method acquireRow(v: Variables, index: uint32, glinear in_sv: SSM.Variables)
  returns (entry: Entry, glinear handle: MutexHandle<Row>, glinear out_sv: SSM.Variables)
    requires Inv(v)
    requires index < FixedSizeImpl();
    ensures handle.m == v.row_mutexes[index];
    ensures out_sv == add(in_sv, oneRowResource(index as nat, Info(entry, Free), 0))
  {
    linear var row;
    row, handle := v.row_mutexes[index].acquire();
    linear var Row(out_entry, row_r) := row;

    entry := out_entry;
    out_sv := SSM.join(in_sv, row_r);
  }

  method releaseRow(
    v: Variables,
    index: uint32,
    entry: Entry,
    glinear handle: MutexHandle<Row>,
    glinear in_sv: SSM.Variables,
    ghost exp_out_sv: SSM.Variables)
  returns (glinear out_sv: SSM.Variables)
    requires Inv(v);
    requires index < FixedSizeImpl();
    requires handle.m == v.row_mutexes[index];
    requires in_sv == add(exp_out_sv, oneRowResource(index as nat, Info(entry, Free), 0))
    ensures out_sv == exp_out_sv;
  {
    glinear var rmutex;
    ghost var right := oneRowResource(index as nat, Info(entry, Free), 0);
    out_sv, rmutex := SSM.split(in_sv, exp_out_sv, right);
    v.row_mutexes[index].release(Row(entry, rmutex), handle);
  }

  method acquireCapacity(v: Variables, thread_id: uint32, glinear in_sv: SSM.Variables)
  returns (
    count: uint32,
    bin_id: uint32,
    glinear cap_handle: MutexHandle<AllocatorBin>,
    glinear out_sv: SSM.Variables)

    decreases *
    requires Inv(v)
    requires in_sv.Variables?
    requires in_sv.insert_capacity.value == 0
    ensures bin_id < CAP.NumberOfBinsImpl()
    ensures cap_handle.m == v.allocator[bin_id]
    ensures out_sv.Variables?
    ensures out_sv == in_sv.(insert_capacity := Count.Variables(count as nat))
    ensures 0 < count <= CapacityImpl()
  {
    // thread_id is a hint for the bin we're supposed to use. 
    // bin_id is the actual place we found the capacity (in case we had to steal it from someone else) 
    bin_id := if thread_id >= CAP.NumberOfBinsImpl() then 0 else thread_id;
    linear var cap;
    cap, cap_handle := v.allocator[bin_id].acquire();

    while true
      invariant cap.count as nat == cap.resource.value <= Capacity()
      invariant Inv(v)
      invariant bin_id < CAP.NumberOfBinsImpl()
      invariant CAP.BinInv(cap)
      invariant cap_handle.m == v.allocator[bin_id]
      decreases *
    {
      if 0 < cap.count {
        break;
      }
      assert CAP.BinInv(cap);
      v.allocator[bin_id].release(cap, cap_handle);

      bin_id := bin_id + 1;
      bin_id := if bin_id >= CAP.NumberOfBinsImpl() then 0 else bin_id;

      cap, cap_handle := v.allocator[bin_id].acquire();
    }

    count := cap.count;
    linear var AllocatorBin(_, cap_r) := cap;
    out_sv := enclose(cap_r);
    out_sv := SSM.join(in_sv, out_sv);
  }

  method releaseCapacity(v: Variables,
    count: uint32,
    bin_id: uint32,
    glinear cap_handle: MutexHandle<AllocatorBin>,
    glinear in_sv: SSM.Variables,
    ghost exp_out_sv: SSM.Variables)
  returns (glinear out_sv: SSM.Variables)
    requires Inv(v);
    requires bin_id < CAP.NumberOfBinsImpl()
    requires cap_handle.m == v.allocator[bin_id];
    requires in_sv.Variables?
    requires in_sv == add(exp_out_sv, unit().(insert_capacity := Count.Variables(count as nat)));
    requires exp_out_sv.insert_capacity.value == 0;
    ensures out_sv == exp_out_sv;
  {
    glinear var rcap;
    assert in_sv.insert_capacity == Count.Variables(count as nat);

    glinear var mid_sv := resources_obey_inv(in_sv);
    out_sv, rcap := SSM.split(mid_sv, exp_out_sv, unit().(insert_capacity := Count.Variables(count as nat)));

    glinear var rcap' := declose(rcap);
    v.allocator[bin_id].release(AllocatorBin(count, rcap'), cap_handle);
  }

  method doQuery(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
  returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    decreases *
    requires Inv(v)
    requires input.QueryInput?
    requires IsInputResource(in_sv, rid, input)
    ensures out_sv == SSM.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key, hash_idx := input.key, hash(input.key);
    var slot_idx := hash_idx;

    var entry; glinear var handle; glinear var r;
    entry, handle, r := acquireRow(v, hash_idx, in_sv);

    ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Querying(rid, key)), 0);
    var step := ProcessQueryTicketStep(query_ticket);
    r := easy_transform_step(r, r', step);

    while true 
      invariant Inv(v);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Querying(rid, key)), 0);
      invariant handle.m == v.row_mutexes[slot_idx];
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
      next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);

      r' := twoRowsResource(slot_idx as nat, Info(entry, Free),
        next_slot_idx as nat, Info(next_entry, Querying(rid, key)), 0);
      r := easy_transform_step(r, r', step);

      ghost var left := oneRowResource(next_slot_idx as nat, Info(next_entry, Querying(rid, key)), 0);
      r := releaseRow(v, slot_idx, entry, handle, r, left);

      slot_idx, entry, handle := next_slot_idx, next_entry, next_handle;
    }
    
    // assert step.QueryNotFoundStep? || step.QueryDoneStep?;
    r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(entry, Free)), Count.Variables(0), multiset{}, multiset{Stub(rid, output)}); 
    r := easy_transform_step(r, r', step);

    out_sv := releaseRow(v, slot_idx, entry, handle, r, SSM.output_stub(rid, output));
  }

  method doInsert(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
  returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    requires Inv(v)
    requires input.InsertInput?
    requires IsInputResource(in_sv, rid, input)
    ensures out_sv == SSM.output_stub(rid, output)
    decreases *
  {
    var insert_ticket := Ticket(rid, input);
    var key, inital_key := input.key, input.key;
    var kv := KV(key, input.value);
    output := MapIfc.InsertOutput(true);

    var hash_idx := hash(key);
    var slot_idx := hash_idx;

    glinear var cap_handle; var bin_id; var count; glinear var r;
    count, bin_id, cap_handle, r := acquireCapacity(v, thread_id, in_sv);

    var entry; glinear var handle;
    entry, handle, r := acquireRow(v, slot_idx, r);

    count := count - 1;

    var step := ProcessInsertTicketStep(insert_ticket);
    ghost var r' := ProcessInsertTicketTransition(r, insert_ticket);
    r := easy_transform_step(r, r', step);

    while true 
      invariant Inv(v);
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Inserting(rid, kv, inital_key)), count as nat)
      invariant kv.key == key
      invariant hash_idx == hash(key)
      invariant handle.m == v.row_mutexes[slot_idx];
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
      next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);

      if step.InsertSwapStep? {
        entry := Full(kv);
        kv := new_kv;
        key := new_kv.key;
      }
  
      r' := twoRowsResource(slot_idx as nat, Info(entry, Free),
        next_slot_idx as nat, Info(next_entry, Inserting(rid, kv, inital_key)), count as nat);
      r := easy_transform_step(r, r', step);

      ghost var expected := oneRowResource(next_slot_idx as nat, Info(next_entry, Inserting(rid, kv, inital_key)), count as nat);
      r := releaseRow(v, slot_idx, entry, handle, r, expected);

      slot_idx, entry, handle := next_slot_idx, next_entry, next_handle;
      hash_idx := hash(key);
    }

    // assert step.InsertDoneStep? || step.InsertUpdateStep?;
    count := if step.InsertDoneStep? then count else count + 1;
    r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(Full(kv), Free)),
      Count.Variables(count as nat),
      multiset{}, multiset{Stub(rid, output)});

    r := easy_transform_step(r, r', step);
    ghost var expected := SSM.output_stub(rid, output).(insert_capacity := Count.Variables(count as nat));
    r := releaseRow(v, slot_idx, Full(kv), handle, r, expected);

    expected := SSM.output_stub(rid, output);
    out_sv := releaseCapacity(v, count, bin_id, cap_handle, r, expected);
  }

  method doRemoveFound(v: Variables, rid: int, 
    slot_idx: uint32,
    hash_idx: uint32,
    inital_key: Key,
    entry: SSM.Entry,
    thread_id: uint32,
    glinear handle: MutexHandle<Row>,
    glinear in_sv: SSM.Variables)
  
    returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    decreases *
    requires Inv(v)
    requires 0 <= slot_idx < FixedSizeImpl()
    requires 0 <= hash_idx < FixedSizeImpl()
    requires in_sv == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, inital_key)), 0);
    requires entry.Full? && entry.kv.key == inital_key
    requires hash(inital_key) == hash_idx
    requires handle.m == v.row_mutexes[slot_idx]
    ensures out_sv == SSM.output_stub(rid, output)
  {
    var found_value := entry.kv.val;

    var slot_idx := slot_idx;
    var next_slot_idx := getNextIndex(slot_idx);

    glinear var handle := handle;
    glinear var next_handle;
    glinear var r;

    var next_entry;
    next_entry, next_handle, r := acquireRow(v, next_slot_idx, in_sv);

    var step := RemoveFoundItStep(slot_idx as nat);
    var r' := twoRowsResource(
        slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
        next_slot_idx as nat, Info(next_entry, Free),
        0);
    r := easy_transform_step(r, r', step);

    while true
      invariant Inv(v);
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant r == twoRowsResource(
        slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
        NextPos(slot_idx as nat), Info(next_entry, Free),
        0)
      invariant handle.m == v.row_mutexes[slot_idx]
      invariant next_handle.m == v.row_mutexes[NextPos(slot_idx as nat)]
      decreases *
    {
      next_slot_idx := getNextIndex(slot_idx);

      if next_entry.Empty? || (next_entry.Full? && hash(next_entry.kv.key) == next_slot_idx) {
        assert DoneTidying(r, slot_idx as nat);
        break;
      }

      ghost var r' := twoRowsResource(
        slot_idx as nat, Info(next_entry, Free),
        next_slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
        0);
      r := easy_transform_step(r, r', RemoveTidyStep(slot_idx as nat));

      ghost var left := oneRowResource(next_slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)), 0);
      r :=  releaseRow(v, slot_idx, next_entry, handle, r, left);

      slot_idx := next_slot_idx;
      next_slot_idx := getNextIndex(slot_idx);
      handle := next_handle;

      next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);
    }

    assert DoneTidying(r, slot_idx as nat);

    next_slot_idx := getNextIndex(slot_idx);
    output := MapIfc.RemoveOutput(true);

    var count; glinear var cap_handle; var bin_id;
    count, bin_id, cap_handle, r := acquireCapacity(v, thread_id, r);

    r' := SSM.Variables(
      twoRowsTable(slot_idx as nat, Info(Empty, Free), next_slot_idx as nat, Info(next_entry, Free)),
      Count.Variables(count as nat + 1),
      multiset{},
      multiset{ Stub(rid, output) }
    );

    step := RemoveDoneStep(slot_idx as nat);
    r := easy_transform_step(r, r', step);

    ghost var expected := SSM.Variables(
      oneRowTable(next_slot_idx as nat, Info(next_entry, Free)),
      Count.Variables(count as nat + 1),
      multiset{},
      multiset{ Stub(rid, output) });
    r := releaseRow(v, slot_idx, Empty, handle, r, expected);

    expected := SSM.output_stub(rid, output).(insert_capacity := Count.Variables(count as nat + 1));
    r := releaseRow(v, next_slot_idx, next_entry, next_handle, r, expected);

    expected := SSM.output_stub(rid, output);
    out_sv := releaseCapacity(v, count + 1, bin_id, cap_handle, r, expected);
  }

  method doRemove(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
    returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    decreases *

    requires Inv(v)
    requires input.RemoveInput?
    requires IsInputResource(in_sv, rid, input)
    ensures out_sv == SSM.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key := input.key;
    var hash_idx := hash(key); var slot_idx := hash_idx;

    linear var row; glinear var handle;
    row, handle := v.row_mutexes[slot_idx].acquire();

    linear var Row(entry, row_r) := row;
    glinear var r := SSM.join(in_sv, row_r);

    var next_slot_idx :uint32;
    glinear var rmutex;

    glinear var r' := oneRowResource(hash_idx as nat, Info(entry, Removing(rid, key)), 0);
    var step : Step := ProcessRemoveTicketStep(query_ticket);
    r := easy_transform_step(r, r', step);

    while true 
      invariant Inv(v);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, key)), 0)
      invariant step.RemoveNotFoundStep? ==> 
        (entry.Full? && shouldHashGoBefore(hash_idx, hash(entry.kv.key), slot_idx))
      invariant step.RemoveTidyStep? ==> (
        && TidyEnabled(r, slot_idx as nat)
        && KnowRowIsFree(r, NextPos(slot_idx as nat)))
      invariant handle.m == v.row_mutexes[slot_idx]
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

      linear var next_row; glinear var next_handle;
      next_row, next_handle := v.row_mutexes[next_slot_idx].acquire();
      linear var Row(next_entry, next_row_r) := next_row;
      r := SSM.join(r, next_row_r);

      r' := twoRowsResource(slot_idx as nat, Info(entry, Free), next_slot_idx as nat, Info(next_entry, Removing(rid, key)), 0);
      r := easy_transform_step(r, r', step);

      ghost var left := oneRowResource(next_slot_idx as nat, Info(next_entry, Removing(rid, key)), 0);
      ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);
      r, rmutex := SSM.split(r, left, right);
      v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);

      slot_idx := next_slot_idx;
      entry := next_entry;
      handle := next_handle;
    }

    if step.RemoveNotFoundStep? {
      output := MapIfc.RemoveOutput(false);
      r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(entry, Free)), Count.Variables(0), multiset{}, multiset{Stub(rid, output)}); 
      r := easy_transform_step(r, r', step);
      ghost var left := SSM.output_stub(rid, output);
      ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);
      r, rmutex := SSM.split(r, left, right);
      v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);
    } else {
      output, r := doRemoveFound(v, rid, slot_idx, hash_idx, key, entry, thread_id, handle, r);
    }
    out_sv := r;
  }

  method call(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables, thread_id: uint32)
    returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    decreases *
  // requires Inv(o)
  // requires ticket == SSM.input_ticket(rid, key)
    ensures out_sv == SSM.output_stub(rid, output)
  {
    // Find the ticket.
    assert |in_sv.tickets| == 1;
    var the_ticket :| the_ticket in in_sv.tickets;

    if the_ticket.input.QueryInput? {
      output, out_sv := doQuery(v, input, rid, in_sv);
    } else if the_ticket.input.InsertInput? {
      output, out_sv := doInsert(v, input, rid, thread_id, in_sv);
    } else if the_ticket.input.RemoveInput? {
      output, out_sv := doRemove(v, input, rid, thread_id, in_sv);
    } else {
      out_sv := in_sv;
      assert false;
    }
  }

  // lemma NewTicket_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, input: Ifc.Input)
  // {
  // }
  
  // lemma ReturnStub_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, output: Ifc.Output)
  // {
  // }
  
}
