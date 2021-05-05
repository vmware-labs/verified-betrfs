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

  linear datatype Row = Row(
    entry: SSM.Entry,
    glinear resource: SSM.Variables)

  type RowMutex = Mutex<Row>
  type RowMutexTable = seq<RowMutex>

  datatype Variables = Variables(row_mutexes: RowMutexTable, allocator: CAP.AllocatorMutexTable)

  function RowInv(index: nat, row: Row): bool
  {
    //&& Valid(row.resource)  // valid is tucked into predicate type
    && 0 <= index as nat < FixedSize()
    && row.resource == oneRowResource(index as nat, Info(row.entry, Free), 0)
  }

  predicate Inv(v: Variables) {
    && CAP.Inv(v.allocator)
    && |v.row_mutexes| == SSM.FixedSize()
    && (forall i | 0 <= i < FixedSize()
      :: v.row_mutexes[i].inv == ((row) => RowInv(i, row)))
  }

  datatype Splitted = Splitted(r':SSM.Variables, ri:SSM.Variables)

  function Split(r:SSM.Variables, i:nat) : Splitted
    requires r.Variables?;
    requires r.tickets == multiset{}
    requires r.stubs == multiset{}
  {
    var r' := SSM.Variables(seq(|r.table|, (j) requires 0 <= j < |r.table| => if j!=i then r.table[j] else None), r.insert_capacity, multiset{}, multiset{});
    var ri := SSM.Variables(seq(|r.table|, (j) requires 0 <= j < |r.table| => if j==i then r.table[j] else None), Count.Variables(0), multiset{}, multiset{});
    Splitted(r', ri)
  }

  method init(glinear in_sv: SSM.Variables)
  returns (v: Variables, glinear out_sv: SSM.Variables)
  // requires SSM.Init(i)
  ensures Inv(v)
  ensures out_sv == unit()
  {
    glinear var remaining_r := in_sv;
    var row_mutexes : RowMutexTable:= [];
    var i:uint32 := 0;
    while i < FixedSizeImpl()
      invariant i as int == |row_mutexes| <= FixedSize()
      invariant forall j:nat | j<i as int :: && row_mutexes[j].inv == (row) => RowInv(j, row)
      invariant remaining_r.Variables?
      invariant remaining_r.tickets == multiset{}
      invariant remaining_r.stubs == multiset{} 
      invariant forall k:nat | k < i as int :: remaining_r.table[k].None?
      invariant forall l:nat | i as int <= l < |remaining_r.table| :: remaining_r.table[l] == Some(Info(Empty, Free))
      invariant remaining_r.insert_capacity.value == Capacity()
    {
      ghost var splitted := Split(remaining_r, i as int);
      glinear var ri;
      remaining_r, ri := SSM.split(remaining_r, splitted.r', splitted.ri);
      var m := new_mutex<Row>(Row(Empty, ri), (row) => RowInv(i as nat, row));
      row_mutexes := row_mutexes + [m];
      i := i + 1;
    }

    assert remaining_r.table == unitTable();
    glinear var insert_capacity;
    out_sv, insert_capacity := declose(remaining_r);
    init(insert_capacity);
  }

  // predicate method shouldHashGoBefore(search_h: uint32, slot_h: uint32, slot_idx: uint32) 
  //   ensures shouldHashGoBefore(search_h, slot_h, slot_idx) == ShouldHashGoBefore(search_h as int, slot_h as int, slot_idx as int)
  // {
  //   || search_h < slot_h <= slot_idx // normal case
  //   || slot_h <= slot_idx < search_h // search_h wraps around the end of array
  //   || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  // }

  // function method getNextIndex(slot_idx: uint32) : uint32
  //   requires slot_idx < FixedSizeImpl()
  // {
  //   if slot_idx == FixedSizeImpl() - 1 then 0 else slot_idx + 1
  // }

  // function DistanceToSlot(src: uint32, dst: uint32) : nat
  //   requires src < FixedSizeImpl()
  //   requires dst < FixedSizeImpl()
  // {
  //   if src >= dst
  //     then (dst as int - src as int + FixedSize() as int)
  //     else (dst as int - src as int)
  // }

  // method doQuery(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
  // returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *
  //   requires Inv(v)
  //   requires input.QueryInput?
  //   requires isInputResource(in_sv, rid, input)
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   var query_ticket := Ticket(rid, input);
  //   var key := input.key;
  //   var hash_idx := hash(key);
  //   var slot_idx := hash_idx;

  //   linear var row; glinear var handle;
  //   row, handle := v.row_mutexes[slot_idx].acquire();
  //   linear var Row(entry, row_r) := row;
  //   glinear var r := SSM.join(in_sv, row_r);

  //   ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Querying(rid, key)), 0);
  //   assert ProcessQueryTicket(r, r', query_ticket);

  //   var step := ProcessQueryTicketStep(query_ticket);
  //   r := easy_transform_step(r, r', step);

  //   while true 
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl();
  //     invariant r == oneRowResource(slot_idx as nat, Info(entry, Querying(rid, key)), 0);
  //     invariant handle.m == v.row_mutexes[slot_idx];
  //     decreases *
  //   {
  //     var slot_idx' := getNextIndex(slot_idx);

  //     match entry {
  //       case Empty => {
  //         output := MapIfc.QueryOutput(NotFound);
  //         step := QueryNotFoundStep(slot_idx as nat);
  //       }
  //       case Full(KV(entry_key, value)) => {
  //         if entry_key == key {
  //           step := QueryDoneStep(slot_idx as nat);
  //           output := MapIfc.QueryOutput(Found(value));
  //         } else {
  //           var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);

  //           if !should_go_before {
  //             step := QuerySkipStep(slot_idx as nat);
  //           } else {
  //             output := MapIfc.QueryOutput(NotFound);
  //             step := QueryNotFoundStep(slot_idx as nat);
  //           }
  //         }
  //       }
  //     }

  //     if !step.QuerySkipStep? {
  //       // this test is required for termination, but is not enforced by verification
  //       // because we are using decreases *
  //       break;
  //     }

  //     // if slot_idx' == hash_idx {
  //     //   QueryUnreachableState(r, slot_idx as nat);
  //     //   break;
  //     // }

  //     linear var next_row; glinear var next_handle;
  //     next_row, next_handle := v.row_mutexes[slot_idx'].acquire();
  //     linear var Row(next_entry, next_row_r) := next_row;
  //     r := SSM.join(r, next_row_r);

  //     r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Querying(rid, key)), 0);
  //     r := easy_transform_step(r, r', step);

  //     glinear var rmutex;
  //     ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Querying(rid, key)), 0);
  //     ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);
  //     r, rmutex := SSM.split(r, left, right);
  //     v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);

  //     slot_idx := slot_idx';
  //     entry := next_entry;
  //     handle := next_handle;
  //   }
    
  //   // assert step.QueryNotFoundStep? || step.QueryDoneStep?;
  //   r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(entry, Free)), 0, multiset{}, multiset{Stub(rid, output)}); 
  //   r := easy_transform_step(r, r', step);

  //   glinear var rmutex;
  //   r, rmutex := SSM.split(r, 
  //     SSM.output_stub(rid, output), 
  //     oneRowResource(slot_idx as nat, Info(entry, Free), 0));
  //   v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);

  //   out_sv := r;
  // }

  // method acquireCapacity(v: Variables, thread_id: uint32)
  // returns (linear cap: AllocatorBin, glinear cap_handle: MutexHandle<AllocatorBin>, tid: uint32)
  //   decreases *
  //   requires Inv(v)
  //   ensures cap.resource == unit().(insert_capacity := cap.count as nat)
  //   ensures 0 < cap.count
  //   ensures tid < CAP.BinCountImpl()
  //   ensures cap_handle.m == v.allocator[tid]
  // {
  //   // thread_id is a hint for the bin we're supposed to use. 
  //   // tid is the actual place we found the capacity (in case we had to steal it from someone else) 
  //   tid := if thread_id >= CAP.BinCountImpl() then 0 else thread_id;
  //   cap, cap_handle := v.allocator[tid].acquire();

  //   while true
  //     invariant tid < CAP.BinCountImpl()
  //     invariant cap.resource == unit().(insert_capacity := cap.count as nat)
  //     invariant cap_handle.m == v.allocator[tid]
  //     decreases *
  //   {
  //     if 0 < cap.count {
  //       break;
  //     }

  //     // assert exists s' :: TableQuantityInv(add(s, s'))
  //     assert CAP.BinInv(cap);
  //     v.allocator[tid].release(cap, cap_handle);

  //     tid := tid + 1;
  //     tid := if tid >= CAP.BinCountImpl() then 0 else tid;

  //     cap, cap_handle := v.allocator[tid].acquire();
  //   }
  // }

  // method doInsert(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
  // returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   requires Inv(v)
  //   requires input.InsertInput?
  //   requires isInputResource(in_sv, rid, input)
  //   ensures out_sv == SSM.output_stub(rid, output)
  //   decreases *
  // {
  //   var allocator := v.allocator;

  //   var query_ticket := Ticket(rid, input);
  //   var key, inital_key := input.key, input.key;
  //   var kv := KV(key, input.value);
  //   output := MapIfc.InsertOutput(true);

  //   var hash_idx := hash(key);
  //   var initial_hash_idx := hash_idx;
  //   var slot_idx := hash_idx;

  //   linear var cap; glinear var cap_handle; var tid;
  //   cap, cap_handle, tid := acquireCapacity(v, thread_id);
  //   linear var AllocatorBin(count, cap_r) := cap;
  //   glinear var r := SSM.join(in_sv, cap_r);

  //   linear var row; glinear var handle;
  //   row, handle := v.row_mutexes[slot_idx].acquire();
  //   linear var Row(entry, row_r) := row;
  //   r := SSM.join(r, row_r);

  //   count := count - 1;

  //   var step := ProcessInsertTicketStep(query_ticket);
  //   ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Inserting(rid, kv, inital_key)), count as nat);
  //   r := easy_transform_step(r, r', step);
  //   glinear var rmutex;

  //   while true 
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl()
  //     invariant r == oneRowResource(slot_idx as nat, Info(entry, Inserting(rid, kv, inital_key)), count as nat)
  //     invariant kv.key == key
  //     invariant hash_idx == hash(key)
  //     invariant handle.m == v.row_mutexes[slot_idx];
  //     decreases *
  //   {
  //     var slot_idx' := getNextIndex(slot_idx);
  //     var new_kv;

  //     match entry {
  //       case Empty => {
  //         step := InsertDoneStep(slot_idx as nat);
  //       }
  //       case Full(KV(entry_key, value)) => {
  //         new_kv := KV(entry_key, value);
  //         if entry_key == key {
  //           step := InsertUpdateStep(slot_idx as nat);
  //         } else {
  //           var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);
  //           if !should_go_before {
  //             step := InsertSkipStep(slot_idx as nat);
  //           } else {
  //             step := InsertSwapStep(slot_idx as nat);
  //           }
  //         }
  //       }
  //     }

  //     if step.InsertDoneStep? || step.InsertUpdateStep? {
  //       break;
  //     }

  //     linear var next_row; glinear var next_handle;
  //     next_row, next_handle := v.row_mutexes[slot_idx'].acquire();
  //     linear var Row(next_entry, next_row_r) := next_row;
  //     r := SSM.join(r, next_row_r);

  //     if step.InsertSwapStep? {
  //       entry := Full(kv);
  //       kv := new_kv;
  //       key := new_kv.key;
  //     }
  
  //     r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Inserting(rid, kv, inital_key)), count as nat);
  //     r := easy_transform_step(r, r', step);

  //     ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Inserting(rid, kv, inital_key)), count as nat);
  //     ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);

  //     r, rmutex := SSM.split(r, left, right);
  //     v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);

  //     slot_idx := slot_idx';
  //     entry := next_entry;
  //     hash_idx := hash(key);
  //     handle := next_handle;
  //   }

  //   // assert step.InsertDoneStep? || step.InsertUpdateStep?;
  //   count := if step.InsertDoneStep? then count else count + 1;
  //   r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(Full(kv), Free)), count as nat, multiset{}, multiset{Stub(rid, output)});
  //   r := easy_transform_step(r, r', step);

  //   r, rmutex := SSM.split(r, 
  //     SSM.output_stub(rid, output).(insert_capacity := count as nat), 
  //     oneRowResource(slot_idx as nat, Info(Full(kv), Free), 0));
  //   v.row_mutexes[slot_idx].release(Row(Full(kv), rmutex), handle);

  //   glinear var rcap;
  //   r, rcap := SSM.split(r,
  //     SSM.output_stub(rid, output), 
  //     unit().(insert_capacity := count as nat));

  //   assert CAP.BinInv(AllocatorBin(count, rcap)); // ha ha ha
  //   allocator[tid].release(AllocatorBin(count, rcap), cap_handle);

  //   out_sv := r;
  // }

  // method doRemoveFound(v: Variables, rid: int, 
  //   slot_idx: uint32,
  //   hash_idx: uint32,
  //   inital_key: Key,
  //   entry: SSM.Entry,
  //   thread_id: uint32,
  //   glinear handle: MutexHandle<Row>,
  //   glinear r: SSM.Variables)
  
  //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *
  //   requires Inv(v)
  //   requires 0 <= slot_idx < FixedSizeImpl()
  //   requires 0 <= hash_idx < FixedSizeImpl()
  //   requires r == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, inital_key)), 0);
  //   requires entry.Full? && entry.kv.key == inital_key
  //   requires hash(inital_key) == hash_idx
  //   requires handle.m == v.row_mutexes[slot_idx]
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   var found_value := entry.kv.val;
  //   // var allocator := v.allocator;

  //   var slot_idx := slot_idx;
  //   var slot_idx' := getNextIndex(slot_idx);

  //   glinear var handle := handle;
  //   glinear var rmutex;

  //   linear var next_row; glinear var next_handle;
  //   next_row, next_handle := v.row_mutexes[slot_idx'].acquire();
  //   linear var Row(next_entry, next_row_r) := next_row;
  //   glinear var r := SSM.join(r, next_row_r);

  //   var step := RemoveFoundItStep(slot_idx as nat);
  //   var r' := twoRowsResource(
  //       slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
  //       slot_idx' as nat, Info(next_entry, Free),
  //       0);
  //   r := easy_transform_step(r, r', step);

  //   while true
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl()
  //     invariant r == twoRowsResource(
  //       slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
  //       NextPos(slot_idx as nat), Info(next_entry, Free),
  //       0)
  //     invariant handle.m == v.row_mutexes[slot_idx]
  //     invariant next_handle.m == v.row_mutexes[NextPos(slot_idx as nat)]
  //     decreases *
  //   {
  //     slot_idx' := getNextIndex(slot_idx);

  //     if next_entry.Empty? || (next_entry.Full? && hash(next_entry.kv.key) == slot_idx') {
  //       assert DoneTidying(r, slot_idx as nat);
  //       break;
  //     }

  //     ghost var r' := twoRowsResource(
  //       slot_idx as nat, Info(next_entry, Free),
  //       slot_idx' as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)),
  //       0);
  //     r := easy_transform_step(r, r', RemoveTidyStep(slot_idx as nat));

  //     ghost var left := oneRowResource(slot_idx' as nat, Info(Empty, RemoveTidying(rid, inital_key, found_value)), 0);
  //     ghost var right := oneRowResource(slot_idx as nat, Info(next_entry, Free), 0);

  //     r, rmutex := SSM.split(r, left, right);
  //     v.row_mutexes[slot_idx].release(Row(next_entry, rmutex), handle);

  //     slot_idx := slot_idx';
  //     slot_idx' := getNextIndex(slot_idx);
  //     handle := next_handle;

  //     next_row, next_handle := v.row_mutexes[slot_idx'].acquire();
  //     linear var Row(next_entry', next_row_r) := next_row;
  //     next_entry := next_entry';
  //     r := SSM.join(r, next_row_r);
  //   }

  //   assert DoneTidying(r, slot_idx as nat);

  //   slot_idx' := getNextIndex(slot_idx);
  //   output := MapIfc.RemoveOutput(true);

  //   linear var cap; glinear var cap_handle; var tid;
  //   cap, cap_handle, tid := acquireCapacity(v, thread_id);
  //   linear var AllocatorBin(count, cap_r) := cap;
  //   r := SSM.join(r, cap_r);

  //   r' := SSM.Variables(
  //     twoRowsTable(slot_idx as nat, Info(Empty, Free), slot_idx' as nat, Info(next_entry, Free)),
  //     count as nat + 1,
  //     multiset{},
  //     multiset{ Stub(rid, output) }
  //   );

  //   step := RemoveDoneStep(slot_idx as nat);
  //   r := easy_transform_step(r, r', step);

  //   ghost var left := SSM.Variables(
  //     oneRowTable(slot_idx' as nat, Info(next_entry, Free)),
  //     count as nat + 1,
  //     multiset{},
  //     multiset{ Stub(rid, output) });
  //   ghost var right := oneRowResource(slot_idx as nat, Info(Empty, Free), 0);

  //   r, rmutex := SSM.split(r, left, right);
  //   v.row_mutexes[slot_idx].release(Row(Empty, rmutex), handle);

  //   r, rmutex := SSM.split(r, 
  //     SSM.output_stub(rid, output).(insert_capacity := count as nat + 1), 
  //     oneRowResource(slot_idx' as nat, Info(next_entry, Free), 0));
  //   v.row_mutexes[slot_idx'].release(Row(next_entry, rmutex), next_handle);

  //   r, cap_r := SSM.split(r,
  //     SSM.output_stub(rid, output), 
  //     unit().(insert_capacity := count as nat + 1));
  
  //   assert CAP.BinInv(AllocatorBin(count as nat +1, cap_r)); // ha ha ha
  //   v.allocator[tid].release(AllocatorBin(count+1, cap_r), cap_handle);

  //   out_sv := r;
  // }

  // method doRemove(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
  //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *

  //   requires Inv(v)
  //   requires input.RemoveInput?
  //   requires isInputResource(in_sv, rid, input)
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   var query_ticket := Ticket(rid, input);
  //   var key := input.key;
  //   var hash_idx := hash(key); var slot_idx := hash_idx;

  //   linear var row; glinear var handle;
  //   row, handle := v.row_mutexes[slot_idx].acquire();

  //   linear var Row(entry, row_r) := row;
  //   glinear var r := SSM.join(in_sv, row_r);

  //   var slot_idx' :uint32;
  //   glinear var rmutex;

  //   glinear var r' := oneRowResource(hash_idx as nat, Info(entry, Removing(rid, key)), 0);
  //   var step : Step := ProcessRemoveTicketStep(query_ticket);
  //   r := easy_transform_step(r, r', step);

  //   while true 
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl();
  //     invariant r == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, key)), 0)
  //     invariant step.RemoveNotFoundStep? ==> 
  //       (entry.Full? && shouldHashGoBefore(hash_idx, hash(entry.kv.key), slot_idx))
  //     invariant step.RemoveTidyStep? ==> (
  //       && TidyEnabled(r, slot_idx as nat)
  //       && KnowRowIsFree(r, NextPos(slot_idx as nat)))
  //     invariant handle.m == v.row_mutexes[slot_idx]
  //     decreases *
  //   {
  //     var slot_idx' := getNextIndex(slot_idx);

  //     match entry {
  //       case Empty => {
  //         step := RemoveNotFoundStep(slot_idx as nat);
  //       }
  //       case Full(KV(entry_key, value)) => {
  //         if entry_key == key {
  //           step := RemoveFoundItStep(slot_idx as nat);
  //         } else {
  //           var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);

  //           if !should_go_before {
  //             step := RemoveSkipStep(slot_idx as nat);
  //           } else {
  //             step := RemoveNotFoundStep(slot_idx as nat);
  //           }
  //         }
  //       }
  //     }

  //     if step.RemoveNotFoundStep? || step.RemoveFoundItStep? {
  //       break;
  //     }

  //     linear var next_row; glinear var next_handle;
  //     next_row, next_handle := v.row_mutexes[slot_idx'].acquire();
  //     linear var Row(next_entry, next_row_r) := next_row;
  //     r := SSM.join(r, next_row_r);

  //     r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Removing(rid, key)), 0);
  //     r := easy_transform_step(r, r', step);

  //     ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Removing(rid, key)), 0);
  //     ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);
  //     r, rmutex := SSM.split(r, left, right);
  //     v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);

  //     slot_idx := slot_idx';
  //     entry := next_entry;
  //     handle := next_handle;
  //   }

  //   if step.RemoveNotFoundStep? {
  //     output := MapIfc.RemoveOutput(false);
  //     r' := SSM.Variables(oneRowTable(slot_idx as nat, Info(entry, Free)), 0, multiset{}, multiset{Stub(rid, output)}); 
  //     r := easy_transform_step(r, r', step);
  //     ghost var left := SSM.output_stub(rid, output);
  //     ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free), 0);
  //     r, rmutex := SSM.split(r, left, right);
  //     v.row_mutexes[slot_idx].release(Row(entry, rmutex), handle);
  //   } else {
  //     output, r := doRemoveFound(v, rid, slot_idx, hash_idx, key, entry, thread_id, handle, r);
  //   }

  //   out_sv := r;
  // }

  // method call(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables, thread_id: uint32)
  //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *
  // // requires Inv(o)
  // // requires ticket == SSM.input_ticket(rid, key)
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   // Find the ticket.
  //   assert |in_sv.tickets| == 1;
  //   var the_ticket :| the_ticket in in_sv.tickets;

  //   if the_ticket.input.QueryInput? {
  //     output, out_sv := doQuery(v, input, rid, in_sv);
  //   } else if the_ticket.input.InsertInput? {
  //     output, out_sv := doInsert(v, input, rid, thread_id, in_sv);
  //   } else if the_ticket.input.RemoveInput? {
  //     output, out_sv := doRemove(v, input, rid, thread_id, in_sv);
  //   } else {
  //     out_sv := in_sv;
  //     assert false;
  //   }
  // }

  // lemma NewTicket_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, input: Ifc.Input)
  // {
  // }
  
  // lemma ReturnStub_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, output: Ifc.Output)
  // {
  // }
  
}
