include "../common/CapacityAllocator.i.dfy"
include "../common/ConcurrencyTools.s.dfy"
include "ShardedHashTable.i.dfy"
include "../common/VerificationObligation.s.dfy"
include "GhostLinearSequence.i.dfy"


module Impl refines VerificationObligation {
  import opened Options
  import SSM = ShardedHashTable
  import opened ShardedHashTable
  import opened KeyValueType
  import opened Mutexes
  import opened CapacityAllocatorTypes
  import CAP = CapacityAllocator
  import opened Limits
  import opened CircularTable
  import opened CircularRange
  import opened GhostLinearSequence_s
  import opened GhostLinearSequence_i

  // function method glinear_seq_set<A>(s1: seq<A>, i: nat, glinear a: A): (s2: seq<A>) 

  linear datatype Row = Row(
    entry: Entry,
    glinear resource: SSM.Variables)

  function RowInv(i: Index, row: Row): bool
  {
    && row.resource == OneRowResource(i, row.entry, 0) 
  }

  type RowMutex = Mutex<Row>

  type RowMutexTable = seq<RowMutex>

  type Handle = MutexHandle<Row>

  predicate RowMutexTableInv(row_mutexes: RowMutexTable)
    requires |row_mutexes| <= FixedSize()
  {
    (forall i | 0 <= i < |row_mutexes|
      :: row_mutexes[i].inv == ((row) => RowInv(i, row)))
  }

  linear datatype Variables = Variables(
    row_mutexes: RowMutexTable,
    glinear handles: glseq<Handle>,
    allocator: CAP.AllocatorMutexTable)
  {
    predicate HandlesInv()
      requires |row_mutexes| == FixedSize()
    {
      && |handles| == FixedSize()
      // if I have the handle, it corresponds to the row mutex
      && (forall i: Index | i in handles
        :: handles[i].m == row_mutexes[i])
    }

    predicate Inv()
    {
      && CAP.Inv(allocator)
      && |row_mutexes| == FixedSize()
      && RowMutexTableInv(row_mutexes)
      && HandlesInv()
    }

    predicate HasHandle(index: Index)
      requires Inv()
    {
      index in handles
    }

    linear inout method acquireRow(index: Index, glinear in_sv: SSM.Variables)
      returns (entry: Entry, glinear out_sv: SSM.Variables)

      requires old_self.Inv()
      requires !old_self.HasHandle(index)
      requires in_sv.Variables?
      requires in_sv.table[index] == None

      ensures self.Inv()
      ensures self.HasHandle(index)
      ensures forall i: Index | i != index ::
        old_self.HasHandle(i) <==> self.HasHandle(i)
      ensures out_sv == in_sv.(table := in_sv.table[index := Some(entry)]);
    {
      linear var row; glinear var handle: Handle;
      row, handle := self.row_mutexes[index].acquire();

      linear var Row(out_entry, row_r) := row;
      entry := out_entry;

      out_sv := SSM.join(in_sv, row_r);
      assert out_sv.Variables?;

      assert handle.m == self.row_mutexes[index];
      lseq_give_inout(inout self.handles, index, handle);

      assert glseq_has(self.handles) == glseq_has(old_self.handles)[index := true];
    }

    linear inout method releaseRow(index: Index, entry: Entry, glinear in_sv: SSM.Variables)
      returns (glinear out_sv: SSM.Variables)
  
      requires old_self.Inv()
      requires old_self.HasHandle(index)
      requires in_sv.Variables?
      requires in_sv.table[index] == Some(entry)
            
      ensures self.Inv()
      ensures !self.HasHandle(index)
      ensures forall i: Index | i != index ::
        old_self.HasHandle(i) <==> self.HasHandle(i)
      ensures out_sv == in_sv.(table := in_sv.table[index := None]);
    {
      glinear var rmutex;
      ghost var left := in_sv.(table := in_sv.table[index := None]);
      ghost var right := OneRowResource(index, entry, 0);
      out_sv, rmutex := SSM.split(in_sv, left, right);
      
      glinear var handle := lseq_take_inout(inout self.handles, index);
      self.row_mutexes[index].release(Row(entry, rmutex), handle);
    }

    // method acquireCapacity(thread_id: uint32, glinear in_sv: SSM.Variables)
    // returns (
    //   count: uint32,
    //   bin_id: uint32,
    //   glinear cap_handle: MutexHandle<AllocatorBin>,
    //   glinear out_sv: SSM.Variables)

    //   decreases *
    //   requires Inv()
    //   requires in_sv.Variables?
    //   requires in_sv.insert_capacity.value == 0
    //   ensures bin_id < CAP.NumberOfBinsImpl()
    //   ensures cap_handle.m == allocator[bin_id]
    //   ensures out_sv.Variables?
    //   ensures out_sv == in_sv.(insert_capacity := Count.Variables(count as nat))
    //   ensures 0 < count <= CapacityImpl()
    // {
    //   // thread_id is a hint for the bin we're supposed to use. 
    //   // bin_id is the actual place we found the capacity (in case we had to steal it from someone else) 
    //   bin_id := if thread_id >= CAP.NumberOfBinsImpl() then 0 else thread_id;
    //   linear var cap;
    //   cap, cap_handle := allocator[bin_id].acquire();

    //   while true
    //     invariant cap.count as nat == cap.resource.value <= Capacity()
    //     invariant Inv()
    //     invariant bin_id < CAP.NumberOfBinsImpl()
    //     invariant CAP.BinInv(cap)
    //     invariant cap_handle.m == allocator[bin_id]
    //     decreases *
    //   {
    //     if 0 < cap.count {
    //       break;
    //     }
    //     assert CAP.BinInv(cap);
    //     allocator[bin_id].release(cap, cap_handle);

    //     bin_id := bin_id + 1;
    //     bin_id := if bin_id >= CAP.NumberOfBinsImpl() then 0 else bin_id;

    //     cap, cap_handle := allocator[bin_id].acquire();
    //   }

    //   count := cap.count;
    //   linear var AllocatorBin(_, cap_r) := cap;
    //   out_sv := enclose(cap_r);
    //   out_sv := SSM.join(in_sv, out_sv);
    // }

    // method releaseCapacity(
    //   count: uint32,
    //   bin_id: uint32,
    //   glinear cap_handle: MutexHandle<AllocatorBin>,
    //   glinear in_sv: SSM.Variables)
    // returns (glinear out_sv: SSM.Variables)
    //   requires Inv();
    //   requires bin_id < CAP.NumberOfBinsImpl()
    //   requires cap_handle.m == allocator[bin_id];
    //   requires in_sv.Variables?;
    //   requires in_sv.insert_capacity == Count.Variables(count as nat);
    //   ensures out_sv == in_sv.(insert_capacity := Count.Variables(0));
    // {
    //   glinear var rcap;
    //   assert in_sv.insert_capacity == Count.Variables(count as nat);
    //   glinear var mid_sv := resources_obey_inv(in_sv);

    //   ghost var left := in_sv.(insert_capacity := Count.Variables(0));
    //   ghost var right := unit().(insert_capacity := Count.Variables(count as nat));

    //   out_sv, rcap := SSM.split(mid_sv, left, right);
    //   glinear var rcap' := declose(rcap);
    //   allocator[bin_id].release(AllocatorBin(count, rcap'), cap_handle);
    // }

    // predicate EntriesMapped(entries: seq<Entry>, range: Range, sv: SSM.Variables)
    //   requires sv.Variables?
    // {
    //   forall i: Index :: range.Contains(i)
    //     ==> (sv.table[i].Some? && 
    // }

    predicate ProbePartialInv(
      entries: seq<Entry>,
      probe_key: Key,
      cur: Index,
      sv: SSM.Variables)
    {
      && Inv()
      && sv.Variables?
      && ValidPartialProbeRange(sv.table, probe_key, cur)
      && var p_range := Partial(hash(probe_key), cur);
      && (forall i: Index ::
        (p_range.Contains(i) <==> sv.table[i].Some?))
      && (forall i: Index ::
        p_range.Contains(i) <==> HasHandle(i))
      // && GetKnownSubTable(sv.table, p_range) == entries
    }

    linear inout method doProbe(probe_key: Key, glinear in_sv: SSM.Variables)
      returns (found: bool, glinear out_sv: SSM.Variables)
      decreases *

      requires old_self.Inv()
      requires forall i: Index :: !old_self.HasHandle(i)
      requires in_sv.Variables? && in_sv.table == UnitTable()

      // ensures 
    {
      var slot_idx := hash(probe_key);
      found := false;

      var entries := [];
      out_sv := in_sv;

      while true
        invariant
          self.ProbePartialInv(entries, probe_key, slot_idx, out_sv)
        // invariant
        //   found ==> SlotFullWithKey(out_sv.table[slot_idx], probe_key)
        decreases *
      {
        var entry;

        entry, out_sv := inout self.acquireRow(slot_idx, out_sv);
        entries := entries + [entry];

        match entry {
          case Empty => {
            break;
          }
          case Full(entry_key, value) => {
            if entry_key == probe_key {
              found := true;
              break;
            }
            if !entry.ShouldSkip(slot_idx, probe_key) {
              break;
            }

            slot_idx := NextIndex(slot_idx);

            if slot_idx == hash(probe_key) {
              assume false;
            }
          }
        }
      }

      assert found ==> SlotFullWithKey(out_sv.table[slot_idx], probe_key);
      // assert !found ==> ValidProbeRange(out_sv.table, probe_key, slot_idx);
    }


    // linear inout method doQuery(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
    //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

    //   decreases *

    //   requires old_self.Inv()
    //   requires input.QueryInput?
    //   requires IsInputResource(in_sv, rid, input)
    //   // ensures out_sv == SSM.output_stub(rid, output)
    // {
    //   var query_ticket := Ticket(rid, input);
    //   var query_key, hash_idx := input.key, hash(input.key);
    //   var slot_idx := hash_idx;
    //   ghost var probe_range := Partial(hash_idx, hash_idx);

    //   var entry; glinear var r;
    //   entry, r := inout self.acquireRow(hash_idx, in_sv);

    //   var entries := [entry];

    //   while true
    //     invariant Inv()
    //     decreases *
    //   {
    //     match entry {
    //       case Empty => {
    //         output := MapIfc.QueryOutput(NotFound);
    //         step := QueryNotFoundStep(slot_idx);
    //       }
    //       case Full(entry_key, value) => {
    //         if entry_key == key {
    //           step := QueryFoundStep(slot_idx);
    //           output := MapIfc.QueryOutput(Found(value));
    //         } else {
    //           var skip := entry.ShouldSkip(slot_idx, query_key);
    //           if !skip {
    //             output := MapIfc.QueryOutput(NotFound);
    //             step := QueryNotFoundStep(slot_idx);
    //           }
    //         }
    //       }
    //     }

    //     var next_slot_idx := NextIndex(slot_idx);
    //     entries := entries + [entry];

    //     entry, r := inout self.acquireRow(next_slot_idx, r);
    //   }
      
    //   // // assert step.QueryNotFoundStep? || step.QueryDoneStep?;
    //   // r := easy_transform_step(r, step);
    //   // out_sv := releaseRow(v, slot_idx, entry, handle, r);
    // }

  }

  predicate Inv(v: Variables)
  {
    v.Inv()
  }

  datatype Splitted = Splitted(expected: SSM.Variables, ri: SSM.Variables)

  function {:opaque} InitResoucePartial(i: nat): SSM.Variables
    requires i <= FixedSize()
  {
    var table := seq(FixedSize(), j => if j >= i then Some(Empty) else None);
    SSM.Variables(table, Count.Variables(Capacity()), multiset{}, multiset{})
  }

  function Split(r: SSM.Variables, i: Index) : (splt: Splitted)
    requires r == InitResoucePartial(i)
    ensures add(splt.expected, splt.ri) == r
  {
    var expected := InitResoucePartial(i+1);
    var ri := OneRowResource(i, Empty, 0);
    reveal InitResoucePartial();
    assert add(expected, ri).table ==
      seq(FixedSize(), j => if j >= i then Some(Empty) else None);
    Splitted(expected, ri)
  }

  // method init(glinear in_sv: SSM.Variables)
  // returns (v: Variables, glinear out_sv: SSM.Variables)
  //   // requires SSM.Init(in_sv)
  //   // ensures Inv(v)
  //   // ensures out_sv == unit()
  // {
  //   glinear var remaining_r := in_sv;
  //   var row_mutexes : RowMutexTable:= [];
  //   var i: uint32 := 0;

  //   assert remaining_r == InitResoucePartial(0) by {
  //     reveal InitResoucePartial();
  //   }

  //   while i < FixedSizeImpl()
  //     invariant i as int == |row_mutexes| <= FixedSize()
  //     invariant remaining_r == InitResoucePartial(i as nat)
  //     invariant RowMutexTableInv(row_mutexes)
  //   {
  //     ghost var splitted := Split(remaining_r, i as int);
      
  //     glinear var ri;
  //     remaining_r, ri := SSM.split(remaining_r, splitted.expected, splitted.ri);

  //     var m := new_mutex<Row>(Row(Empty, ri), (row) => RowInv(i as nat, row));
  //     row_mutexes := row_mutexes + [m];
  //     i := i + 1;
  //   }

  //   reveal InitResoucePartial();
  //   assert remaining_r.table == UnitTable();
  //   glinear var cap := declose(remaining_r);

  //   var allocator; glinear var remaining_cap;
  //   assert cap.value == Capacity();
  //   allocator, remaining_cap := CAP.init(cap);
  //   assert Count.Inv(Count.add(remaining_cap, remaining_cap));
  //   out_sv := enclose(remaining_cap);
  //   v := Variables.Variables(row_mutexes, allocator);
  // }

  // predicate method shouldHashGoBefore(search_h: uint32, slot_h: uint32, slot_idx: uint32) 
  //   ensures shouldHashGoBefore(search_h, slot_h, slot_idx) 
  //     == ShouldHashGoBefore(search_h as int, slot_h as int, slot_idx as int)
  // {
  //   || search_h < slot_h <= slot_idx // normal case
  //   || slot_h <= slot_idx < search_h // search_h wraps around the end of array
  //   || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  // }

  // method doInsert(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
  // returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   requires Inv(v)
  //   requires input.InsertInput?
  //   requires IsInputResource(in_sv, rid, input)
  //   ensures out_sv == SSM.output_stub(rid, output)
  //   decreases *
  // {
  //   var insert_ticket := Ticket(rid, input);
  //   var key, inital_key := input.key, input.key;
  //   var kv := KV(key, input.value);
  //   output := MapIfc.InsertOutput(true);

  //   var hash_idx := hash(key);
  //   var slot_idx := hash_idx;

  //   glinear var cap_handle; var bin_id; var count; glinear var r;
  //   count, bin_id, cap_handle, r := acquireCapacity(v, thread_id, in_sv);

  //   var entry; glinear var handle;
  //   entry, handle, r := acquireRow(v, slot_idx, r);

  //   count := count - 1;

  //   var step := ProcessInsertTicketStep(insert_ticket);
  //   r := easy_transform_step(r, step);

  //   while true 
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl()
  //     invariant r == OneRowResource(slot_idx as nat, Info(entry, Inserting(rid, kv, inital_key)), count as nat)
  //     invariant kv.key == key
  //     invariant hash_idx == hash(key)
  //     invariant handle.m == v.row_mutexes[slot_idx];
  //     decreases *
  //   {
  //     var next_slot_idx := getNextIndex(slot_idx);
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

  //     glinear var next_handle; var next_entry;
  //     next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);

  //     if step.InsertSwapStep? {
  //       entry := Full(kv);
  //       kv := new_kv;
  //       key := new_kv.key;
  //     }
  
  //     r := easy_transform_step(r, step);
  //     r := releaseRow(v, slot_idx, entry, handle, r);

  //     slot_idx, entry, handle := next_slot_idx, next_entry, next_handle;
  //     hash_idx := hash(key);
  //   }

  //   // assert step.InsertDoneStep? || step.InsertUpdateStep?;
  //   count := if step.InsertDoneStep? then count else count + 1;
  //   r := easy_transform_step(r, step);

  //   r := releaseRow(v, slot_idx, Full(kv), handle, r);
  //   out_sv := releaseCapacity(v, count, bin_id, cap_handle, r);
  // }

  // method doRemoveFound(v: Variables, rid: int, 
  //   slot_idx: uint32,
  //   hash_idx: uint32,
  //   inital_key: Key,
  //   entry: SSM.Entry,
  //   thread_id: uint32,
  //   glinear handle: Handle,
  //   glinear in_sv: SSM.Variables)
  
  //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *
  //   requires Inv(v)
  //   requires 0 <= slot_idx < FixedSizeImpl()
  //   requires 0 <= hash_idx < FixedSizeImpl()
  //   requires in_sv == OneRowResource(slot_idx as nat, Info(entry, Removing(rid, inital_key)), 0);
  //   requires entry.Full? && entry.kv.key == inital_key
  //   requires hash(inital_key) == hash_idx
  //   requires handle.m == v.row_mutexes[slot_idx]
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   var found_value := entry.kv.val;

  //   var slot_idx := slot_idx;
  //   var next_slot_idx := getNextIndex(slot_idx);

  //   glinear var handle := handle;
  //   glinear var next_handle; glinear var r; var next_entry;
  //   next_entry, next_handle, r := acquireRow(v, next_slot_idx, in_sv);

  //   var step := RemoveFoundItStep(slot_idx as nat);
  //   r := easy_transform_step(r, step);

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
  //     next_slot_idx := getNextIndex(slot_idx);

  //     if next_entry.Empty? || (next_entry.Full? && hash(next_entry.kv.key) == next_slot_idx) {
  //       assert DoneTidying(r, slot_idx as nat);
  //       break;
  //     }

  //     r := easy_transform_step(r, RemoveTidyStep(slot_idx as nat));
  //     r :=  releaseRow(v, slot_idx, next_entry, handle, r);

  //     slot_idx := next_slot_idx;
  //     next_slot_idx := getNextIndex(slot_idx);
  //     handle := next_handle;

  //     next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);
  //   }

  //   assert DoneTidying(r, slot_idx as nat);

  //   next_slot_idx := getNextIndex(slot_idx);
  //   output := MapIfc.RemoveOutput(true);

  //   var count; glinear var cap_handle; var bin_id;
  //   count, bin_id, cap_handle, r := acquireCapacity(v, thread_id, r);

  //   step := RemoveDoneStep(slot_idx as nat);
  //   r := easy_transform_step(r, step);

  //   r := releaseRow(v, slot_idx, Empty, handle, r);
  //   r := releaseRow(v, next_slot_idx, next_entry, next_handle, r);
  //   out_sv := releaseCapacity(v, count + 1, bin_id, cap_handle, r);
  // }

  // method doRemove(v: Variables, input: Ifc.Input, rid: int, thread_id: uint32, glinear in_sv: SSM.Variables)
  //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
  //   decreases *

  //   requires Inv(v)
  //   requires input.RemoveInput?
  //   requires IsInputResource(in_sv, rid, input)
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   var query_ticket := Ticket(rid, input);
  //   var key := input.key;
  //   var hash_idx := hash(key);
  //   var slot_idx := hash_idx;

  //   var entry; glinear var handle; glinear var r;
  //   entry, handle, r := acquireRow(v, slot_idx, in_sv);

  //   var step : Step := ProcessRemoveTicketStep(query_ticket);
  //   r := easy_transform_step(r, step);

  //   while true 
  //     invariant Inv(v);
  //     invariant 0 <= slot_idx < FixedSizeImpl();
  //     invariant r == OneRowResource(slot_idx as nat, Info(entry, Removing(rid, key)), 0)
  //     invariant step.RemoveNotFoundStep? ==> 
  //       (entry.Full? && shouldHashGoBefore(hash_idx, hash(entry.kv.key), slot_idx))
  //     invariant step.RemoveTidyStep? ==> (
  //       && TidyEnable(r, slot_idx as nat)
  //       && KnowRowIsFree(r, NextPos(slot_idx as nat)))
  //     invariant handle.m == v.row_mutexes[slot_idx]
  //     decreases *
  //   {
  //     var next_slot_idx := getNextIndex(slot_idx);

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

  //     glinear var next_handle; var next_entry;
  //     next_entry, next_handle, r := acquireRow(v, next_slot_idx, r);

  //     r := easy_transform_step(r, step);
  //     r := releaseRow(v, slot_idx, entry, handle, r);

  //     slot_idx, entry, handle := next_slot_idx, next_entry, next_handle;
  //   }

  //   if step.RemoveNotFoundStep? {
  //     output := MapIfc.RemoveOutput(false);
  //     r := easy_transform_step(r, step);
  //     r := releaseRow(v, slot_idx, entry, handle, r);
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
