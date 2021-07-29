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
  import opened Sequences

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

    predicate HasNoHandle()
      requires Inv()
    {
      forall i: Index :: !HasHandle(i)
    }

    linear inout method acquireRowInner(index: Index, glinear in_sv: SSM.Variables)
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

    predicate RangeOwnershipInv(entries: seq<Entry>, range: Range, sv: SSM.Variables)
    {
      && Inv()
      && sv.Variables?
      && (forall i: Index :: (range.Contains(i) <==> HasHandle(i)))
      && (forall i: Index :: (range.Contains(i) <==> sv.table[i].Some?))
      && UnwrapRange(sv.table, range) == entries
    }

    linear inout method acquireRow(
      entries: seq<Entry>,
      range: Range,
      glinear in_sv: SSM.Variables)
    returns (
      entries': seq<Entry>,
      range': Range,
      glinear out_sv: SSM.Variables
    )

    requires old_self.RangeOwnershipInv(entries, range, in_sv)
    requires range.Partial?
    requires RangeFull(in_sv.table, range)

    ensures self.RangeOwnershipInv(entries', range', out_sv);
    ensures range'.Partial?
    ensures |entries'| != 0
    ensures Last(entries').Full? ==> RangeFull(out_sv.table, range')
    // ensures entry.Empty? ==> RangeFull(out_sv.table, range)
    ensures range' == range.RightExtend1()
    ensures var entry := Last(entries');
      && out_sv == in_sv.(table := in_sv.table[range.end := Some(entry)])
      && out_sv.table[range.end] == Some(entry)
    {
      out_sv := in_sv;
      ghost var prev_sv := out_sv;

      var slot_idx := range.end; var entry;
      entry, out_sv := inout self.acquireRowInner(slot_idx, out_sv);
      RangeEquivalentUnwrap(prev_sv.table, out_sv.table, range);

      if range.AlmostComplete() {
        out_sv := resources_obey_inv(out_sv);
        AlmostCompleteFullRangeImpossible(out_sv, range);
      }

      entries' := entries + [entry];
      range' := range.RightExtend1();
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

    linear inout method probe(probe_key: Key, glinear in_sv: SSM.Variables)
      returns (
        entries: seq<Entry>,
        found: bool,
        range: Range,
        glinear out_sv: SSM.Variables)
      decreases *

      requires old_self.Inv()
      requires forall i: Index :: !old_self.HasHandle(i)
      requires in_sv.Variables? && in_sv.table == UnitTable()

      ensures range.HasSome()
      ensures self.RangeOwnershipInv(entries, range, out_sv)
      ensures found ==> SlotFullWithKey(out_sv.table[range.GetLast()], probe_key)
      ensures !found ==> ValidProbeRange(out_sv.table, probe_key, range.RightShrink1())
      ensures out_sv.insert_capacity == in_sv.insert_capacity
      ensures out_sv.tickets == in_sv.tickets
      ensures out_sv.stubs == in_sv.stubs
    {
      var p_hash := hash(probe_key);

      found := false; entries := [];
      range := Partial(p_hash, p_hash);
      out_sv := in_sv;

      while true
        invariant range.Partial? && range.start == p_hash
        invariant self.RangeOwnershipInv(entries, range, out_sv)
        invariant ValidPartialProbeRange(out_sv.table, probe_key, range)
        invariant out_sv.insert_capacity == in_sv.insert_capacity
        invariant out_sv.tickets == in_sv.tickets
        invariant out_sv.stubs == in_sv.stubs
        decreases *
      {
        var slot_idx := range.end;
        entries, range, out_sv := inout self.acquireRow(entries, range, out_sv);
        var entry: Entry := entries[ |entries| - 1 ];
   
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
          }
        }
      }
    }

    linear inout method releaseRows(entries: seq<Entry>, range: Range, glinear in_sv: SSM.Variables)
      returns (glinear out_sv: SSM.Variables)

      requires old_self.RangeOwnershipInv(entries, range, in_sv)

      ensures self.Inv()
      ensures self.HasNoHandle();
      ensures out_sv.Variables?
      ensures out_sv.table == UnitTable();
      ensures out_sv.insert_capacity == in_sv.insert_capacity
      ensures out_sv.tickets == in_sv.tickets
      ensures out_sv.stubs == in_sv.stubs
    {
      var range := range;
      var entries := entries;
      var index := |entries|;
      out_sv := in_sv;

      while range.HasSome()
        invariant 0 <= index <= |entries| 
        invariant self.RangeOwnershipInv(entries[..index], range, out_sv)
        invariant out_sv.insert_capacity == in_sv.insert_capacity
        invariant out_sv.tickets == in_sv.tickets
        invariant out_sv.stubs == in_sv.stubs
        decreases |range|
      {
        var slot_idx := range.GetLast();
        ghost var prev_table := out_sv.table;

        out_sv := inout self.releaseRow(slot_idx, entries[index-1], out_sv);
        range := range.RightShrink1();
        index := index - 1;

        RangeEquivalentUnwrap(prev_table, out_sv.table, range);
      }

      assert self.HasNoHandle();
      assert out_sv.table == UnitTable();
    }

    linear inout method query(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      decreases *
      requires old_self.Inv()
      requires old_self.HasNoHandle()
      requires input.QueryInput?
      requires IsInputResource(in_sv, rid, input)
      ensures out_sv == SSM.output_stub(rid, output)
    {
      var query_ticket := Ticket(rid, input);
      var query_key := input.key;

      var entries, found, p_range;
      entries, found, p_range, out_sv := inout self.probe(query_key, in_sv);

      var slot_idx := p_range.GetLast();

      if found {
        var step := QueryFoundStep(query_ticket, slot_idx);
        assert QueryFoundEnable(out_sv, step);
        out_sv := easy_transform_step(out_sv, step);
        output := MapIfc.QueryOutput(Found(entries[ |entries| - 1 ].value));
      } else {
        var step := QueryNotFoundStep(query_ticket, slot_idx);
        assert QueryNotFoundEnable(out_sv, step);
        out_sv := easy_transform_step(out_sv, step);
        output := MapIfc.QueryOutput(NotFound);
      }

      out_sv := inout self.releaseRows(entries, p_range, out_sv);
      assert out_sv.stubs == multiset { Stub(rid, output) };
    }

    linear inout method insertNotFound(ticket: Ticket, p_range: Range, entries: seq<Entry>, glinear in_sv: SSM.Variables)
      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      requires old_self.RangeOwnershipInv(entries, p_range, in_sv)
      requires p_range.HasSome()
      requires p_range.Partial?

      requires var probe_key := ticket.input.key;
        ValidProbeRange(in_sv.table, probe_key, p_range.RightShrink1())

      requires ticket in in_sv.tickets
      requires ticket.input.InsertInput?
      requires in_sv.insert_capacity.value >= 1
      requires in_sv.stubs == multiset{}
  
      // ensures out_sv == SSM.output_stub(ticket.rid, output)
    {
      out_sv := in_sv;
      var probe_key := ticket.input.key;
      var entries := entries;
      var range := p_range;
      var start := range.GetLast();
      var end := start;
      var entry := entries[ |entries| - 1 ];

      var h := hash(probe_key);
      var probe_range := Partial(h, start);

      if entry.Full? {
        while true
          invariant range.Partial? && range.start == h
          invariant self.RangeOwnershipInv(entries, range, out_sv)
          invariant ValidProbeRange(out_sv.table, probe_key, probe_range)
          invariant RangeFull(out_sv.table, range)
          invariant out_sv.insert_capacity == in_sv.insert_capacity
          invariant out_sv.tickets == in_sv.tickets
          invariant out_sv.stubs == in_sv.stubs
          decreases FixedSize() - |range|
        {
          ghost var prev_sv := out_sv;
          end := range.end;
          entries, range, out_sv := inout self.acquireRow(entries, range, out_sv);
          entry := entries[ |entries| - 1 ];

          if entry.Empty? {
            assert SlotEmpty(out_sv.table[end]);
            break;
          }
        }
      }
      output := MapIfc.InsertOutput(true);

      var shift_range := Partial(start, end);
      var step := InsertStep(ticket, start, end);
      assert InsertEnable(out_sv, step);
      ghost var t1 := out_sv.table;
      out_sv := easy_transform_step(out_sv, step);
      var t2 := out_sv.table;
      assert out_sv.stubs == multiset { Stub(ticket.rid, output) };

      var inserted := Full(ticket.input.key, ticket.input.value);
      RightShiftUnwrap(t1, t2, inserted, entries, range, start);

      var probe_len := WrappedDistance(p_range.start, start);
      var new_entries := entries[..probe_len] + [inserted] + entries[probe_len..|entries| - 1];

      assert UnwrapRange(t2, range) == new_entries;
      out_sv := inout self.releaseRows(new_entries, range, out_sv);
    }

    // linear inout method insert(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
    //   returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

    //   decreases *
    //   requires old_self.Inv()
    //   requires old_self.HasNoHandle()
    //   requires input.InsertInput?
    //   requires IsInputResource(in_sv, rid, input)
    
    // {
    //   var insert_ticket := Ticket(rid, input);
    //   var insert_key, insert_value := input.key, input.value;

    //   var entries, found, p_range;
    //   entries, found, p_range, out_sv := inout self.probe(insert_key, in_sv);

    //   var slot_idx := p_range.GetLast();

    //   if found {
    //     var step := OverwriteStep(insert_ticket, slot_idx);
    //     assert OverwriteEnable(out_sv, step);
    //     out_sv := easy_transform_step(out_sv, step);
    //   } else {
    //     var step := InsertStep(insert_ticket, slot_idx);
    //     assert InsertEnable(out_sv, step);
    //     out_sv := easy_transform_step(out_sv, step);
    //   }

    //   output := MapIfc.InsertOutput(true);
    // }
  }

  // method rightShiftEntries(entries: seq<Entry>,
  //   new_entry: Entry,
  //   prev_table: FixedTable,
  //   range: Range, 
  //   table: FixedTable)
  //   requires UnwrapRange(prev_table, range) == entries
  //   requires table == TableRightShift(prev_table, Some(new_entry), start, end);
  // {
  // }

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

  method call(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables, thread_id: uint32)
    returns (output: Ifc.Output, glinear out_sv: SSM.Variables)
    decreases *
  // requires Inv(in_sv)
  // requires ticket == SSM.input_ticket(rid, key)
    ensures out_sv == SSM.output_stub(rid, output)
  {
    // assert SSM.Inv();
    NewTicketValid(rid, input);
    assert Valid(input_ticket(rid, input));

    out_sv := in_sv;
    assume false;

    // assert |in_sv.tickets| == 1;
    // var the_ticket :| the_ticket in in_sv.tickets;

    // if the_ticket.input.QueryInput? {
    //   output, out_sv := doQuery(v, input, rid, in_sv);
    // } else if the_ticket.input.InsertInput? {
    //   output, out_sv := doInsert(v, input, rid, thread_id, in_sv);
    // } else if the_ticket.input.RemoveInput? {
    //   output, out_sv := doRemove(v, input, rid, thread_id, in_sv);
    // } else {
    //   out_sv := in_sv;
    //   assert false;
    // }
  }

  // lemma NewTicket_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, input: Ifc.Input)
  // {
  // }
  
  // lemma ReturnStub_RefinesMap(s: SSM.Variables, s': SSM.Variables, rid: int, output: Ifc.Output)
  // {
  // }
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
