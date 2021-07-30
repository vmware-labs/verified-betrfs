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
  import opened GhostLinearMaybe

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

  predicate RowMutexTableInv(row_mutexes: RowMutexTable)
    requires |row_mutexes| <= FixedSize()
  {
    (forall i | 0 <= i < |row_mutexes|
      :: row_mutexes[i].inv == ((row) => RowInv(i, row)))
  }

  linear datatype Variables = Variables(
    row_mutexes: RowMutexTable,
    glinear handles: glseq<MutexHandle<Row>>,
    glinear cap_handle: glseq<MutexHandle<AllocatorBin>>,
    bin_id: uint32,
    allocator: CAP.AllocatorMutexTable)
  {
    predicate HasCapHandle()
      requires |cap_handle| == 1
    {
      0 in cap_handle
    }

    predicate CapHandleInv()
    {
      && CAP.Inv(allocator)
      && |cap_handle| == 1
      && bin_id < CAP.NumberOfBinsImpl()
      && (HasCapHandle() ==> 
        cap_handle[0].m == allocator[bin_id])
    }

    predicate HandlesInv()
      requires |row_mutexes| == FixedSize()
    {
      && |handles| == FixedSize()
      // if I have the handle, it corresponds to the row mutex
      && (forall i: Index | i in handles
        :: handles[i].m == row_mutexes[i])
      && CapHandleInv()
    }

    predicate Inv()
    {
      && |row_mutexes| == FixedSize()
      && RowMutexTableInv(row_mutexes)
      && HandlesInv()
    }

    predicate HasRowHandle(index: Index)
      requires Inv()
    {
      index in handles
    }

    predicate HasNoRowHandle()
      requires Inv()
    {
      forall i: Index :: !HasRowHandle(i)
    }

    linear inout method acquireRowInner(index: Index, glinear in_sv: SSM.Variables)
      returns (entry: Entry, glinear out_sv: SSM.Variables)

      requires old_self.Inv()
      requires !old_self.HasRowHandle(index)
      requires in_sv.Variables?
      requires in_sv.table[index] == None

      ensures self.Inv()
      ensures self == old_self.(handles := self.handles)
      ensures self.HasRowHandle(index)
      ensures forall i: Index | i != index ::
        old_self.HasRowHandle(i) <==> self.HasRowHandle(i)
      ensures out_sv == in_sv.(table := in_sv.table[index := Some(entry)])
    {
      linear var row; glinear var handle: MutexHandle<Row>;
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
      && (forall i: Index :: (range.Contains(i) <==> HasRowHandle(i)))
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
    ensures self == old_self.(handles := self.handles)
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
      requires old_self.HasRowHandle(index)
      requires in_sv.Variables?
      requires in_sv.table[index] == Some(entry)
            
      ensures self.Inv()
      ensures self == old_self.(handles := self.handles)
      ensures !self.HasRowHandle(index)
      ensures forall i: Index | i != index ::
        old_self.HasRowHandle(i) <==> self.HasRowHandle(i)
      ensures out_sv == in_sv.(table := in_sv.table[index := None]);
    {
      glinear var rmutex;
      ghost var left := in_sv.(table := in_sv.table[index := None]);
      ghost var right := OneRowResource(index, entry, 0);
      out_sv, rmutex := SSM.split(in_sv, left, right);
      
      glinear var handle := lseq_take_inout(inout self.handles, index);
      self.row_mutexes[index].release(Row(entry, rmutex), handle);
    }

    linear inout method releaseRows(entries: seq<Entry>, range: Range, glinear in_sv: SSM.Variables)
      returns (glinear out_sv: SSM.Variables)

      requires old_self.RangeOwnershipInv(entries, range, in_sv)

      ensures self.Inv()
      ensures self == old_self.(handles := self.handles)
      ensures self.HasNoRowHandle();
      ensures out_sv == in_sv.(table := UnitTable())
    {
      var range := range;
      var entries := entries;
      var index := |entries|;
      out_sv := in_sv;

      while range.HasSome()
        invariant 0 <= index <= |entries| 
        invariant self.RangeOwnershipInv(entries[..index], range, out_sv)
        invariant self == old_self.(handles := self.handles)
        invariant out_sv == in_sv.(table := out_sv.table)
        decreases |range|
      {
        var slot_idx := range.GetLast();
        ghost var prev_table := out_sv.table;

        out_sv := inout self.releaseRow(slot_idx, entries[index-1], out_sv);
        range := range.RightShrink1();
        index := index - 1;

        RangeEquivalentUnwrap(prev_table, out_sv.table, range);
      }

      assert self.HasNoRowHandle();
      assert out_sv.table == UnitTable();
    }

    linear inout method acquireCapacity(glinear in_sv: SSM.Variables)
    returns (
      count: uint32,
      glinear out_sv: SSM.Variables)

      decreases *
      requires old_self.Inv()
      requires !old_self.HasCapHandle()
      requires in_sv.Variables?
      requires in_sv.insert_capacity.value == 0

      ensures self.Inv()
      ensures self.HasCapHandle()
      ensures self == old_self.(cap_handle := self.cap_handle)
        .(bin_id := self.bin_id)
      ensures 0 < count <= CapacityImpl()
      ensures out_sv == in_sv
        .(insert_capacity := Count.Variables(count as nat))
    {
      // bin_id is the actual place we found the capacity (in case we had to steal it from someone else) 
      var bid := 0;
      linear var cap; glinear var cap_handle;
      cap, cap_handle := self.allocator[bid].acquire();

      while true
        invariant cap.count as nat == cap.resource.value <= Capacity()
        invariant self.Inv()
        invariant bid < CAP.NumberOfBinsImpl()
        invariant CAP.BinInv(cap)
        invariant cap_handle.m == self.allocator[bid]
        decreases *
      {
        if cap.count > 0 {
          break;
        }
        assert CAP.BinInv(cap);
        self.allocator[bid].release(cap, cap_handle);

        bid := bid + 1;
        bid := if bid >= CAP.NumberOfBinsImpl() then 0 else bid;

        cap, cap_handle := self.allocator[bid].acquire();
      }
      
      inout self.bin_id := bid;
      lseq_give_inout(inout self.cap_handle, 0, cap_handle);

      count := cap.count;
      linear var AllocatorBin(_, cap_r) := cap;
      out_sv := enclose(cap_r);
      out_sv := SSM.join(in_sv, out_sv);
      assert out_sv.Variables?;
    }

    linear inout method releaseCapacity(
      count: uint32,
      glinear in_sv: SSM.Variables)
    returns (glinear out_sv: SSM.Variables)
      requires old_self.Inv();
      requires old_self.HasCapHandle()
      requires in_sv.Variables?;
      requires in_sv.insert_capacity == Count.Variables(count as nat);

      ensures self.Inv()
      ensures self == old_self.(cap_handle := self.cap_handle)
      ensures !self.HasCapHandle()
      ensures out_sv == in_sv.(insert_capacity := Count.Variables(0));
    {
      glinear var rcap;
      assert in_sv.insert_capacity == Count.Variables(count as nat);
      glinear var mid_sv := resources_obey_inv(in_sv);

      ghost var left := in_sv.(insert_capacity := Count.Variables(0));
      ghost var right := unit().(insert_capacity := Count.Variables(count as nat));

      glinear var cap_handle := lseq_take_inout(inout self.cap_handle, 0);

      out_sv, rcap := SSM.split(mid_sv, left, right);
      glinear var rcap' := declose(rcap);
      self.allocator[self.bin_id].release(AllocatorBin(count, rcap'), cap_handle);
    }

    linear inout method probe(probe_key: Key, glinear in_sv: SSM.Variables)
      returns (
        entries: seq<Entry>,
        found: bool,
        range: Range,
        glinear out_sv: SSM.Variables)
      decreases *

      requires old_self.Inv()
      requires forall i: Index :: !old_self.HasRowHandle(i)
      requires in_sv.Variables? && in_sv.table == UnitTable()

      ensures range.Partial?
      ensures range.HasSome()

      ensures self.RangeOwnershipInv(entries, range, out_sv)
      ensures self == old_self.(handles := self.handles)
      ensures found ==> KeyPresentProbeRange(out_sv.table, probe_key, range.RightShrink1())
      ensures !found ==> KeyAbsentProbeRange(out_sv.table, probe_key, range.RightShrink1())
      ensures out_sv == in_sv.(table := out_sv.table)
    {
      var p_hash := hash(probe_key);

      found := false; entries := [];
      range := Partial(p_hash, p_hash);
      out_sv := in_sv;

      while true
        invariant range.Partial? && range.start == p_hash
        invariant self == old_self.(handles := self.handles)
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

    linear inout method query(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      decreases *
      requires old_self.Inv()
      requires old_self.HasNoRowHandle()
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

    linear inout method insertOverwrite(
      ticket: Ticket,
      range: Range,
      entries: seq<Entry>,
      glinear in_sv: SSM.Variables)

      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      requires old_self.RangeOwnershipInv(entries, range, in_sv)
      requires range.HasSome()
      requires range.Partial?
      requires var probe_key := ticket.input.key;
        KeyPresentProbeRange(in_sv.table, probe_key, range.RightShrink1())
      requires in_sv.tickets == multiset{ticket}
      requires in_sv.insert_capacity.value == 0
      requires ticket.input.InsertInput?
      requires in_sv.stubs == multiset{}

      ensures out_sv == SSM.output_stub(ticket.rid, output)
    {
      out_sv := in_sv;
      
      var probe_key := ticket.input.key;
      var h := hash(probe_key);
      var end := range.GetLast();
      var probe_range := Partial(h, end);

      var inserted := Full(probe_key, ticket.input.value);
      ghost var t1 := out_sv.table;
      out_sv := easy_transform_step(out_sv, OverwriteStep(ticket, end));
      ghost var t2 := out_sv.table;
      
      var new_entries := entries[ |entries| - 1 := inserted ];

      assert UnwrapRange(t2, range) == new_entries by {
        assert RangeEquivalent(t1, t2, probe_range);
        RangeEquivalentUnwrap(t1, t2, probe_range);
      }

      output := MapIfc.InsertOutput(true);
      out_sv := inout self.releaseRows(new_entries, range, out_sv);
    }

    linear inout method insertNotFound(
      ticket: Ticket,
      range: Range,
      entries: seq<Entry>,
      glinear in_sv: SSM.Variables)
      
      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      decreases *

      requires old_self.RangeOwnershipInv(entries, range, in_sv)
      requires !old_self.HasCapHandle()

      requires ticket.input.InsertInput?

      requires range.HasSome()
      requires range.Partial?
      requires var probe_key := ticket.input.key;
        KeyAbsentProbeRange(in_sv.table, probe_key, range.RightShrink1())

      requires in_sv.tickets == multiset{ticket}
      requires in_sv.insert_capacity.value == 0
      requires in_sv.stubs == multiset{}
  
      ensures out_sv == SSM.output_stub(ticket.rid, output)
    {
      out_sv := in_sv;

      var probe_key := ticket.input.key;
      var h := hash(probe_key);
      var start, end := range.GetLast(), range.GetLast();

      var entries, range := entries, range;
      var probe_range := Partial(h, start);
      var entry := entries[ |entries| - 1 ];
      var inserted := Full(probe_key, ticket.input.value);

      if entry.Full? {
        while true
          invariant range.Partial? && range.start == h
          invariant self.RangeOwnershipInv(entries, range, out_sv)
          invariant !self.HasCapHandle()
          invariant KeyAbsentProbeRange(out_sv.table, probe_key, probe_range)
          invariant RangeFull(out_sv.table, range)
          invariant self == old_self.(handles := self.handles) 
          invariant out_sv == in_sv.(table := out_sv.table)
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
  
      var count;
      count, out_sv := inout self.acquireCapacity(out_sv);
      var shift_range := Partial(start, end);

      ghost var t1 := out_sv.table;
      out_sv := easy_transform_step(out_sv, InsertStep(ticket, start, end));
      var t2 := out_sv.table;

      RightShiftUnwrap(t1, t2, inserted, entries, range, start);

      var probe_len := WrappedDistance(range.start, start);
      var new_entries := entries[..probe_len] + [inserted] + entries[probe_len..|entries| - 1];

      assert UnwrapRange(t2, range) == new_entries;
      out_sv := inout self.releaseRows(new_entries, range, out_sv);
      out_sv := inout self.releaseCapacity(count - 1, out_sv);
      output := MapIfc.InsertOutput(true);
    }

    linear inout method insert(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
      returns (output: Ifc.Output, glinear out_sv: SSM.Variables)

      decreases *
      requires old_self.Inv()
      requires old_self.HasNoRowHandle()
      requires !old_self.HasCapHandle()
      requires input.InsertInput?
      requires IsInputResource(in_sv, rid, input)

      ensures out_sv == SSM.output_stub(rid, output)
    {
      var insert_ticket := Ticket(rid, input);
      var insert_key, insert_value := input.key, input.value;

      var entries, found, p_range;
      entries, found, p_range, out_sv := inout self.probe(insert_key, in_sv);

      if found {
        output, out_sv := inout self.insertOverwrite(insert_ticket, p_range, entries, out_sv);
      } else {
        assert !self.HasCapHandle();
        output, out_sv := inout self.insertNotFound(insert_ticket, p_range, entries, out_sv);
      }
    }
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




