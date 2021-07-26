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

    linear inout method doProbe(probe_key: Key, glinear in_sv: SSM.Variables)
      returns (
        entries: seq<Entry>,
        found: bool,
        p_range: Range,
        glinear out_sv: SSM.Variables)
  
      decreases *

      requires old_self.Inv()
      requires forall i: Index :: !old_self.HasHandle(i)
      requires in_sv.Variables? && in_sv.table == UnitTable()

      ensures self.Inv()
      ensures forall i: Index :: (p_range.Contains(i) <==> self.HasHandle(i))
      ensures out_sv.Variables?
      ensures forall i: Index :: (p_range.Contains(i) <==> out_sv.table[i].Some?)
      ensures UnwrapKnownRange(out_sv.table, p_range) == entries
      ensures p_range.HasSome()
      ensures var slot_idx := p_range.GetLast();
        && (found ==> SlotFullWithKey(out_sv.table[slot_idx], probe_key))
        && (!found ==> ValidProbeRange(out_sv.table, probe_key, Partial(hash(probe_key), slot_idx)))
      ensures out_sv.insert_capacity == in_sv.insert_capacity
      ensures out_sv.tickets == in_sv.tickets
      ensures out_sv.stubs == in_sv.stubs
    {
      var p_hash := hash(probe_key);
      var done := false;

      found := false;
      entries := [];
      p_range := Partial(p_hash, p_hash);
      out_sv := in_sv;

      while true
        invariant p_range.Partial? && p_range.start == p_hash

        invariant self.Inv()
        invariant (forall i: Index :: (p_range.Contains(i) <==> self.HasHandle(i)))

        invariant out_sv.Variables?
        invariant (forall i: Index :: (p_range.Contains(i) <==> out_sv.table[i].Some?))
        invariant !done ==> ValidPartialProbeRange(out_sv.table, probe_key, p_range)
        invariant UnwrapKnownRange(out_sv.table, p_range) == entries
        invariant out_sv.insert_capacity == in_sv.insert_capacity
        invariant out_sv.tickets == in_sv.tickets
        invariant out_sv.stubs == in_sv.stubs

        decreases *
      {
        var entry; ghost var prev_sv := out_sv;
        var slot_idx := p_range.end;
        entry, out_sv := inout self.acquireRow(slot_idx, out_sv);
        RangeEquivalentUnwrap(prev_sv.table, out_sv.table, p_range);

        entries := entries + [entry];
        p_range := p_range.RightExtend1();

        if p_range.Complete? {
          out_sv := resources_obey_inv(out_sv);
          CompleteProbeRangeImpossible(out_sv, probe_key);
          assert entry.Empty?;
        }

        assert slot_idx == p_range.GetLast();

        match entry {
          case Empty => {
            done := true;
            break;
          }
          case Full(entry_key, value) => {
            if entry_key == probe_key {
              done := true;
              found := true;
              break;
            }
            if !entry.ShouldSkip(slot_idx, probe_key) {
              done := true;
              break;
            }
          }
        }
      }
    }

    linear inout method releaseRows(entries: seq<Entry>, range: Range, glinear in_sv: SSM.Variables)
      returns (glinear out_sv: SSM.Variables)

      requires old_self.Inv()
      requires in_sv.Variables?
      requires (forall i: Index :: (range.Contains(i) <==> old_self.HasHandle(i)))
      requires forall i: Index :: (range.Contains(i) <==> in_sv.table[i].Some?)
      requires UnwrapKnownRange(in_sv.table, range) == entries

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
        invariant self.Inv()
        invariant (forall i: Index :: (range.Contains(i) <==> self.HasHandle(i)))
        invariant out_sv.Variables?
        invariant (forall i: Index :: (range.Contains(i) <==> out_sv.table[i].Some?))
        invariant 0 <= index <= |entries| 
        invariant UnwrapKnownRange(out_sv.table, range) == entries[..index]
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

    linear inout method doQuery(input: Ifc.Input, rid: int, glinear in_sv: SSM.Variables)
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

      entries, found, p_range, out_sv := inout self.doProbe(query_key, in_sv);

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
