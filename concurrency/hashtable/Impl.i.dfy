include "../framework/GhostLinearSequence.i.dfy"
include "../framework/Mutex.s.dfy"
include "HashTableStubSSM.s.dfy"

module Impl {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened GhostLinearMaybe
  import opened GhostLinearSequence_s
  import opened GhostLinearSequence_i
  import opened Mutexes

  import opened KeyValueType
  import opened Limits
  import SSM = HashTableStubSSM
  import opened CircularTable
  import opened CircularRange

  import T = Tokens(TicketStubPCM(MapIfc, SSM))
  import TST = TicketStubToken(MapIfc, SSM) 
  import opened GhostLoc

  type Token = T.Token

  function OneRowToken(loc: Loc, i: Index, entry: Entry): Token
  {
    T.Token(loc, SSM.OneRowResource(i, entry))
  }

  linear datatype Row = Row(
    entry: Entry,
    glinear resource: Token)
  {
    predicate Inv(loc: Loc, i: Index)
    {
      resource == OneRowToken(loc, i, entry)
    }
  }

  type RowMutex = Mutex<Row>

  type RowMutexTable = seq<RowMutex>

  predicate RowMutexTableInv(row_mutexes: RowMutexTable, loc: Loc)
    requires |row_mutexes| <= FixedSize()
  {
    (forall i | 0 <= i < |row_mutexes|
      :: row_mutexes[i].inv == ((row: Row) => row.Inv(loc, i)))
  }

  datatype IVariables = IVariables(
    row_mutexes: RowMutexTable,
    capacity: uint32)

  linear datatype Variables = Variables(
    glinear token: Token,
    glinear handles: glseq<MutexHandle<Row>>,
    iv: IVariables)
  {
    predicate HasRowHandle(index: Index)
      requires |handles| == FixedSize()
    {
      index in handles
    }

    predicate HasNoRowHandle()
      requires |handles| == FixedSize()
    {
      forall i: Index :: !HasRowHandle(i)
    }

    predicate Inv()
    {
      && token.val.Variables?

      && |iv.row_mutexes| == FixedSize()
      && RowMutexTableInv(iv.row_mutexes, token.loc)

      && |handles| == FixedSize()

      // have the handle ==> corresponds to the row mutex
      && (forall i: Index :: HasRowHandle(i) ==> 
        handles[i].m == iv.row_mutexes[i])
      // have the handle <==> have the row in token
      && (forall i: Index ::HasRowHandle(i) <==> token.val.table[i].Some?)

      && iv.capacity as nat == token.val.insert_capacity
    }

    predicate RangeOwnershipInv(entries: seq<Entry>, range: Range)
    {
      && Inv()
      && range.Partial?
      && (forall i: Index :: (range.Contains(i) <==> HasRowHandle(i)))
      && UnwrapRange(token.val.table, range) == entries
    }

    predicate RowOnlyUpdate(old_var: Variables)
      requires token.val.Variables?
      requires old_var.token.val.Variables?
    {
      var table := token.val.table;
      var val := old_var.token.val.(table := table);
      var token := old_var.token.(val := val);
      && this == old_var.(token := token).(handles := handles)
    }

    linear inout method acquireRow(old_entries: seq<Entry>, old_range: Range)
      returns (entries: seq<Entry>, entry: Entry, range: Range)

      requires old_self.RangeOwnershipInv(old_entries, old_range)

      ensures entries == old_entries + [entry]
      ensures range == old_range.RightExtend1()
      ensures self.RangeOwnershipInv(entries, range)
      ensures self.token.val.table ==
        old_self.token.val.table[old_range.end := Some(entry)] 
      ensures self.token.loc == old_self.token.loc
      ensures RangeFull(old_self.token.val.table, old_range)
        && entry.Full? ==> RangeFull(self.token.val.table, range)
      ensures self.RowOnlyUpdate(old_self)
    {
      var index := old_range.end;
      assert !old_range.Contains(index);
  
      linear var row; glinear var handle: MutexHandle<Row>;
      row, handle := self.iv.row_mutexes[index].acquire();
  
      linear var Row(out_entry, row_token) := row;
      entry := out_entry;

      T.inout_join(inout self.token, row_token);
      lseq_give_inout(inout self.handles, index, handle);

      if old_range.AlmostComplete() {
        // out_sv := resources_obey_inv(out_sv);
        // AlmostCompleteFullRangeImpossible(out_sv, range);
        assume false;
      }

      RangeEquivalentUnwrap(old_self.token.val.table,
        self.token.val.table, old_range);

      entries := old_entries + [entry];
      range := old_range.RightExtend1();
    }

    linear inout method releaseRow(entries: seq<Entry>, old_range: Range)
      returns (range: Range)

      requires old_self.RangeOwnershipInv(entries, old_range)
      requires old_range.HasSome()

      ensures range == old_range.RightShrink1()
      ensures self.RangeOwnershipInv(entries[..|entries| -1 ], range)
      ensures self.RowOnlyUpdate(old_self)
    {
      var index := old_range.GetLast();
      var len := |entries|;
      var entry := entries[len-1];

      glinear var rmutex;
      ghost var table := self.token.val.table[index := None];
      ghost var left := self.token.val.(table := table);
      ghost var right := SSM.OneRowResource(index, entry);
      rmutex := T.inout_split(inout self.token, left, right);

      glinear var handle := lseq_take_inout(inout self.handles, index);
      self.iv.row_mutexes[index].release(Row(entry, rmutex), handle);
      range := old_range.RightShrink1();

      RangeEquivalentUnwrap(old_self.token.val.table,
        self.token.val.table, range);
    }

    linear inout method releaseRows(entries: seq<Entry>, range: Range)
      requires old_self.RangeOwnershipInv(entries, range)

      ensures self.Inv()
      ensures self.HasNoRowHandle();
      ensures self.RowOnlyUpdate(old_self)
    {
      var range := range;
      var entries := entries;
      var index := |entries|;

      while range.HasSome()
        invariant 0 <= index <= |entries| 
        invariant self.RangeOwnershipInv(entries[..index], range)
        invariant self.RowOnlyUpdate(old_self)
        decreases |range|
      {
        var slot_idx := range.GetLast();

        range := inout self.releaseRow(entries[..index], range);
        index := index - 1;
      }
    }

    linear inout method probe(probe_key: Key)
      returns (found: bool,
        entries: seq<Entry>,
        range: Range)
      decreases *

      requires old_self.Inv()
      requires old_self.HasNoRowHandle()

      ensures range.Partial?
      ensures range.HasSome()

      ensures self.RangeOwnershipInv(entries, range)
      ensures found ==> KeyPresentProbeRange(self.token.val.table, probe_key, range.RightShrink1())
      ensures !found ==> KeyAbsentProbeRange(self.token.val.table, probe_key, range.RightShrink1())
    {
      var p_hash := hash(probe_key);

      found := false; entries := [];
      range := Partial(p_hash, p_hash);

      while true
        invariant range.Partial? && range.start == p_hash
        invariant self.RangeOwnershipInv(entries, range)
        invariant ValidPartialProbeRange(self.token.val.table, probe_key, range)
        invariant self.RowOnlyUpdate(old_self)
        decreases *
      {
        var slot_idx := range.end;
        var entry;
        entries, entry, range := inout self.acquireRow(entries, range);
   
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

//     linear inout method acquireCapacity(glinear in_sv: SSM.M)
//     returns (
//       count: uint32,
//       glinear out_sv: SSM.M)

//       decreases *
//       requires old_self.Inv()
//       requires !old_self.HasCapHandle()
//       requires in_sv.Variables?
//       requires in_sv.insert_capacity.value == 0

//       ensures self.Inv()
//       ensures self.HasCapHandle()
//       ensures self == old_self.(cap_handle := self.cap_handle)
//         .(bin_id := self.bin_id)
//       ensures 0 < count <= CapacityImpl()
//       ensures out_sv == in_sv
//         .(insert_capacity := Count.Variables(count as nat))
//     {
//       // bin_id is the actual place we found the capacity (in case we had to steal it from someone else) 
//       var bid := 0;
//       linear var cap; glinear var cap_handle;
//       cap, cap_handle := self.allocator[bid].acquire();

//       while true
//         invariant cap.count as nat == cap.resource.value <= Capacity()
//         invariant self.Inv()
//         invariant bid < CAP.NumberOfBinsImpl()
//         invariant CAP.BinInv(cap)
//         invariant cap_handle.m == self.allocator[bid]
//         decreases *
//       {
//         if cap.count > 0 {
//           break;
//         }
//         assert CAP.BinInv(cap);
//         self.allocator[bid].release(cap, cap_handle);

//         bid := bid + 1;
//         bid := if bid >= CAP.NumberOfBinsImpl() then 0 else bid;

//         cap, cap_handle := self.allocator[bid].acquire();
//       }
      
//       inout self.bin_id := bid;
//       lseq_give_inout(inout self.cap_handle, 0, cap_handle);

//       count := cap.count;
//       linear var AllocatorBin(_, cap_r) := cap;
//       out_sv := enclose(cap_r);
//       out_sv := SSM.join(in_sv, out_sv);
//       assert out_sv.Variables?;
//     }

//     linear inout method releaseCapacity(
//       count: uint32,
//       glinear in_sv: SSM.M)
//     returns (glinear out_sv: SSM.M)
//       requires old_self.Inv();
//       requires old_self.HasCapHandle()
//       requires in_sv.Variables?;
//       requires in_sv.insert_capacity == Count.Variables(count as nat);

//       ensures self.Inv()
//       ensures self == old_self.(cap_handle := self.cap_handle)
//       ensures !self.HasCapHandle()
//       ensures out_sv == in_sv.(insert_capacity := Count.Variables(0));
//     {
//       glinear var rcap;
//       assert in_sv.insert_capacity == Count.Variables(count as nat);
//       glinear var mid_sv := resources_obey_inv(in_sv);

//       ghost var left := in_sv.(insert_capacity := Count.Variables(0));
//       ghost var right := unit().(insert_capacity := Count.Variables(count as nat));

//       glinear var cap_handle := lseq_take_inout(inout self.cap_handle, 0);

//       out_sv, rcap := SSM.split(mid_sv, left, right);
//       glinear var rcap' := declose(rcap);
//       self.allocator[self.bin_id].release(AllocatorBin(count, rcap'), cap_handle);
//     }



//     linear inout method query(input: Ifc.Input, rid: int, glinear in_sv: SSM.M)
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       decreases *
//       requires old_self.Inv()
//       requires old_self.HasNoRowHandle()
//       requires input.QueryInput?
//       requires IsInputResource(in_sv, rid, input)
//       ensures out_sv == SSM.output_stub(rid, output)
//     {
//       var query_ticket := Ticket(rid, input);
//       var query_key := input.key;

//       var entries, found, p_range;
//       entries, found, p_range, out_sv := inout self.probe(query_key, in_sv);

//       var slot_idx := p_range.GetLast();

//       if found {
//         var step := QueryFoundStep(query_ticket, slot_idx);
//         assert QueryFoundEnable(out_sv, step);
//         out_sv := easy_transform_step(out_sv, step);
//         output := MapIfc.QueryOutput(Found(entries[ |entries| - 1 ].value));
//       } else {
//         var step := QueryNotFoundStep(query_ticket, slot_idx);
//         assert QueryNotFoundEnable(out_sv, step);
//         out_sv := easy_transform_step(out_sv, step);
//         output := MapIfc.QueryOutput(NotFound);
//       }

//       out_sv := inout self.releaseRows(entries, p_range, out_sv);
//       assert out_sv.stubs == multiset { Stub(rid, output) };
//     }

//     linear inout method insertOverwrite(
//       ticket: Ticket,
//       range: Range,
//       entries: seq<Entry>,
//       glinear in_sv: SSM.M)

//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       requires old_self.RangeOwnershipInv(entries, range, in_sv)
//       requires range.HasSome()
//       requires range.Partial?
//       requires var probe_key := ticket.input.key;
//         KeyPresentProbeRange(in_sv.table, probe_key, range.RightShrink1())
//       requires in_sv.tickets == multiset{ticket}
//       requires in_sv.insert_capacity.value == 0
//       requires ticket.input.InsertInput?
//       requires in_sv.stubs == multiset{}

//       ensures out_sv == SSM.output_stub(ticket.rid, output)
//     {
//       out_sv := in_sv;
      
//       var probe_key := ticket.input.key;
//       var h := hash(probe_key);
//       var end := range.GetLast();
//       var probe_range := Partial(h, end);

//       var inserted := Full(probe_key, ticket.input.value);
//       ghost var t1 := out_sv.table;
//       out_sv := easy_transform_step(out_sv, OverwriteStep(ticket, end));
//       ghost var t2 := out_sv.table;
      
//       var new_entries := entries[ |entries| - 1 := inserted ];

//       assert UnwrapRange(t2, range) == new_entries by {
//         assert RangeEquivalent(t1, t2, probe_range);
//         RangeEquivalentUnwrap(t1, t2, probe_range);
//       }

//       output := MapIfc.InsertOutput(true);
//       out_sv := inout self.releaseRows(new_entries, range, out_sv);
//     }

//     linear inout method insertNotFound(
//       ticket: Ticket,
//       range: Range,
//       entries: seq<Entry>,
//       glinear in_sv: SSM.M)
      
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       decreases *

//       requires old_self.RangeOwnershipInv(entries, range, in_sv)
//       requires !old_self.HasCapHandle()

//       requires ticket.input.InsertInput?

//       requires range.HasSome()
//       requires range.Partial?
//       requires var probe_key := ticket.input.key;
//         KeyAbsentProbeRange(in_sv.table, probe_key, range.RightShrink1())

//       requires in_sv.tickets == multiset{ticket}
//       requires in_sv.insert_capacity.value == 0
//       requires in_sv.stubs == multiset{}
  
//       ensures out_sv == SSM.output_stub(ticket.rid, output)
//     {
//       out_sv := in_sv;

//       var probe_key := ticket.input.key;
//       var h := hash(probe_key);
//       var start, end := range.GetLast(), range.GetLast();

//       var entries, range := entries, range;
//       var probe_range := Partial(h, start);
//       var entry := entries[ |entries| - 1 ];
//       var inserted := Full(probe_key, ticket.input.value);

//       if entry.Full? {
//         while true
//           invariant range.Partial? && range.start == h
//           invariant self.RangeOwnershipInv(entries, range, out_sv)
//           invariant !self.HasCapHandle()
//           invariant KeyAbsentProbeRange(out_sv.table, probe_key, probe_range)
//           invariant RangeFull(out_sv.table, range)
//           invariant self == old_self.(handles := self.handles) 
//           invariant out_sv == in_sv.(table := out_sv.table)
//           decreases FixedSize() - |range|
//         {
//           ghost var prev_sv := out_sv;
//           end := range.end;
//           entries, range, out_sv := inout self.acquireRow(entries, range, out_sv);
//           entry := entries[ |entries| - 1 ];

//           if entry.Empty? {
//             assert SlotEmpty(out_sv.table[end]);
//             break;
//           }
//         }
//       }
  
//       var count;
//       count, out_sv := inout self.acquireCapacity(out_sv);
//       var shift_range := Partial(start, end);

//       ghost var t1 := out_sv.table;
//       out_sv := easy_transform_step(out_sv, InsertStep(ticket, start, end));
//       var t2 := out_sv.table;

//       RightShiftUnwrap(t1, t2, inserted, entries, range, start);

//       var probe_len := WrappedDistance(range.start, start);
//       var new_entries := entries[..probe_len] + [inserted] + entries[probe_len..|entries| - 1];

//       assert UnwrapRange(t2, range) == new_entries;
//       out_sv := inout self.releaseRows(new_entries, range, out_sv);
//       out_sv := inout self.releaseCapacity(count - 1, out_sv);
//       output := MapIfc.InsertOutput(true);
//     }

//     linear inout method insert(input: Ifc.Input, rid: int, glinear in_sv: SSM.M)
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       decreases *
//       requires old_self.Inv()
//       requires old_self.HasNoRowHandle()
//       requires !old_self.HasCapHandle()
//       requires input.InsertInput?
//       requires IsInputResource(in_sv, rid, input)

//       ensures out_sv == SSM.output_stub(rid, output)
//     {
//       var insert_ticket := Ticket(rid, input);
//       var insert_key, insert_value := input.key, input.value;

//       var entries, found, p_range;
//       entries, found, p_range, out_sv := inout self.probe(insert_key, in_sv);

//       if found {
//         output, out_sv := inout self.insertOverwrite(insert_ticket, p_range, entries, out_sv);
//       } else {
//         assert !self.HasCapHandle();
//         output, out_sv := inout self.insertNotFound(insert_ticket, p_range, entries, out_sv);
//       }
//     }

//     linear inout method removeFound(
//       ticket: Ticket,
//       range: Range,
//       entries: seq<Entry>,
//       glinear in_sv: SSM.M)
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       decreases *

//       requires old_self.RangeOwnershipInv(entries, range, in_sv)
//       requires !old_self.HasCapHandle()

//       requires ticket.input.RemoveInput?

//       requires range.HasSome()
//       requires range.Partial?
//       requires var probe_key := ticket.input.key;
//         KeyPresentProbeRange(in_sv.table, probe_key, range.RightShrink1())

//       requires in_sv.tickets == multiset{ticket}
//       requires in_sv.insert_capacity.value == 0
//       requires in_sv.stubs == multiset{}
    
//       ensures out_sv == SSM.output_stub(ticket.rid, output)
//     {
//       out_sv := in_sv;

//       var probe_key := ticket.input.key;
//       var h := hash(probe_key);
//       var start, end := range.GetLast(), range.end;

//       var entries, range := entries, range;
//       var probe_range := Partial(h, start);
//       var entry := entries[ |entries| - 1 ];

//       assert entry.key == probe_key;
//       assert SlotFullWithKey(out_sv.table[start], probe_key);

//       while true
//         invariant range.Partial? && range.start == h
//         invariant self.RangeOwnershipInv(entries, range, out_sv)
//         invariant !self.HasCapHandle()
//         invariant KeyPresentProbeRange(out_sv.table, probe_key, probe_range)
//         invariant RangeFull(out_sv.table, range)
//         invariant forall i: Index | Partial(NextIndex(start), range.end).Contains(i) :: SlotShouldTidy(out_sv.table[i], i);
//         invariant self == old_self.(handles := self.handles) 
//         invariant out_sv == in_sv.(table := out_sv.table)
//         decreases FixedSize() - |range|
//       {
//         ghost var prev_sv := out_sv;
//         end := range.end;
//         entries, range, out_sv := inout self.acquireRow(entries, range, out_sv);
//         entry := entries[ |entries| - 1 ];

//         if entry.Empty? || !entry.ShouldTidy(end) {
//           break;
//         }
//       }

//       end := PrevIndex(end);

//       // assert ValidTidyRange(out_sv.table, Partial(start, end), probe_key);
//       var count;
//       count, out_sv := inout self.acquireCapacity(out_sv);

//       ghost var t1 := out_sv.table;
//       out_sv := easy_transform_step(out_sv, RemoveStep(ticket, start, end));
//       var t2 := out_sv.table;

//       // assert IsTableLeftShift(t1, t2, start, end);
//       LeftShiftUnwrap(t1, t2, entries, range, start);

//       var len := WrappedDistance(range.start, range.end);
//       var probe_len := WrappedDistance(range.start, start);
//       var new_entries := entries[..probe_len] + entries[probe_len+1..len - 1] + [Empty] + [entries[len - 1]];
  
//       assert UnwrapRange(t2, range) == new_entries;
//       out_sv := inout self.releaseRows(new_entries, range, out_sv);
//       out_sv := inout self.releaseCapacity(count + 1, out_sv);
//       output := MapIfc.RemoveOutput(true);
//     }

//     linear inout method remove(input: Ifc.Input, rid: int, glinear in_sv: SSM.M)
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)

//       decreases *
//       requires old_self.Inv()
//       requires old_self.HasNoRowHandle()
//       requires !old_self.HasCapHandle()
//       requires input.RemoveInput?
//       requires IsInputResource(in_sv, rid, input)

//       ensures out_sv == SSM.output_stub(rid, output)
//     {
//       var ticket := Ticket(rid, input);
//       var remove_key := input.key;

//       var entries, found, p_range;
//       entries, found, p_range, out_sv := inout self.probe(remove_key, in_sv);

//       if found {
//         output, out_sv := inout self.removeFound(ticket, p_range, entries, out_sv);
//       } else {
//         var slot_idx := p_range.GetLast();
//         var step := RemoveNotFoundStep(ticket, slot_idx);
//         assert RemoveNotFoundEnable(out_sv, step);
//         out_sv := easy_transform_step(out_sv, step);
//         output := MapIfc.RemoveOutput(false);
//         out_sv := inout self.releaseRows(entries, p_range, out_sv);
//       }
//     }

//     linear inout method call(input: Ifc.Input, rid: int, glinear in_sv: SSM.M)
//       returns (output: Ifc.Output, glinear out_sv: SSM.M)
//       decreases *
//     requires old_self.Inv()
//     requires old_self.HasNoRowHandle()
//     requires !old_self.HasCapHandle()
//     requires in_sv == SSM.input_ticket(rid, input)
//     ensures out_sv == SSM.output_stub(rid, output)
//     {
//       assert |in_sv.tickets| == 1;
//       var the_ticket :| the_ticket in in_sv.tickets;
      
//       if the_ticket.input.QueryInput? {
//         output, out_sv := inout self.query(input, rid, in_sv);
//       } else if the_ticket.input.InsertInput? {
//         output, out_sv := inout self.insert(input, rid, in_sv);
//       } else if the_ticket.input.RemoveInput? {
//         output, out_sv := inout self.remove(input, rid, in_sv);
//       } else {
//         out_sv := in_sv;
//         assert false;
//       }
//     }
//   }

//   predicate Inv(v: Variables)
//   {
//     v.Inv()
//   }

//   datatype Splitted = Splitted(expected: SSM.M, ri: SSM.M)

//   function {:opaque} InitResoucePartial(i: nat): SSM.M
//     requires i <= FixedSize()
//   {
//     var table := seq(FixedSize(), j => if j >= i then Some(Empty) else None);
//     SSM.M(table, Count.Variables(Capacity()), multiset{}, multiset{})
//   }

//   function Split(r: SSM.M, i: Index) : (splt: Splitted)
//     requires r == InitResoucePartial(i)
//     ensures add(splt.expected, splt.ri) == r
//   {
//     var expected := InitResoucePartial(i+1);
//     var ri := OneRowResource(i, Empty, 0);
//     reveal InitResoucePartial();
//     assert add(expected, ri).table ==
//       seq(FixedSize(), j => if j >= i then Some(Empty) else None);
//     Splitted(expected, ri)
  }

  // method init(glinear in_sv: SSM.M)
  // returns (v: Variables, glinear out_sv: SSM.M)
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

  // method call(v: Variables, input: Ifc.Input, rid: int, glinear in_sv: SSM.M, thread_id: uint32)
  //   returns (output: Ifc.Output, glinear out_sv: SSM.M)
  //   decreases *
  // // requires Inv(in_sv)
  // // requires ticket == SSM.input_ticket(rid, key)
  //   ensures out_sv == SSM.output_stub(rid, output)
  // {
  //   NewTicketValid(rid, input);
  //   assert Valid(input_ticket(rid, input));

  //   out_sv := in_sv;
  //   assert |in_sv.tickets| == 1;
  //   var the_ticket :| the_ticket in out_sv.tickets;

    
  //   if the_ticket.input.QueryInput? {
  //     output, out_sv := inout v.query(input, rid, out_sv);
  //   // } else if the_ticket.input.InsertInput? {
  //   //   output, out_sv := inout v.doInsert(input, rid, thread_id, in_sv);
  //   // } else if the_ticket.input.RemoveInput? {
  //   //   output, out_sv := inout v.doRemove(input, rid, thread_id, in_sv);
  //   } else {
  //     out_sv := in_sv;
  //     assert false;
  //   }
  // }

  // lemma NewTicket_RefinesMap(s: SSM.M, s': SSM.M, rid: int, input: Ifc.Input)
  // {
  // }
  
  // lemma ReturnStub_RefinesMap(s: SSM.M, s': SSM.M, rid: int, output: Ifc.Output)
  // {
  // }
}
