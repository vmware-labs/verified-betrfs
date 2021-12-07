include "../framework/GlinearMap.s.dfy"
include "../framework/GlinearMap.i.dfy"
include "../framework/Mutex.i.dfy"
include "HashTableStubSSM.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"

module Impl {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened GlinearMap
  import opened GlinearMap_i
  import opened Mutexes

  import opened Limits
  import opened KeyValueType
  import MapIfc
  import SSM = HashTableStubSSM
  import opened CircularTable
  import opened CircularRange

  import opened LinearSequence_i
  import opened LinearSequence_s

  import PCM = TicketStubPCM(MapIfc, SSM)
  import T = Tokens(PCM)
  import TST = TicketStubToken(MapIfc, SSM) 
  import opened GhostLoc

  type Token = T.Token

  linear datatype Row = Row(
    entry: Entry,
    glinear resource: Token)
  {
    predicate Inv(loc: Loc, i: Index)
    {
      resource == T.Token(loc, SSM.OneRowResource(i, entry))
    }
  }

  linear datatype Cap = Cap(
    remaining: nat,
    glinear resource: Token)
  {
    predicate Inv(loc: Loc)
    {
      && remaining <= Capacity()
      && resource == T.Token(loc, SSM.unit()
        .(insert_capacity := remaining))
    }
  }

  type RowMutex = Mutex<Row>

  type RowMutexTable = lseq<RowMutex>

  predicate RowMutexTablePartialInv(row_mutexes: RowMutexTable, loc: Loc, index: nat)
    requires index <= |row_mutexes| == FixedSize()
  {
    && (forall i | 0 <= i < index ::
      && i in row_mutexes
      && row_mutexes[i].WF()
      && (row_mutexes[i].inv == ((row: Row) => row.Inv(loc, i))))
    && (forall i | index <= i < |row_mutexes| ::
      (i !in row_mutexes))
  }

  predicate RowMutexTableInv(row_mutexes: RowMutexTable, loc: Loc)
    requires |row_mutexes| == FixedSize()
  {
    RowMutexTablePartialInv(row_mutexes, loc, |row_mutexes|)
  }

  datatype CapUpdate =
    | Increment
    | Decrement
    | Unchanged

  linear datatype IVariables = IVariables(
    linear row_mutexes: RowMutexTable,
    linear cap_mutex: Mutex<Cap>)
  {
    predicate Inv(loc: Loc)
    {
      && |row_mutexes| == FixedSize()
      && RowMutexTableInv(row_mutexes, loc)
      && cap_mutex.WF()
      && (cap_mutex.inv == ((cap: Cap) => cap.Inv(loc)))
    }
  }

  linear datatype Variables = Variables(
    glinear token: Token,
    glinear handles: map<Index, MutexHandle<Row>>)
  {
    predicate HasRowHandle(index: Index)
    {
      index in handles
    }

    predicate HasNoRowHandle()
    {
      forall i: Index :: !HasRowHandle(i)
    }

    predicate Inv(iv: IVariables)
    {
      && token.val.Variables?

      && iv.Inv(token.loc)
      // have the handle ==> corresponds to the row mutex
      && (forall i: Index :: HasRowHandle(i) ==> (
        && handles[i].WF()
        && handles[i].m == iv.row_mutexes[i]))
      // have the handle <==> have the row in token
      && (forall i: Index ::HasRowHandle(i) <==> token.val.table[i].Some?)
    }

    predicate RangeOwnershipInv(iv: IVariables, entries: seq<Entry>, range: Range)
    {
      && Inv(iv)
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

    linear inout method acquireRow(shared iv: IVariables, old_entries: seq<Entry>, old_range: Range)
      returns (entries: seq<Entry>, entry: Entry, range: Range)

      requires old_self.RangeOwnershipInv(iv, old_entries, old_range)
      requires RangeFull(old_self.token.val.table, old_range)

      ensures entries == old_entries + [entry]
      ensures range == old_range.RightExtend1()
      ensures self.RangeOwnershipInv(iv, entries, range)
      ensures self.token.val.table ==
        old_self.token.val.table[old_range.end := Some(entry)] 
      ensures self.token.loc == old_self.token.loc
      ensures entry.Full? ==> RangeFull(self.token.val.table, range)
      ensures self.RowOnlyUpdate(old_self)
      decreases *
    {
      var index := old_range.end;
      assert !old_range.Contains(index);
  
      linear var row; glinear var handle: MutexHandle<Row>;
      row, handle := lseq_peek(iv.row_mutexes, index as uint64).acquire();
  
      linear var Row(out_entry, row_token) := row;
      entry := out_entry;

      T.inout_join(inout self.token, row_token);
      glmap_insert_inout(inout self.handles, index, handle);

      if old_range.AlmostComplete() {
        gshared var temp := T.get_unit_shared(self.token.loc);
        T.is_valid(temp, inout self.token);

        calc ==> {
          PCM.valid(SSM.dot(SSM.unit(), self.token.val));
          {
            SSM.commutative(SSM.unit(), self.token.val);
          }
          PCM.valid(SSM.dot(self.token.val, SSM.unit()));
          {
            SSM.dot_unit(self.token.val);
          }
          PCM.valid(self.token.val);
          {
            SSM.AlmostCompleteFullRangeImpossible(self.token.val, old_range);
          }
          false;
        }
      }

      RangeEquivalentUnwrap(old_self.token.val.table,
        self.token.val.table, old_range);

      entries := old_entries + [entry];
      range := old_range.RightExtend1();
    }

    linear inout method releaseRow(shared iv: IVariables, entries: seq<Entry>, old_range: Range)
      returns (range: Range)

      requires old_self.RangeOwnershipInv(iv, entries, old_range)
      requires old_range.HasSome()

      ensures range == old_range.RightShrink1()
      ensures self.RangeOwnershipInv(iv, entries[..|entries| -1 ], range)
      ensures self.RowOnlyUpdate(old_self)
    {
      var index := old_range.GetLast();
      var len := |entries|;
      var entry := entries[len-1];

      glinear var mutex_token;
      ghost var table := self.token.val.table[index := None];
      ghost var left := self.token.val.(table := table);
      ghost var right := SSM.OneRowResource(index, entry);
      mutex_token := T.inout_split(inout self.token, left, right);

      glinear var handle := glmap_take_inout(inout self.handles, index);

      lseq_peek(iv.row_mutexes, index as uint64).release(Row(entry, mutex_token), handle);

      range := old_range.RightShrink1();

      RangeEquivalentUnwrap(old_self.token.val.table,
        self.token.val.table, range);
    }

    predicate CapOnlyUpdate(old_var: Variables, udpate: CapUpdate)
      requires token.val.Variables?
      requires old_var.token.val.Variables?
      requires udpate.Decrement? ==> old_var.token.val.insert_capacity > 0
    {
      var cap := old_var.token.val.insert_capacity +
        (match udpate 
          case Increment => 1
          case Decrement => -1
          case Unchanged => 0);
      var val := old_var.token.val.(insert_capacity := cap);
      var token := old_var.token.(val := val);
      && this == old_var.(token := token)
    }

    linear inout method acquireCapacity(shared iv: IVariables)
      decreases *

      requires old_self.Inv(iv)

      ensures self.Inv(iv)
      ensures self.CapOnlyUpdate(old_self, Increment)
    {
      var continue := true;

      while continue
        invariant self.Inv(iv)
        invariant continue ==> self.CapOnlyUpdate(old_self, Unchanged)
        invariant !continue ==> self.CapOnlyUpdate(old_self, Increment)
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
          T.inout_join(inout self.token, temp_token);
          continue := false;
        }

        iv.cap_mutex.release(Cap(count, cap_token), handle);
      }
    }

    linear inout method releaseCapacity(shared iv: IVariables)
      requires old_self.Inv(iv)
      requires old_self.token.val.insert_capacity == 1

      ensures self.Inv(iv)
      ensures self.CapOnlyUpdate(old_self, Decrement)
      decreases *
    {
      linear var cap; glinear var handle: MutexHandle<Cap>;
      cap, handle := iv.cap_mutex.acquire();

      linear var Cap(count, cap_token) := cap;

      count := count + 1;
      ghost var left := self.token.val.(insert_capacity := 0);
      ghost var right := SSM.unit().(insert_capacity := 1);
      assert SSM.dot(left, right) == self.token.val; 
      glinear var temp_token := T.inout_split(inout self.token, left, right);
      T.inout_join(inout cap_token, temp_token);

      iv.cap_mutex.release(Cap(count, cap_token), handle);
    }

    linear inout method releaseRows(shared iv: IVariables, entries: seq<Entry>, range: Range)
      requires old_self.RangeOwnershipInv(iv, entries, range)

      ensures self.Inv(iv)
      ensures self.HasNoRowHandle();
      ensures self.RowOnlyUpdate(old_self)
    {
      var range := range;
      var entries := entries;
      var index := |entries|;

      while range.HasSome()
        invariant 0 <= index <= |entries| 
        invariant self.RangeOwnershipInv(iv, entries[..index], range)
        invariant self.RowOnlyUpdate(old_self)
        decreases |range|
      {
        var slot_idx := range.GetLast();

        range := inout self.releaseRow(iv, entries[..index], range);
        index := index - 1;
      }
    }

    linear inout method probe(shared iv: IVariables, probe_key: Key)
      returns (found: bool,
        entries: seq<Entry>,
        range: Range)
      requires old_self.Inv(iv)
      requires old_self.HasNoRowHandle()

      ensures range.Partial?
      ensures range.HasSome()

      ensures self.RangeOwnershipInv(iv, entries, range)
      ensures found ==> KeyPresentProbeRange(self.token.val.table, probe_key, range.RightShrink1())
      ensures !found ==> KeyAbsentProbeRange(self.token.val.table, probe_key, range.RightShrink1())
      ensures self.RowOnlyUpdate(old_self)
      decreases *
    {
      var p_hash := hash(probe_key);

      found := false; entries := [];
      range := Partial(p_hash, p_hash);

      while true
        invariant range.Partial? && range.start == p_hash
        invariant self.RangeOwnershipInv(iv, entries, range)
        invariant ValidPartialProbeRange(self.token.val.table, probe_key, range)
        invariant self.RowOnlyUpdate(old_self)
        decreases FixedSize() - |range|
      {
        var slot_idx := range.end;
        var entry;
        entries, entry, range := inout self.acquireRow(iv, entries, range);
   
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

    linear inout method query(shared iv: IVariables, ghost rid: nat, input: MapIfc.Input)
      returns (output: MapIfc.Output)

      requires old_self.Inv(iv)
      requires old_self.HasNoRowHandle()
      requires input.QueryInput?
      requires old_self.token.val == SSM.Ticket(rid, input)

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
      decreases *
    {
      var query_key := input.key;

      var entries, found, p_range;
      found, entries, p_range := inout self.probe(iv, query_key);

      var slot_idx := p_range.GetLast();

      if found {
        var step := SSM.QueryFoundStep(rid, input, slot_idx);
        var expected := self.token.val.QueryFound(step);
        assert SSM.NextStep(self.token.val, expected, step);
        TST.inout_update_next(inout self.token, expected);
        output := MapIfc.QueryOutput(Found(entries[ |entries| - 1 ].value));
      } else {
        var step := SSM.QueryNotFoundStep(rid, input, slot_idx);
        var expected := self.token.val.QueryNotFound(step);
        assert SSM.NextStep(self.token.val, expected, step);
        TST.inout_update_next(inout self.token, expected);
        output := MapIfc.QueryOutput(NotFound);
      }

      inout self.releaseRows(iv, entries, p_range);
    }

    linear inout method insertOverwrite(
      shared iv: IVariables,
      ghost rid: nat, input: MapIfc.Input,
      entries: seq<Entry>, range: Range)
      returns (output: MapIfc.Output)

      requires old_self.RangeOwnershipInv(iv, entries, range)

      requires input.InsertInput?
      requires old_self.token.val == SSM.Ticket(rid, input).(table := old_self.token.val.table)

      requires range.HasSome()
      requires range.Partial?
      requires KeyPresentProbeRange(old_self.token.val.table, input.key, range.RightShrink1())

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
    {
      var probe_key := input.key;
      var h := hash(probe_key);
      var end := range.GetLast();
      var probe_range := Partial(h, end);

      var inserted := Full(probe_key, input.value);

      var step := SSM.OverwriteStep(rid, input, end);
      var expected := self.token.val.Overwrite(step);
      assert SSM.NextStep(self.token.val, expected, step);

      ghost var t1 := self.token.val.table;
      TST.inout_update_next(inout self.token, expected);
      ghost var t2 := self.token.val.table;

      var new_entries := entries[ |entries| - 1 := inserted ];

      assert UnwrapRange(t2, range) == new_entries by {
        assert RangeEquivalent(t1, t2, probe_range);
        RangeEquivalentUnwrap(t1, t2, probe_range);
      }

      output := MapIfc.InsertOutput(true);
      inout self.releaseRows(iv, new_entries, range);
    }

    linear inout method insertNotFound(
      shared iv: IVariables,
      ghost rid: nat, input: MapIfc.Input,
      entries: seq<Entry>, range: Range)
      returns (output: MapIfc.Output)

      requires old_self.RangeOwnershipInv(iv, entries, range)

      requires input.InsertInput?
      requires old_self.token.val == SSM.Ticket(rid, input).(table := old_self.token.val.table).(insert_capacity := 1)

      requires range.HasSome()
      requires range.Partial?
      requires KeyAbsentProbeRange(old_self.token.val.table, input.key, range.RightShrink1())

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
      decreases *
    {
      var probe_key := input.key;
      var h := hash(probe_key);
      var start, end := range.GetLast(), range.GetLast();

      var entries, range := entries, range;
      var probe_range := Partial(h, start);
      var entry := entries[ |entries| - 1 ];
      var inserted := Full(probe_key, input.value);

      if entry.Full? {
        while true
          invariant range.Partial? && range.start == h
          invariant self.RangeOwnershipInv(iv, entries, range)
          invariant KeyAbsentProbeRange(self.token.val.table, probe_key, probe_range)
          invariant RangeFull(self.token.val.table, range)
          invariant self.RowOnlyUpdate(old_self)
          decreases FixedSize() - |range|
        {
          end := range.end;
          entries, entry, range := inout self.acquireRow(iv, entries, range);

          if entry.Empty? {
            // assert SlotEmpty(out_sv.table[end]);
            break;
          }
        }
      }

      var step := SSM.InsertStep(rid, input, start, end); 
      
      var expected := self.token.val.Insert(step);
      assert SSM.NextStep(self.token.val, expected, step);

      ghost var t1 := self.token.val.table;
      TST.inout_update_next(inout self.token, expected);
      ghost var t2 := self.token.val.table;

      assert forall i: Index :: t1[i].Some? <==> t2[i].Some?;

      RightShiftUnwrap(t1, t2, inserted, entries, range, start);

      var probe_len := WrappedDistance(range.start, start);
      var new_entries := entries[..probe_len] + [inserted] + entries[probe_len..|entries| - 1];

      assert UnwrapRange(t2, range) == new_entries;
      inout self.releaseRows(iv, new_entries, range);
      output := MapIfc.InsertOutput(true);
    }

    linear inout method insert(shared iv: IVariables, ghost rid: nat, input: MapIfc.Input)
      returns (output: MapIfc.Output)
      decreases *

      requires old_self.Inv(iv)
      requires old_self.HasNoRowHandle()
      requires input.InsertInput?
      requires old_self.token.val == SSM.Ticket(rid, input)

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
    {
      var insert_key, insert_value := input.key, input.value;

      var entries, found, p_range;
      found, entries, p_range := inout self.probe(iv, insert_key);

      if found {
        output := inout self.insertOverwrite(iv, rid, input, entries, p_range);
      } else {
        inout self.acquireCapacity(iv);
        output := inout self.insertNotFound(iv, rid, input, entries, p_range);
      }
    }

    linear inout method removeFound(
      shared iv: IVariables,
      ghost rid: nat, input: MapIfc.Input,
      entries: seq<Entry>, range: Range)
      returns (output: MapIfc.Output)

      requires old_self.RangeOwnershipInv(iv, entries, range)

      requires input.RemoveInput?
      requires old_self.token.val == SSM.Ticket(rid, input).(table := old_self.token.val.table)

      requires range.HasSome()
      requires range.Partial?
      requires KeyPresentProbeRange(old_self.token.val.table, input.key, range.RightShrink1())

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
      decreases *
    {
      var probe_key := input.key;
      var h := hash(probe_key);
      var start, end := range.GetLast(), range.GetLast();

      var entries, range := entries, range;
      var probe_range := Partial(h, start);
      var entry := entries[ |entries| - 1 ];

      while true
        invariant range.Partial? && range.start == h
        invariant self.RangeOwnershipInv(iv, entries, range)
        invariant KeyPresentProbeRange(self.token.val.table, probe_key, probe_range)
        invariant RangeFull(self.token.val.table, range)
        invariant forall i: Index | Partial(NextIndex(start), range.end).Contains(i) :: SlotShouldTidy(self.token.val.table[i], i);
        invariant self.RowOnlyUpdate(old_self)
        decreases FixedSize() - |range|
      {
        end := range.end;
        entries, entry, range := inout self.acquireRow(iv, entries, range);

        if entry.Empty? || !entry.ShouldTidy(end) {
          break;
        }
      }

      end := PrevIndex(end);

      var step := SSM.RemoveStep(rid, input, start, end); 
      
      var expected := self.token.val.Remove(step);
      assert SSM.NextStep(self.token.val, expected, step);

      ghost var t1 := self.token.val.table;
      TST.inout_update_next(inout self.token, expected);
      ghost var t2 := self.token.val.table;

      assert forall i: Index :: t1[i].Some? <==> t2[i].Some?;

      LeftShiftUnwrap(t1, t2, entries, range, start);

      var len := WrappedDistance(range.start, range.end);
      var probe_len := WrappedDistance(range.start, start);
      var new_entries := entries[..probe_len] + entries[probe_len+1..len - 1] + [Empty] + [entries[len - 1]];
  
      inout self.releaseRows(iv, new_entries, range);
      inout self.releaseCapacity(iv);
      output := MapIfc.RemoveOutput(true);
    }

    linear inout method remove(shared iv: IVariables, ghost rid: nat, input: MapIfc.Input)
      returns (output: MapIfc.Output)

      requires old_self.Inv(iv)
      requires old_self.HasNoRowHandle()
      requires input.RemoveInput?
      requires old_self.token.val == SSM.Ticket(rid, input)

      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
      decreases *
    {
      var remove_key := input.key;

      var entries, found, p_range;
      found, entries, p_range := inout self.probe(iv, remove_key);

      if found {
        output := inout self.removeFound(iv, rid, input, entries, p_range);
      } else {
        var slot_idx := p_range.GetLast();
        var step := SSM.RemoveNotFoundStep(rid, input, slot_idx);
        var expected := self.token.val.RemoveNotFound(step);
        assert SSM.NextStep(self.token.val, expected, step);
        TST.inout_update_next(inout self.token, expected);
        inout self.releaseRows(iv, entries, p_range);
        output := MapIfc.RemoveOutput(false);
      }
    }

    linear inout method call(shared iv: IVariables, ghost rid: nat, input: MapIfc.Input)
      returns (output: MapIfc.Output)
      decreases *

      requires old_self.Inv(iv)
      requires old_self.HasNoRowHandle()
      requires old_self.token.val == SSM.Ticket(rid, input)
      ensures self.Inv(iv)
      ensures self.token.loc == old_self.token.loc
      ensures self.token.val == SSM.Stub(rid, output)
    {
      if input.QueryInput? {
        output := inout self.query(iv, rid, input);
      } else if input.InsertInput? {
        output := inout self.insert(iv, rid, input);
      } else if input.RemoveInput? {
        output := inout self.remove(iv, rid, input);
      }
    }
  }

  datatype Splitted = Splitted(expected: SSM.M, ri: SSM.M)

  function {:opaque} InitResoucePartial(i: nat): SSM.M
    requires i <= FixedSize()
  {
    var table := seq(FixedSize(), j => if j >= i then Some(Empty) else None);
    SSM.unit().(table := table).(insert_capacity := Capacity())
  }

  function Split(r: SSM.M, i: Index) : (splt: Splitted)
    requires r == InitResoucePartial(i)
    ensures SSM.dot(splt.expected, splt.ri) == r
  {
    var expected := InitResoucePartial(i+1);
    var ri := SSM.OneRowResource(i, Empty);
    reveal InitResoucePartial();
    assert SSM.dot(expected, ri).table ==
      seq(FixedSize(), j => if j >= i then Some(Empty) else None);
    Splitted(expected, ri)
  }

  method init(glinear in_token: Token)
  returns (linear v: Variables, linear iv: IVariables)
    requires in_token.val.Variables?
    requires SSM.Init() == in_token.val
    ensures v.token.loc == in_token.loc
    ensures v.Inv(iv)
    ensures v.HasNoRowHandle()
    ensures v.token.val == SSM.unit()
  {
    var loc := in_token.loc;
    glinear var token := in_token;
    linear var row_mutexes := lseq_alloc(FixedSizeImpl() as uint64);
    var i: uint32 := 0;

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
        (row: Row) => row.Inv(loc, i as nat));
  
      lseq_give_inout(inout row_mutexes, i as uint64, m);

      i := i + 1;
    }

    assert token.val == SSM.unit().(insert_capacity := Capacity()) by {
      reveal InitResoucePartial();
    }

    glinear var mutex_token := T.inout_split(inout token, SSM.unit(), SSM.unit().(insert_capacity := Capacity()));

    linear var cap_mutex := new_mutex<Cap>(Cap(CapacityImpl() as nat, mutex_token),
      (cap: Cap) => cap.Inv(loc));

    glinear var handles := glmap_empty<Index, MutexHandle<Row>>();

    v := Variables.Variables(
      token,
      handles);

    iv := IVariables(row_mutexes, cap_mutex);
  }
}
