include "../common/ConcurrencyModel.s.dfy"
include "../common/AppSpec.s.dfy"
include "../common/CountMonoid.i.dfy"
include "CircularTable.i.dfy"

module ShardedHashTable refines ShardedStateMachine {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened KeyValueType
  import opened Limits
  import opened CircularRange
  import opened CircularTable

  import MapIfc
  import Count

//////////////////////////////////////////////////////////////////////////////
// Data structure definitions
//////////////////////////////////////////////////////////////////////////////

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  function DummyKey() : Key

  datatype Variables =
      | Variables(table: FixedTable,
          insert_capacity: Count.Variables,
          tickets: multiset<Ticket>,
          stubs: multiset<Stub>)
      | Fail
        // The NextStep disjunct is complex, but we'll show that as long
        // as the impl obeys them, it'll never land in Fail.
        // The state is here to "leave slack" in the defenition of add(),
        // so that we can push off the proof that we never end up failing
        // until UpdatePreservesValid. If we didn't do it this way, we'd
        // have to show that add is complete, which would entail sucking
        // the definition of update and proof of UpdatePreservesValid all
        // into the definition of add().

  function unit() : Variables
  {
    Variables(UnitTable(), Count.Variables(0), multiset{}, multiset{})
  }

  function input_ticket(id: int, input: Ifc.Input) : Variables
  {
    unit().(tickets := multiset{Ticket(id, input)})
  }

  function output_stub(id: int, output: Ifc.Output) : Variables
  {
    unit().(stubs := multiset{Stub(id, output)})
  }

  predicate nonoverlapping<A>(a: seq<Option<A>>, b: seq<Option<A>>)
  requires |a| == FixedSize()
  requires |b| == FixedSize()
  {
    forall i | 0 <= i < FixedSize() :: !(a[i].Some? && b[i].Some?)
  }

  function fuse<A>(a: Option<A>, b: Option<A>) : Option<A>
  {
    if a.Some? then a else b
  }

  function fuse_seq<A>(a: seq<Option<A>>, b: seq<Option<A>>) : seq<Option<A>>
  requires |a| == FixedSize()
  requires |b| == FixedSize()
  requires nonoverlapping(a, b)
  {
    seq(FixedSize(), i requires 0 <= i < |a| => fuse(a[i], b[i]))
  }

  function add(x: Variables, y: Variables) : Variables
  {
    if x.Variables? && y.Variables? && nonoverlapping(x.table, y.table) then (
      Variables(fuse_seq(x.table, y.table),
          Count.add(x.insert_capacity, y.insert_capacity),
          x.tickets + y.tickets,
          x.stubs + y.stubs)
    ) else (
      Fail
    )
  }

  lemma add_unit(x: Variables)
  ensures add(x, unit()) == x
  {
  }

  lemma commutative(x: Variables, y: Variables)
  ensures add(x, y) == add(y, x)
  {
    if x.Variables? && y.Variables? && nonoverlapping(x.table, y.table) {
      assert fuse_seq(x.table, y.table) == fuse_seq(y.table, x.table);
      assert add(x, y).tickets == add(y, x).tickets;
      assert add(x, y).stubs == add(y, x).stubs;
    }
  }

  lemma associative(x: Variables, y: Variables, z: Variables)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
    if x.Variables? && y.Variables? && z.Variables? && nonoverlapping(x.table, y.table)
        && nonoverlapping(fuse_seq(x.table, y.table), z.table)
    {
      assert add(x, add(y, z)) == add(add(x, y), z);
    }
  }
  predicate Init(s: Variables)
  {
    && s.Variables?
    && (forall i | 0 <= i < |s.table| :: s.table[i] == Some(Empty))
    && s.insert_capacity.value == Capacity()
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  predicate IsInputResource(in_r: Variables, rid: int, input: Ifc.Input)
  {
    && in_r.Variables?
    && in_r.table == UnitTable()
    && in_r.insert_capacity.value == 0
    && in_r.tickets == multiset { Ticket(rid, input) }
    && in_r.stubs == multiset { }
  }

//////////////////////////////////////////////////////////////////////////////
// Transition definitions
//////////////////////////////////////////////////////////////////////////////

  datatype Step =
    | InsertStep(ticket: Ticket, kv: (Key, Value), start: Index, end: Index)
    | OverwriteStep(ticket: Ticket, kv: (Key, Value), end: Index)

    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveFoundStep(ticket: Ticket, range: Range)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

// Insert transition definitions

  // NOTE: dummy_index/dummy_key does nothing here
  predicate SlotFull(entry: Option<Entry>, dummy_index: Index, dummy_key: Key)
  {
    entry.Some? && entry.value.Full?
  }

  predicate RangeFull(table: FixedTable, range: Range)
  {
    TrueInRange(table, range, DummyKey(), SlotFull)
  }

  predicate SlotFullKeyNotFound(entry: Option<Entry>, slot_index: Index, key: Key)
  {
    && SlotFull(entry, slot_index, key)
    && entry.value.key != key
  }

  predicate RangeFullKeyNotFound(table: FixedTable, range: Range, key: Key)
  {
    TrueInRange(table, range, key, SlotFullKeyNotFound)
  }

  predicate SlotEmpty(entry: Option<Entry>)
  {
    entry.Some? && entry.value.Empty?
  }

  predicate SlotShouldSkip(entry: Option<Entry>, slot_index: Index, insert_key: Key)
  {
    && SlotFullKeyNotFound(entry, slot_index, insert_key)
    // the psl at the slot is geq than the psl of insert
    && PSL(entry.value.key, slot_index) >= PSL(insert_key, slot_index)
  }

  predicate RangeShouldSkip(table: FixedTable, range: Range, insert_key: Key)
  {
    TrueInRange(table, range, insert_key, SlotShouldSkip)
  }

  predicate SlotShouldSwap(entry: Option<Entry>, slot_index: Index, insert_key: Key)
  {
    && SlotFullKeyNotFound(entry, slot_index, insert_key)
    // the psl at the slot is less than the psl of the insert
    && PSL(entry.value.key, slot_index) < PSL(insert_key, slot_index)
  }

  predicate InsertEnable(v: Variables, step: Step)
  {
    && step.InsertStep?
    && var InsertStep(ticket, (key, _), start, end) := step;
    && v.Variables?
    && var table := v.table;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    && v.insert_capacity.value >= 1

    // skip upto (not including) start
    && RangeShouldSkip(table, Partial(hash(key), start), key)
    // insert at start
    && (SlotShouldSwap(table[start], start, key)
      || SlotEmpty(table[start]))
    // this part is full
    && RangeFull(table, Partial(start, end))
    // but the end is empty 
    && SlotEmpty(table[end])
  }

  function Insert(v: Variables, step: Step): Variables
    requires InsertEnable(v, step)
  {
    var InsertStep(ticket, kv, start, end) := step;
    var table' := TableRightShift(v.table, Some(Full(kv.0, kv.1)), start, end);
    v.(table := table')
      .(insert_capacity := Count.Variables(v.insert_capacity.value - 1))
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
  }
/*
  predicate OverwriteEnable(v: Variables, step: Step)
  {
    && step.OverwriteStep?
    && var OverwriteStep(ticket, (key, _), end) := step;
    && v.Variables?
    && var table := v.table;

    && ticket in v.tickets
    && ticket.input.InsertInput?

    // the entry at end index has the same key
    && table[end].Some?
    && table[end].value.Full?
    && table[end].value.key == key
  }

  function Overwrite(v: Variables, step: Step): Variables
    requires OverwriteEnable(v, step)
  {
    var OverwriteStep(ticket, kv, end) := step;
    v.(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
      .(table := v.table[end := Some(Full(kv.0, kv.1))])
  }

// Query transition definitions

  predicate QueryFoundEnable(v: Variables, step: Step)
  {
    && step.QueryFoundStep?
    && var QueryFoundStep(ticket, i) := step;
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.QueryInput?
    && v.table[i].Some?
    && v.table[i].value.Full?
    && v.table[i].value.key == ticket.input.key
  }

  function QueryFound(v: Variables, step: Step): Variables
    requires QueryFoundEnable(v, step)
  {
    var QueryFoundStep(ticket, i) := step;
    v.(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{
        Stub(ticket.rid, MapIfc.QueryOutput(Found(v.table[i].value.value)))})
  }

  predicate QueryNotFoundEnable(v: Variables, step: Step)
  {
    && step.QueryNotFoundStep?
    && var QueryNotFoundStep(ticket, end) := step;
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.QueryInput?
    && v.table[end].Some?
    && v.table[end].value.Empty?
    && RangeFullKeyNotFound(v.table, hash(ticket.input.key), end, ticket.input.key)
  }

  function QueryNotFound(v: Variables, step: Step): Variables
    requires QueryNotFoundEnable(v, step)
  {
    var QueryNotFoundStep(ticket, end) := step;
    v.(tickets := v.tickets - multiset{ticket})
    .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.QueryOutput(NotFound))})
  }

// Remove transition definitions

  // NOTE dummy_key not being used
  predicate SlotShouldTidy(entry: Option<Entry>, slot_index: Index, dummy_key: Key)
  {
    && SlotFull(entry, slot_index, DummyKey())
    && hash(entry.value.key) != slot_index
  }

  predicate RangeShouldTidy(table: FixedTable, start: Index, end: Index)
  { 
    TrueInRange(table, start, end, DummyKey(), SlotShouldTidy)
  }

  predicate RemoveFoundEnable(v: Variables, step: Step)
  {
    && step.RemoveFoundStep?
    && var RemoveFoundStep(ticket, start, end) := step;
    var key := ticket.input.key;
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && v.table[start].Some?
    && v.table[start].value.Full?
    && v.table[start].value.key == key
  
    && var startNext := NextIndex(start);
    && var endNext := NextIndex(end);
    // should tidy this Range
    && RangeShouldTidy(v.table, startNext, endNext)
    // should stop at endNext
    && !SlotShouldTidy(v.table[endNext], endNext, key)
  }

  function RemoveFound(v: Variables, step: Step): Variables
    requires RemoveFoundEnable(v, step)
  {
    var RemoveFoundStep(ticket, start, end) := step;
    var table' := TableLeftShift(v.table, start, end);
    v.(table := table')
      .(insert_capacity := Count.Variables(v.insert_capacity.value + 1))
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(true))})
  }

  predicate RemoveNotFoundEnable(v: Variables, step: Step)
  {
    && step.RemoveNotFoundStep?
    && var RemoveNotFoundStep(ticket, end) := step;
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && v.table[end].Some?
    && v.table[end].value.Empty?
    && RangeFullKeyNotFound(v.table, hash(ticket.input.key), end, ticket.input.key)
  }

  function RemoveNotFound(v: Variables, step: Step): Variables
    requires RemoveNotFoundEnable(v, step)
  {
    var RemoveNotFoundStep(ticket, end) := step;
    v.(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(false))})
  }
*/

// All transitions

  predicate NextEnable(v: Variables, step: Step)
  {
    if step.InsertStep? then InsertEnable(v, step)
    // else if step.OverwriteStep? then OverwriteEnable(v, step)
    // else if step.QueryFoundStep? then QueryFoundEnable(v, step)
    // else if step.QueryNotFoundStep? then QueryNotFoundEnable(v, step)
    // else if step.RemoveFoundStep? then RemoveFoundEnable(v, step)
    // else if step.RemoveNotFoundStep? then RemoveNotFoundEnable(v, step)
    else false
  }

  function GetNext(v: Variables, step: Step) : Variables
    requires NextEnable(v, step)
  {
    if step.InsertStep? then Insert(v, step)
    // else if step.OverwriteStep? then Overwrite(v, step)
    // else if step.QueryFoundStep? then QueryFound(v, step)
    // else if step.QueryNotFoundStep? then QueryNotFound(v, step)
    // else if step.RemoveFoundStep? then RemoveFound(v, step)
    // else if step.RemoveNotFoundStep? then RemoveNotFound(v, step)
    else Fail
  }

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    && NextEnable(v, step)
    && v' == GetNext(v, step)
  }

  predicate Next(s: Variables, s': Variables)
  {
    exists step :: NextStep(s, s', step)
  }

//////////////////////////////////////////////////////////////////////////////
// global-level Invariant proof
//////////////////////////////////////////////////////////////////////////////

  predicate QuantityInv(s: Variables)
  {
    && s.Variables?
    && TableQuantity(s.table) + s.insert_capacity.value == Capacity()
  }

  predicate Inv(s: Variables)
  {
    && s.Variables?
    && TableInv(s.table)
    && QuantityInv(s)
  }

  lemma InvImpliesEmptySlot(s: Variables) returns (e: Index)
    requires Inv(s)
    ensures s.table[e].value.Empty?;
  {
    var table := s.table;
    assert TableQuantity(table) <= Capacity();
    if forall i: Index :: table[i].value.Full? {
      FullTableQuantity(table);
      assert TableQuantity(table) == FixedSize();
      assert false;
    }
    assert exists e: Index :: table[e].value.Empty?;
    e :| table[e].value.Empty?;
  }

//////////////////////////////////////////////////////////////////////////////
// Proof that Init && Next maintains Inv
//////////////////////////////////////////////////////////////////////////////

  lemma InsertPreservesQuantityInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures QuantityInv(s')
  {
    var InsertStep(ticket, kv, start, end) := step;
    var table, table' := s.table, s'.table;
    var inserted := Some(Full(kv.0, kv.1));

    if start == end {
      TableQuantityReplace1(table, table', end);
      assert QuantityInv(s');
    } else if start < end {
      calc == {
        TableQuantity(table);
        {
          assert table[..start] + table[start..end] + [table[end]] + table[end+1..] == table;
          TableQuantityConcat(table[..start] + table[start..end] + [table[end]], table[end+1..]);
          TableQuantityConcat(table[..start] + table[start..end], [table[end]]);
          TableQuantityConcat(table[..start], table[start..end]);
        }
        TableQuantity(table[..start]) + TableQuantity(table[start..end]) + TableQuantity([table[end]]) + TableQuantity(table[end+1..]);
        {
          reveal TableQuantity();
        }
        TableQuantity(table[..start]) + TableQuantity(table[start..end]) + TableQuantity(table[end+1..]);
      }

      calc == {
        TableQuantity(table');
        {
          assert table' == table[..start] + [inserted] + table[start..end] + table[end+1..];
          TableQuantityConcat(table[..start] + [inserted] + table[start..end], table[end+1..]);
          TableQuantityConcat(table[..start] + [inserted], table[start..end]);
          TableQuantityConcat(table[..start], [inserted]);
        }
        TableQuantity(table[..start]) + TableQuantity([inserted]) + TableQuantity(table[start..end]) + TableQuantity(table[end+1..]);
        {
          reveal TableQuantity();
        }
        TableQuantity(table) + 1;
      }
    } else {
      var last_index := |table| - 1;

      calc == {
        TableQuantity(table);
        {
          assert table == table[..end] + [table[end]] + table[end+1..start] + table[start..last_index] + [table[last_index]];
          TableQuantityConcat(table[..end] + [table[end]] + table[end+1..start] + table[start..last_index], [table[last_index]]);
          TableQuantityConcat(table[..end] + [table[end]] + table[end+1..start], table[start..last_index]);
          TableQuantityConcat(table[..end] + [table[end]], table[end+1..start]);
          TableQuantityConcat(table[..end], [table[end]]);
        }
        TableQuantity(table[..end]) + TableQuantity([table[end]]) + TableQuantity(table[end+1..start]) + TableQuantity(table[start..last_index]) + TableQuantity([table[last_index]]);
        {
          reveal TableQuantity();
        }
        TableQuantity(table[..end]) + TableQuantity(table[end+1..start]) + TableQuantity(table[start..last_index]) + TableQuantity([table[last_index]]);
      } 

      calc == {
        TableQuantity(table');
        {
          assert table' == [table[last_index]] + table[..end] + table[end+1..start] + [inserted] + table[start..last_index];
          TableQuantityConcat([table[last_index]] + table[..end] + table[end+1..start] + [inserted], table[start..last_index]);
          TableQuantityConcat([table[last_index]] + table[..end] + table[end+1..start], [inserted]);
          TableQuantityConcat([table[last_index]] + table[..end], table[end+1..start]);
          TableQuantityConcat([table[last_index]], table[..end]);
        }
        TableQuantity([table[last_index]]) + TableQuantity(table[..end]) + TableQuantity(table[end+1..start]) + TableQuantity([inserted]) + TableQuantity(table[start..last_index]);
        {
          reveal TableQuantity();
        }
        TableQuantity(table) + 1;
      }
    }
  }

  lemma InsertEnableEnsuresEmptySlots(s: Variables, step: Step)
    returns (e: Index)
    requires Inv(s)
    requires InsertEnable(s, step)
    ensures s.table[e].value.Empty? && e != step.end
  {
    calc {
      TableQuantity(s.table);
      == 
      Capacity() - s.insert_capacity.value;
      <=
      Capacity() - 1;
      ==
      FixedSize() - 2;
    }
    assert TableQuantity(s.table) <= FixedSize() - 2;
    // TODO: this should be "easy"
    assume false;
  }

  predicate ValidProbeRange(s: Variables, p_range: Range, key: Key)
  {
    && Inv(s)
    && p_range.Partial?
    && p_range.start == hash(key)
    && RangeShouldSkip(s.table, p_range, key)
    && (SlotEmpty(s.table[p_range.end])
      || SlotShouldSwap(s.table[p_range.end], p_range.end, key))
  }

  // a valid probe range would cover key's hash segment 
  lemma ProbeRangeSufficient(s: Variables, p_range: Range, key: Key)
    requires ValidProbeRange(s, p_range, key)
    ensures var h_range := GetHashSegment(s.table, hash(key));
      h_range.HasSome() ==> (
        && p_range.Contains(h_range.start)
        && h_range.end == p_range.end
      )
  {
    var table := s.table;
    var Partial(h, pr_end) := p_range;

    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);

    if h_range.HasNone() {
      return;
    }

    var Partial(hr_start, hr_end) := h_range;

    // narrow where hr_start is
    assert p_range.Contains(hr_start) by {
      assert ValidPSL(table, hr_start);
    }

    // narrow where hr_end is
    if !(p_range.Contains(hr_end) || hr_end == pr_end) {
      assert h_range.Contains(pr_end);
      assert false;
    }

    // fix where hr_end is
    if p_range.Contains(hr_end) {
      assert ValidPSL(table, hr_end);
      assert false;
    }

    assert hr_end == pr_end;
    assert p_range.Contains(hr_start);
  }

  lemma InsertPreservesKeySegment(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures ExistsHashSegment(s'.table, hash(step.kv.0))
  {
    var InsertStep(_, (key, _), start, end) := step;
    var table, table' := s.table, s'.table;
    var h := hash(key);

    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);

    // if there is no segment, then the singleton segment is valid
    if h_range.HasNone() {
      assert ValidHashSegment(table', h, Partial(start, NextIndex(start)));
      return;
    }

    var Partial(hr_start, hr_end) := h_range;

    // if the shift begins at h, then there should not be a valid h_range
    if h == start {
      assert ValidPSL(table, hr_start);
      assert false;
    }

    ProbeRangeSufficient(s, Partial(h, start), key);

    if hr_start == NextIndex(start) {
      var e := InsertEnableEnsuresEmptySlots(s, step);
      assert end == start;
      assert false;
    }

    assert ValidHashSegment(table', h, Partial(hr_start, NextIndex(start)));
  }

  lemma InsertPreservesOtherSegments(s: Variables, s': Variables, step: Step, h: Index)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    requires h != hash(step.kv.0)
    ensures ExistsHashSegment(s'.table, h);
  {
    var InsertStep(_, (key, value), start, end) := step;
    var table, table' := s.table, s'.table;

    var range := Partial(start, end);
    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);

    // the segment was not toched at all (it could be empty in the first place)  
    if !h_range.OverlapsWith(range) {
      assert ValidHashSegment(table', h, h_range);
      return;
    }

    var Partial(hr_start, hr_end) := h_range;
    var h_range' := Partial(NextIndex(hr_start), NextIndex(hr_end));

    // the segment was shifted, but contained in the shift range
    if h_range.IsSubOf(range) {
      forall i: Index | h_range'.Contains(i)
        ensures table'[i].value.Full? && SlotKeyHash(table', i) == h
      {
        var prev_i := PrevIndex(i);
        assert table'[i] == table[prev_i];
        assert h_range.Contains(prev_i);
      }

      forall i: Index | !h_range'.Contains(i)
        ensures (table'[i].value.Full? ==> SlotKeyHash(table', i) != h);
      {
        var prev_i := PrevIndex(i);
        assert || table'[i] == table[prev_i]
          || table'[i] == table[i]
          || table'[i] == Some(Full(key, value));

        if table'[i] == table[prev_i] {
          assert !h_range.Contains(prev_i);
        } else if table'[i] == table[i] {
          assert !h_range.Contains(i);
        }
      }
      assert ValidHashSegment(table', h, h_range');
      return;
    }

    // if hr_start is in range, and h_range is not a subset
    // hr_end would corss the end, which should be empty
    if range.Contains(hr_start) {
      assert false;
      return;
    }

    assert Partial(start, NextIndex(end)).Contains(hr_end);
    assert h_range.Contains(start);

    var pre_start := PrevIndex(start);
    assert ValidPSL(table, pre_start); 
    
    assert hash(table[pre_start].value.key) != 
      hash(table[start].value.key);
    assert false;
  }

  lemma InsertPreservesValidPSL(s: Variables, s': Variables, step: Step, i: Index)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    requires s'.table[i].value.Full?
    ensures ValidPSL(s'.table, i); 
  {
    var InsertStep(_, (key, value), start, end) := step;
    var table, table' := s.table, s'.table;
    
    assert ValidPSL(table, i);

    // no shifting in the table, just an insert
    if start == end {
      // surprisingly this doesn't require more proofs
      assert ValidPSL(table', i);
      return;
    }

    // newly inserted
    if i == start {
      assert ValidPSL(table', i);
      return;
    }

    var h := hash(table'[i].value.key);

    // simple case where hash is at i
    if h == i {
      assert ValidPSL(table', i);
      return;
    }

    var h_range := GetHashSegment(table, h);

    // the range is none-empty, otherwise it should be newly inserted
    assert h_range.Partial?;

    // slot i is not shifted
    if table[i] == table'[i] {
      assert Partial(end, start).Contains(i);
      
      assert Partial(end, start).Contains(h);
      assert Partial(end, i).Contains(h)
        || Partial(i, start).Contains(h);
      
      if Partial(i, start).Contains(h) {
        assert Partial(start, i).Contains(end);
        assert Partial(h, i).Contains(end);
        assert false;
      }

      assert Partial(end, i).Contains(h);
      assert ValidPSL(table', i);
      return;
    }

    // slot i is shifted
    if table'[i].value.Empty? {
      return;
    }

    var key_i := table'[i].value.key;
    var h_i := hash(key_i);
    var prev_i := PrevIndex(i);

    if h_i == hash(key) {
      ProbeRangeSufficient(s, Partial(h, start), key);
      assert false;
      return;
    }

    assert table'[i] == table[prev_i];
    assert ValidPSL(table, prev_i);
    var inserted := Some(Full(key, value));

    forall j: Index | Partial(h_i, i).Contains(j)
    ensures
      && table'[j].value.Full?
      && SlotPSL(table', j) >= PSL(key_i, j)
    {
      var prev_j := PrevIndex(j);
      if Partial(NextIndex(start), NextIndex(end)).Contains(j) {
        assert table'[j] == table[prev_j];
        var h_j := hash(table[prev_j].value.key);
        if j == h_j {
          var e := InvImpliesEmptySlot(s);
          assert ValidPSL(table, PrevIndex(h_j));
          assert false;
        }
        RightShiftedPSL(table, table', inserted, start, end, j);
      } else if Partial(NextIndex(end), start).Contains(j) {
        assert table'[j] == table[j];
      } else {
        assert table'[j] == inserted;
      }
    }

    assert ValidPSL(table', i);
  }

  lemma InsertPreservesKeyUnique(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures KeysUnique(s'.table)
  {
    var InsertStep(ticket, (key, value), start, end) := step;
    var table, table' := s.table, s'.table;

    var range := Partial(start, end);
    if !RangeFullKeyNotFound(table, range, key) {
      var i: Index :|
        && range.Contains(i)
        && !SlotFullKeyNotFound(table[i], i, key);
      var s_key := table[start].value.key;

      var psl_at_s := PSL(s_key, start);
      var vpsl_at_s := PSL(key, start);

      assert psl_at_s >= vpsl_at_s by {
        assert ValidPSL(table, i);
      }
      assert false;
    }

    if !KeysUnique(table') {
      var i: Index, j: Index :| 
        && table'[i].value.Full?
        && table'[j].value.Full?
        && i != j
        && table'[i].value.key == table'[j].value.key;
      assert i == start || j == start;
      var index := if i == start then j else i;
      assert ValidPSL(table, index);
      assert false;
    }
  }

  lemma InsertPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    InsertPreservesKeyUnique(s, s', step);

    forall h: Index
      ensures ExistsHashSegment(s'.table, h);
    {
      if h == hash(step.kv.0) {
        InsertPreservesKeySegment(s, s', step);
      } else {
        InsertPreservesOtherSegments(s, s', step, h);
      }
    }

    forall i: Index
      ensures ValidPSL(s'.table, i)
    {
      if s'.table[i].value.Full? {
        InsertPreservesValidPSL(s, s', step, i);
      }
    }

    InsertPreservesQuantityInv(s, s', step);
  }

/*
  lemma OverwriteStepPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.OverwriteStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    var OverwriteStep(ticket, kv, end) := step;
    var table, table' := s.table, s'.table;

    forall e: Index, i: Index
      ensures ValidHashInSlot(table', e, i)
    {
      assert ValidHashInSlot(table, e, i);
    }

    forall e: Index, j: Index, k: Index
      ensures ValidOrdering(table', e, j, k)
    {
      assert ValidOrdering(table, e, j, k);
      assert ValidHashInSlot(table, e, j);
      assert ValidHashInSlot(table, e, k);
    }

    forall j : Index 
      ensures ContiguousToEntry(table', j)
    {
      assert ContiguousToEntry(table, j);
    }

    TableQuantityReplace1(table, table', end);
  }

  lemma RemoveFoundStepPreservesEmptySlot(s: Variables, s': Variables, step: Step) returns (i: Index)
    requires Inv(s)
    requires step.RemoveFoundStep? && NextStep(s, s', step)
    ensures s.table[i].value.Empty?
    ensures s'.table[i].value.Empty?
  {
    i := InvImpliesEmptySlot(s);
    var table, table' := s.table, s'.table;

    forall e: Index | table[e].value.Empty?
      ensures table'[e].value.Empty?
    {
    }
    
    assert table'[i].value.Empty?;
  }

  lemma RemoveFoundStepPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.RemoveFoundStep? && NextStep(s, s', step)
    // ensures Inv(s')
  {
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, step: Step)
  requires Inv(s)
  requires NextStep(s, s', step)
  ensures Inv(s')
  {
    if step.InsertStep? {
      InsertStepPreservesInv(s, s', step);
    } else if step.OverwriteStep? {
      OverwriteStepPreservesInv(s, s', step);
    } else if step.RemoveFoundStep? {
      assume false;
    } else {
      assert Inv(s');
    }
  }
*/

//   lemma Next_PreservesInv(s: Variables, s': Variables)
//   requires Inv(s)
//   requires Next(s, s')
//   ensures Inv(s')
//   {
//     var step :| NextStep(s, s', step);
//     NextStep_PreservesInv(s, s', step);
//   }

// //////////////////////////////////////////////////////////////////////////////
// // fragment-level validity defined wrt Inv
// //////////////////////////////////////////////////////////////////////////////
//   predicate Valid(s: Variables)
//     ensures Valid(s) ==> s.Variables?
//   {
//     && s.Variables?
//     && exists t :: Inv(add(s, t))
//   }

//   lemma InvImpliesValid(s: Variables)
//     requires Inv(s)
//     ensures Valid(s)
//   {
//     // reveal Valid();
//     add_unit(s);
//   }

//   lemma EmptyTableQuantityIsZero(infos: Table)
//     requires (forall i | 0 <= i < |infos| :: infos[i] == Some(Empty))
//     ensures TableQuantity(infos) == 0
//   {
//     reveal_TableQuantity();
//   }

//   lemma InitImpliesValid(s: Variables)
//   //requires Init(s)
//   //ensures Valid(s)
//   {
//     EmptyTableQuantityIsZero(s.table);
//     InvImpliesValid(s);
//   }

//   lemma NextPreservesValid(s: Variables, s': Variables)
//   //requires Next(s, s')
//   //requires Valid(s)
//   ensures Valid(s')
//   {
//     // reveal Valid();
//     var t :| Inv(add(s, t));
//     InvImpliesValid(add(s, t));
//     update_monotonic(s, s', t);
//     Next_PreservesInv(add(s, t), add(s', t));
//   }

//   predicate TransitionEnable(s: Variables, step: Step)
//   {
//     match step {
//     }
//   }

//   function GetTransition(s: Variables, step: Step): (s': Variables)
//     requires TransitionEnable(s, step)
//     ensures NextStep(s, s', step);
//   {
//     match step {
//     }
//   }

//   // Reduce boilerplate by letting caller provide explicit step, which triggers a quantifier for generic Next()
//   glinear method easy_transform_step(glinear b: Variables, ghost step: Step)
//   returns (glinear c: Variables)
//     requires TransitionEnable(b, step)
//     ensures c == GetTransition(b, step)
//   {
//     var e := GetTransition(b, step);
//     c := do_transform(b, e);
//   }

//   lemma NewTicketPreservesValid(r: Variables, id: int, input: Ifc.Input)
//     //requires Valid(r)
//     ensures Valid(add(r, input_ticket(id, input)))
//   {
//     // reveal Valid();
//     var ticket := input_ticket(id, input);
//     var t :| Inv(add(r, t));

//     assert add(add(r, ticket), t).table == add(r, t).table;
//     assert add(add(r, ticket), t).insert_capacity == add(r, t).insert_capacity;
//   }

//   // Trusted composition tools. Not sure how to generate them.
//   glinear method {:extern} enclose(glinear a: Count.Variables) returns (glinear h: Variables)
//     requires Count.Valid(a)
//     ensures h == unit().(insert_capacity := a)

//   glinear method {:extern} declose(glinear h: Variables) returns (glinear a: Count.Variables)
//     requires h.Variables?
//     requires h.table == unitTable() // h is a unit() except for a
//     requires h.tickets == multiset{}
//     requires h.stubs == multiset{}
//     ensures a == h.insert_capacity
//
}
