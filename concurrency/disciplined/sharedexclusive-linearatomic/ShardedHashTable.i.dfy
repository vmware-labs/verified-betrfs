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

  function OneRowTable(i: Index, entry: Entry) : FixedTable
  {
    UnitTable()[i := Some(entry)]
    // seq(FixedSize(), j => if i == j then Some(entry) else None)
  }

  function OneRowResource(i: Index, entry: Entry, cap: nat) : Variables 
  {
    Variables(OneRowTable(i, entry), Count.Variables(cap), multiset{}, multiset{})
  }

//////////////////////////////////////////////////////////////////////////////
// Transition definitions
//////////////////////////////////////////////////////////////////////////////

  datatype Step =
    | InsertStep(ticket: Ticket, start: Index, end: Index)
    | OverwriteStep(ticket: Ticket, end: Index)

    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveStep(ticket: Ticket, start: Index, end: Index)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

// Insert transitions

  predicate InsertEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.InsertStep?
    && var InsertStep(ticket, start, end) := step;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    && v.insert_capacity.value >= 1

    && var table := v.table;
    && var p_range := Partial(hash(ticket.input.key), start);
    && ValidProbeRange(table, ticket.input.key, p_range)
    // this part is full
    && RangeFull(table, Partial(start, end))
    // but the end is empty 
    && SlotEmpty(table[end])
  }

  function Insert(v: Variables, step: Step): Variables
    requires InsertEnable(v, step)
  {
    var InsertStep(ticket, start, end) := step;
    var entry := Some(Full(ticket.input.key, ticket.input.value));
    var table' := TableRightShift(v.table, entry, start, end);
    v.(table := table')
      .(insert_capacity := Count.Variables(v.insert_capacity.value - 1))
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
  }

  predicate OverwriteEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.OverwriteStep?
    && var OverwriteStep(ticket, end) := step;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    
    // the entry at end index has the same key
    && SlotFull(v.table[end])
    && v.table[end].value.key == ticket.input.key
  }

  function Overwrite(v: Variables, step: Step): Variables
    requires OverwriteEnable(v, step)
  {
    var OverwriteStep(ticket, end) := step;
    var entry := Some(Full(ticket.input.key, ticket.input.value));
    v.(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
      .(table := v.table[end := entry])
  }

// Query transitions

  predicate QueryFoundEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.QueryFoundStep?

    && var QueryFoundStep(ticket, end) := step;
    && ticket in v.tickets
    && ticket.input.QueryInput?
 
    && SlotFullWithKey(v.table[end], ticket.input.key)
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
    && v.Variables?
    && step.QueryNotFoundStep?

    && var QueryNotFoundStep(ticket, end) := step;
    && ticket in v.tickets
    && ticket.input.QueryInput?
    && var p_range := Partial(hash(ticket.input.key), end);
    && ValidProbeRange(v.table, ticket.input.key, p_range)
  }

  function QueryNotFound(v: Variables, step: Step): Variables
    requires QueryNotFoundEnable(v, step)
  {
    var QueryNotFoundStep(ticket, end) := step;
    v.(tickets := v.tickets - multiset{ticket})
    .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.QueryOutput(NotFound))})
  }

// Remove transitions

  predicate RemoveEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.RemoveStep?

    && var RemoveStep(ticket, start, end) := step;
    && ticket in v.tickets
    && ticket.input.RemoveInput?

    && ValidTidyRange(v.table, Partial(start, end), ticket.input.key)
  }

  function Remove(v: Variables, step: Step): Variables
    requires RemoveEnable(v, step)
  {
    var RemoveStep(ticket, start, end) := step;
    var table' := TableLeftShift(v.table, start, end);
    v.(table := table')
      .(insert_capacity := Count.Variables(v.insert_capacity.value + 1))
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(true))})
  }

  predicate RemoveNotFoundEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.RemoveNotFoundStep?

    && var RemoveNotFoundStep(ticket, end) := step;
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && var p_range := Partial(hash(ticket.input.key), end);
    && ValidProbeRange(v.table, ticket.input.key, p_range)
  }

  function RemoveNotFound(v: Variables, step: Step): Variables
    requires RemoveNotFoundEnable(v, step)
  {
    var RemoveNotFoundStep(ticket, end) := step;
    v.(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(false))})
  }

// All transitions

  predicate NextEnable(v: Variables, step: Step)
  {
    if step.InsertStep? then InsertEnable(v, step)
    else if step.OverwriteStep? then OverwriteEnable(v, step)
    else if step.QueryFoundStep? then QueryFoundEnable(v, step)
    else if step.QueryNotFoundStep? then QueryNotFoundEnable(v, step)
    else if step.RemoveStep? then RemoveEnable(v, step)
    else if step.RemoveNotFoundStep? then RemoveNotFoundEnable(v, step)
    else false
  }

  function GetNext(v: Variables, step: Step) : Variables
    requires NextEnable(v, step)
  {
    if step.InsertStep? then Insert(v, step)
    else if step.OverwriteStep? then Overwrite(v, step)
    else if step.QueryFoundStep? then QueryFound(v, step)
    else if step.QueryNotFoundStep? then QueryNotFound(v, step)
    else if step.RemoveStep? then Remove(v, step)
    else if step.RemoveNotFoundStep? then RemoveNotFound(v, step)
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
    requires s.Variables?
  {
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

  lemma InsertPreservesKeyUnique(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures KeysUnique(s'.table)
  {
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;
    var table, table' := s.table, s'.table;

    var range := Partial(start, end);
    if !RangeFullWithOtherKeys(table, range, key) {
      var i: Index :|
        && range.Contains(i)
        && !SlotFullWithOtherKey(table[i], key);
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

  lemma InsertEnableEnsuresEmptySlots(s: Variables, step: Step)
    returns (e: Index)
    requires Inv(s)
    requires InsertEnable(s, step)
    ensures SlotEmpty(s.table[e]) && e != step.end
  {
   var table := s.table;
   var end := step.end;

    calc {
      TableQuantity(table);
      == 
      Capacity() - s.insert_capacity.value;
      <=
      Capacity() - 1;
      ==
      FixedSize() - 2;
    }
    assert TableQuantity(s.table) <= FixedSize() - 2;
    assert SlotEmpty(s.table[end]);

    if forall e : Index :: e != end ==> SlotFull(table[e]) {
      var input := step.ticket.input;
      var full := table[end := Some(Full(input.key, input.value))];
      FullTableQuantity(full);
      TableQuantityReplace1(full, table, end);
      assert false;
    }

    var empt : Index :| empt != end && !SlotFull(table[empt]);
    return empt;
  }

  lemma InsertPreservesKeySegment(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures ExistsHashSegment(s'.table, hash(step.ticket.input.key))
  {
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;

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
    
    var p_range := Partial(hash(key), start);
    ProbeRangeSufficient(s.table, key, p_range);

    if hr_start == NextIndex(start) {
      var e := InsertEnableEnsuresEmptySlots(s, step);
      assert end == start;
      assert false;
    }

    assert ValidHashSegment(table', h, Partial(hr_start, NextIndex(start)));
  }

  lemma InsertPreservesOtherSegment(s: Variables, s': Variables, step: Step, h: Index)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    requires h != hash(step.ticket.input.key)
    ensures ExistsHashSegment(s'.table, h);
  {
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;
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
        ensures table'[i].value.Full? && SlotKeyHash(table'[i]) == h
      {
        var prev_i := PrevIndex(i);
        assert table'[i] == table[prev_i];
        assert h_range.Contains(prev_i);
      }

      forall i: Index | !h_range'.Contains(i)
        ensures (table'[i].value.Full? ==> SlotKeyHash(table'[i]) != h);
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
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;
    var inserted := Some(Full(key, value));
    var table, table' := s.table, s'.table;
    
    if Partial(NextIndex(start), NextIndex(end)).Contains(i) {
      assert table'[i] == table[PrevIndex(i)];
      assert ValidPSL(table, PrevIndex(i));

      var key_i := table'[i].value.key;
      var h_i := hash(key_i);

      forall j: Index | Partial(h_i, i).Contains(j)
      ensures
        && table'[j].value.Full?
        && SlotPSL(table', j) >= PSL(key_i, j)
      {
        if Partial(NextIndex(start), NextIndex(end)).Contains(j) {
          var e := InvImpliesEmptySlot(s);
          RightShiftPSL(table, table', inserted, start, end, j);
        }
      }
    }  else if Partial(NextIndex(end), start).Contains(i) {
      assert table'[i] == table[i];
      assert ValidPSL(table, i);
    } else {
      assert table'[i] == Some(Full(key, value));
    }
  }

  lemma InsertPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;
    var table, table' := s.table, s'.table;

    InsertPreservesKeyUnique(s, s', step);

    forall h: Index
      ensures ExistsHashSegment(s'.table, h);
    {
      if h == hash(key) {
        InsertPreservesKeySegment(s, s', step);
      } else {
        InsertPreservesOtherSegment(s, s', step, h);
      }
    }

    forall i: Index
      ensures ValidPSL(s'.table, i)
    {
      if s'.table[i].value.Full? {
        InsertPreservesValidPSL(s, s', step, i);
      }
    }

    RightShiftTableQuantity(table, table', Some(Full(key, value)), start, end);
  }

  lemma OverwritePreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.OverwriteStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    var OverwriteStep(ticket, end) := step;
    var InsertInput(key, value) := ticket.input;
    var table, table' := s.table, s'.table;

    assert KeysUnique(table');

    forall h: Index
      ensures ExistsHashSegment(table', h)
    {
      var h_range := GetHashSegment(table, h);
      assert ValidHashSegment(table', h, h_range);
    }

    forall i: Index
      ensures ValidPSL(table', i)
    {
      assert ValidPSL(table, i);
    }

    TableQuantityReplace1(table, table', end);
  }

  lemma RemovePreservesKeySegment(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    ensures ExistsHashSegment(s'.table, hash(step.ticket.input.key))
  {
    var table, table' := s.table, s'.table;
    var RemoveStep(ticket, start, end) := step;
    var key := ticket.input.key;
    var h := hash(key);

    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);
    var Partial(hr_start, hr_end) := h_range;
    var s_range := Partial(start, NextIndex(end));

    if s_range.HasNone() {
      var e := InvImpliesEmptySlot(s);
      assert false;
    }

    if h_range.DisjointsWith(s_range) {
      assert false;
    }

    var e := InvImpliesEmptySlot(s);
    TidyRangeSufficient(table, Partial(start, end), key);
    assert !h_range.Contains(NextIndex(end));

    var h_range' := Partial(hr_start, PrevIndex(hr_end));
    assert ValidHashSegment(table', h, h_range');
  }

  lemma RemovePreservesOtherSegment(s: Variables, s': Variables, step: Step, h: Index)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    requires h != hash(step.ticket.input.key)
    ensures ExistsHashSegment(s'.table, h)
  {
    var table, table' := s.table, s'.table;
    var RemoveStep(ticket, start, end) := step;
    var key := ticket.input.key;

    // the segment that shares the hash
    var h_range := GetHashSegment(table, h);
    var Partial(hr_start, hr_end) := h_range;
    var s_range := Partial(start, NextIndex(end));

    if s_range.HasNone() {
      var e := InvImpliesEmptySlot(s);
      assert false;
    }

    if h_range.DisjointsWith(s_range) {
      assert ValidHashSegment(table', h, h_range);
      return;
    }

    if h_range.IsSubOf(s_range) {
      var h_range' := h_range.LeftShift1();
      assert ValidHashSegment(table', h, h_range');
      return;
    }

    if h_range.IsSuperOf(s_range) {
      assert false;
    }

    if h_range.Contains(start) {
      assert false;
    }
    
    if h_range.Contains(end) {
      var e := InvImpliesEmptySlot(s);
      TidyRangeSufficient(table, Partial(start, end), key);
      assert false;
    }
  }

  lemma RemovePreservesValidPSL(s: Variables, s': Variables, step: Step, i: Index)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    requires SlotFull(s'.table[i])
    ensures ValidPSL(s'.table, i)
  {
    var RemoveStep(ticket, start, end) := step;
    var table, table' := s.table, s'.table;
    var next_end := NextIndex(end);
    var s_range := Partial(start, next_end);

    var key_i := table'[i].value.key;
    var h := hash(key_i);

    if Partial(start, end).Contains(i) {
      var old_i := NextIndex(i);
      assert ValidPSL(table, old_i);
      assert ValidPSL(table', i);
    } else if Partial(NextIndex(end), start).Contains(i) {
      assert ValidPSL(table, i);
      assert ValidPSL(table', i);
    } else {
      assert i == end;
      assert false;
    }
  }

  lemma RemovePreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    assert KeysUnique(s'.table);
    
    forall h: Index
      ensures ExistsHashSegment(s'.table, h);
    {
      if h == hash(step.ticket.input.key) {
        RemovePreservesKeySegment(s, s', step);
      } else {
        RemovePreservesOtherSegment(s, s', step, h);
      }
    }

    forall i: Index
      ensures ValidPSL(s'.table, i)
    {
      if s'.table[i].value.Full? {
        RemovePreservesValidPSL(s, s', step, i);
      }
    }

    LeftShiftTableQuantity(s.table, s'.table, step.start, step.end);
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, step: Step)
  requires Inv(s)
  requires NextStep(s, s', step)
  ensures Inv(s')
  {
    if step.InsertStep? {
      InsertPreservesInv(s, s', step);
    } else if step.OverwriteStep? {
      OverwritePreservesInv(s, s', step);
    } else if step.RemoveStep? {
      RemovePreservesInv(s, s', step);
    } else {
      assert Inv(s');
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
  {
    var step :| NextStep(s, s', step);
    NextStepPreservesInv(s, s', step);
  }

// //////////////////////////////////////////////////////////////////////////////
// // fragment-level validity defined wrt Inv
// //////////////////////////////////////////////////////////////////////////////

  predicate Valid(s: Variables)
    ensures Valid(s) ==> s.Variables?
  {
    && s.Variables?
    && exists t :: Inv(add(s, t))
  }

  // lemma FullTableValidImpossible(s: Variables)
  //   requires Valid(s)
  // {

  // }


  lemma InvImpliesValid(s: Variables)
    requires Inv(s)
    ensures Valid(s)
  {
    // reveal Valid();
    add_unit(s);
  }

  lemma InitImpliesValid(s: Variables)
    // requires Init(s)
    // ensures Valid(s)
  {
    var table := s.table;
    EmptyTableQuantity(table);
    forall i: Index
      ensures ExistsHashSegment(table, i)
    {
      var range := Partial(0, 0);
      assert ValidHashSegment(table, i, range);
    }
    // assert TableInv(table);
    InvImpliesValid(s);
  }

  lemma NextPreservesValid(s: Variables, s': Variables)
  //requires Next(s, s')
  //requires Valid(s)
  ensures Valid(s')
  {
    // reveal Valid();
    var t :| Inv(add(s, t));
    InvImpliesValid(add(s, t));
    update_monotonic(s, s', t);
    NextPreservesInv(add(s, t), add(s', t));
  }

  // Reduce boilerplate by letting caller provide explicit step, which triggers a quantifier for generic Next()
  glinear method easy_transform_step(glinear b: Variables, ghost step: Step)
  returns (glinear c: Variables)
    requires NextEnable(b, step)
    ensures c == GetNext(b, step)
  {
    var e := GetNext(b, step);
    assert NextStep(b, e, step);
    c := do_transform(b, e);
  }

  // lemma NewTicketPreservesValid(r: Variables, id: int, input: Ifc.Input)
  //   //requires Valid(r)
  //   ensures Valid(add(r, input_ticket(id, input)))
  // {
  //   // reveal Valid();
  //   var ticket := input_ticket(id, input);
  //   var t :| Inv(add(r, t));

  //   assert add(add(r, ticket), t).table == add(r, t).table;
  //   assert add(add(r, ticket), t).insert_capacity == add(r, t).insert_capacity;
  // }

  lemma NewTicketValid(id: int, input: Ifc.Input)
    ensures Valid(input_ticket(id, input))
  {
    var v := input_ticket(id, input);
    var v' := unit()
      .(table := EmptyTable())
      .(insert_capacity := Count.Variables(Capacity()));
    var s := add(v, v');

    var table := s.table;
    assert table == EmptyTable();
    EmptyTableQuantity(table);

    forall i: Index
      ensures && ValidPSL(table, i)
        && ExistsHashSegment(table, i)
    {
      var range := Partial(0, 0);
      assert ValidHashSegment(table, i, range);
      assert SlotEmpty(table[i]);
    }

    assert Inv(s);
  }

  // Trusted composition tools. Not sure how to generate them.
  glinear method {:extern} enclose(glinear a: Count.Variables) returns (glinear h: Variables)
    requires Count.Valid(a)
    ensures h == unit().(insert_capacity := a)

  glinear method {:extern} declose(glinear h: Variables) returns (glinear a: Count.Variables)
    requires h.Variables?
    requires h.table == UnitTable() // h is a unit() except for a
    requires h.tickets == multiset{}
    requires h.stubs == multiset{}
    ensures a == h.insert_capacity

  lemma CompleteProbeRangeImpossible(v: Variables, key: Key)
    requires Valid(v)
    requires 
      var key_hash := hash(key);
      && v.table[PrevIndex(key_hash)].Some?
      && ValidPartialProbeRange(v.table, key, Partial(key_hash, PrevIndex(key_hash)))
    ensures SlotEmpty(v.table[PrevIndex(hash(key))])
  {
    var t :| Inv(add(v, t));

    var table1, table2 := v.table, t.table;
    var table3 := fuse_seq(table1, table2);
    assert TableInv(table3);
    assert table1 == table3;

    var last := PrevIndex(hash(key));

    if table1[last].value.Full? {
      var e := InvImpliesEmptySlot(add(v, t));
      assert false;
    }
  }
}
