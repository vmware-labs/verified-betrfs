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
    | InsertStep(ticket: Ticket, start: Index, end: Index)
    | OverwriteStep(ticket: Ticket, end: Index)

    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveStep(ticket: Ticket, start: Index, end: Index)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

// Insert transition definitions

  predicate InsertEnable(v: Variables, step: Step)
  {
    && v.Variables?
    && step.InsertStep?
    && var InsertStep(ticket, start, end) := step;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    && v.insert_capacity.value >= 1

    && var key := ticket.input.key;
    && var table := v.table;
    && ValidProbeRange(table, Partial(hash(key), start), key)
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

// Remove transition definitions
  predicate RemoveEnable(v: Variables, step: Step)
  {
    && step.RemoveStep?
    && var RemoveStep(ticket, start, end) := step;
    && v.Variables?
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

  predicate RemoveNotFoundEnable(v: Variables, step: Step)
  {
    && step.RemoveNotFoundStep?
    && var RemoveNotFoundStep(ticket, end) := step;
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && SlotEmpty(v.table[end])
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
    else if step.RemoveStep? then RemoveEnable(v, step)
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
    else if step.RemoveStep? then Remove(v, step)
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
    if !RangeFullKeyNotFound(table, range, key) {
      var i: Index :|
        && range.Contains(i)
        && !SlotFullKeyNotFound(table[i], key);
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

    ProbeRangeSufficient(s.table, Partial(h, start), key);

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
      ProbeRangeSufficient(s.table, Partial(h, start), key);
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
        RightShiftPSL(table, table', inserted, start, end, j);
      } else if Partial(NextIndex(end), start).Contains(j) {
        assert table'[j] == table[j];
      } else {
        assert table'[j] == inserted;
      }
    }

    assert ValidPSL(table', i);
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
    var table, table' := s.table, s'.table;
    var RemoveStep(ticket, start, end) := step;
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


/*
  lemma NextStepPreservesInv(s: Variables, s': Variables, step: Step)
  requires Inv(s)
  requires NextStep(s, s', step)
  ensures Inv(s')
  {
    if step.InsertStep? {
      InsertStepPreservesInv(s, s', step);
    } else if step.OverwriteStep? {
      OverwriteStepPreservesInv(s, s', step);
    } else if step.RemoveStep? {
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
