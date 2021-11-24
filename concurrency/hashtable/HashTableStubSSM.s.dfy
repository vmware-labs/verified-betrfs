include "../framework/AsyncSSM.s.dfy"
include "../framework/StateMachines.s.dfy"
include "CircularTable.i.dfy"

module HashTableStubSSM refines TicketStubSSM(MapIfc)
{
  import opened NativeTypes
  import opened Options
  import opened KeyValueType
  import opened Limits
  import opened MapIfc
  import opened CircularRange
  import opened CircularTable

  datatype M =
    | Variables(table: FixedTable,
        insert_capacity: nat,
        reqs: map<RequestId, MapIfc.Input>,
        resps: map<RequestId, MapIfc.Output>)
    | Fail
  {
    predicate HasReq(rid: RequestId, input: MapIfc.Input)
      requires Variables?
    {
      && rid in reqs
      && reqs[rid] == input
    }

    //////////////////////////////////////////////////////////////////////////////
    // Transition definitions
    //////////////////////////////////////////////////////////////////////////////

    // Insert transitions
  
    predicate InsertEnable(step: Step)
    {
      && Variables?
      && step.InsertStep?
      && var InsertStep(rid, input, start, end) := step;
      && HasReq(rid, input)
      && input.InsertInput?
      && insert_capacity >= 1

      && var p_range := Partial(hash(input.key), start);
      && KeyAbsentProbeRange(table, input.key, p_range)
      // this part is full
      && RangeFull(table, Partial(start, end))
      // but the end is empty 
      && SlotEmpty(table[end])
    }

    function Insert(step: Step): M
      requires InsertEnable(step)
    {
      var InsertStep(rid, input, start, end) := step;
      var entry := Some(Full(input.key, input.value));
      var table' := TableRightShift(table, entry, start, end);
      this.(table := table')
        .(insert_capacity := insert_capacity - 1)
        .(reqs := reqs - {rid})
        .(resps := resps[rid := MapIfc.InsertOutput(true)])
    }

    predicate OverwriteEnable(step: Step)
    {
      && Variables?
      && step.OverwriteStep?
      && var OverwriteStep(rid, input, end) := step;
      && HasReq(rid, input)
      && input.InsertInput?
      
      // the entry at end index has the same key
      && SlotFull(table[end])
      && table[end].value.key == input.key
    }

    function Overwrite(step: Step): M
      requires OverwriteEnable(step)
    {
      var OverwriteStep(rid, input, end) := step;
      var entry := Some(Full(input.key, input.value));
      this.(reqs := reqs - {rid})
        .(resps := resps[rid := MapIfc.InsertOutput(true)])
        .(table := table[end := entry])
    }

    // Query transitions

    predicate QueryFoundEnable(step: Step)
    {
      && Variables?
      && step.QueryFoundStep?
      && var QueryFoundStep(rid, input, end) := step;
      && HasReq(rid, input)
      && input.QueryInput?
  
      && SlotFullWithKey(table[end], input.key)
    }

    function QueryFound(step: Step): M
      requires QueryFoundEnable(step)
    {
      var QueryFoundStep(rid, input, i) := step;
      this.(reqs := reqs - {rid})
        .(resps := resps[rid := MapIfc.QueryOutput(Found(table[i].value.value))])
    }
  
    predicate QueryNotFoundEnable(step: Step)
    {
      && Variables?
      && step.QueryNotFoundStep?

      && var QueryNotFoundStep(rid, input, end) := step;
      && HasReq(rid, input)
      && input.QueryInput?
    
      && var p_range := Partial(hash(input.key), end);
      && KeyAbsentProbeRange(table, input.key, p_range)
    }

    function QueryNotFound(step: Step): M
      requires QueryNotFoundEnable(step)
    {
      var QueryNotFoundStep(rid, input, end) := step;
      this.(reqs := reqs - {rid})
      .(resps := resps[rid := MapIfc.QueryOutput(NotFound)])
    }

    // Remove transitions

    predicate RemoveEnable(step: Step)
    {
      && Variables?
      && step.RemoveStep?

      && var RemoveStep(rid, input, start, end) := step;
      && HasReq(rid, input)
      && input.RemoveInput?

      && ValidTidyRange(table, Partial(start, end), input.key)
    }

    function Remove(step: Step): M
      requires RemoveEnable(step)
    {
      var RemoveStep(rid, input, start, end) := step;
      this.(table := TableLeftShift(table, start, end))
        .(insert_capacity := insert_capacity + 1)
        .(reqs := reqs - {rid})
        .(resps := resps[rid := MapIfc.RemoveOutput(true)])
    }

    predicate RemoveNotFoundEnable(step: Step)
    {
      && Variables?
      && step.RemoveNotFoundStep?

      && var RemoveNotFoundStep(rid, input, end) := step;
      && HasReq(rid, input)
      && input.RemoveInput?
      && var p_range := Partial(hash(input.key), end);
      && KeyAbsentProbeRange(table, input.key, p_range)
    }

    function RemoveNotFound(step: Step): M
      requires RemoveNotFoundEnable(step)
    {
      var RemoveNotFoundStep(rid, input, end) := step;
      this.(reqs := reqs - {rid})
        .(resps := resps[rid := MapIfc.RemoveOutput(false)])
    }

    // All transitions

    predicate NextEnable(step: Step)
    {
      if step.InsertStep? then InsertEnable(step)
      else if step.OverwriteStep? then OverwriteEnable(step)
      else if step.QueryFoundStep? then QueryFoundEnable(step)
      else if step.QueryNotFoundStep? then QueryNotFoundEnable(step)
      else if step.RemoveStep? then RemoveEnable(step)
      else if step.RemoveNotFoundStep? then RemoveNotFoundEnable(step)
      else false
    }

    function GetNext(step: Step) : M
      requires NextEnable(step)
    {
      if step.InsertStep? then Insert(step)
      else if step.OverwriteStep? then Overwrite(step)
      else if step.QueryFoundStep? then QueryFound(step)
      else if step.QueryNotFoundStep? then QueryNotFound(step)
      else if step.RemoveStep? then Remove(step)
      else if step.RemoveNotFoundStep? then RemoveNotFound(step)
      else Fail
    }
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

  function dot(x: M, y: M) : M
  {
    if x.Variables? && y.Variables?
      && nonoverlapping(x.table, y.table)
      && x.reqs.Keys !! y.reqs.Keys
      && x.resps.Keys !! y.resps.Keys
    then (
      Variables(fuse_seq(x.table, y.table),
          x.insert_capacity + y.insert_capacity,
          x.reqs + y.reqs,
          x.resps + y.resps)
    ) else (
      Fail
    )
  }

  function unit(): M
  {
    Variables(UnitTable(), 0, map[], map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input): M
  {
    unit().(reqs := map[rid := input])
  }

  function Stub(rid: RequestId, output: IOIfc.Output) : M
  {
    unit().(resps := map[rid := output])
  }
  
  predicate IsStub(rid: RequestId, output: IOIfc.Output, stub: M)
  {
    stub== Stub(rid, output) 
  }

  function OneRowTable(i: Index, entry: Entry) : FixedTable
  {
    UnitTable()[i := Some(entry)]
  }

  function OneRowResource(i: Index, entry: Entry) : M 
  {
    Variables(OneRowTable(i, entry), 0, map[], map[])
  }

  function request_ids_in_use(m: M) : set<RequestId>
  {
    if m.Fail? then
      {}
    else
      (set rid | rid in m.reqs :: rid) +
      (set rid | rid in m.resps :: rid)
  }

  function Init(): M
  {
    Variables(
      EmptyTable(),
      Capacity(), map[], map[])
  }

  datatype Step =
    | InsertStep(rid: RequestId, input: Input, start: Index, end: Index)
    | OverwriteStep(rid: RequestId, input: Input, end: Index)

    | QueryFoundStep(rid: RequestId, input: Input, i: Index)
    | QueryNotFoundStep(rid: RequestId, input: Input, end: Index)

    | RemoveStep(rid: RequestId, input: Input, start: Index, end: Index)
    | RemoveNotFoundStep(rid: RequestId, input: Input, end: Index)

  predicate NextStep(v: M, v': M, step: Step)
  {
    && v.NextEnable(step)
    && v' == v.GetNext(step)
  }

  predicate Internal(shard: M, shard': M)
  {
    exists step :: NextStep(shard, shard', step)
  }

  predicate QuantityInv(s: M)
    requires s.Variables?
  {
    && TableQuantity(s.table) + s.insert_capacity == Capacity()
  }

  predicate Inv(s: M)
  {
    && s.Variables?
    && TableInv(s.table)
    && QuantityInv(s)
    && s.reqs.Keys !! s.resps.Keys
  }

  lemma InitImpliesInv(s: M)
  {
    var table := s.table;
    EmptyTableQuantity(table);
    forall i: Index
      ensures ExistsHashSegment(table, i)
    {
      var range := Partial(0, 0);
      assert ValidHashSegment(table, i, range);
    }
  }

  lemma InvImpliesEmptySlot(s: M) returns (e: Index)
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

  lemma InvImpliesEmptySlots(s: M) returns (e1: Index, e2: Index)
    requires Inv(s)
    ensures s.table[e1].value.Empty?
    ensures s.table[e2].value.Empty?
    ensures e1 != e2
  {
    var table := s.table;
    calc {
      TableQuantity(table);
      == 
      Capacity() - s.insert_capacity;
      <=
      Capacity();
      <=
      FixedSize() - 2;
    }

    e1 := InvImpliesEmptySlot(s);

    if forall e2: Index :: e2 != e1 ==> table[e2].value.Full? {
      SingleEmptyTableQuantity(table, e1);
      assert false;
    }
    assert exists e2: Index :: e2 != e1 && table[e2].value.Empty?;
    e2 :| e2 != e1 && table[e2].value.Empty?;
  }

  //////////////////////////////////////////////////////////////////////////////
  // Proof that Init && Next maintains Inv
  //////////////////////////////////////////////////////////////////////////////

  lemma InsertPreservesKeyUnique(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures KeysUnique(s'.table)
  {
    var InsertStep(rid, input, start, end) := step;
    var InsertInput(key, value) := input;
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

  lemma InsertEnableEnsuresEmptySlots(s: M, step: Step)
    returns (e: Index)
    requires Inv(s)
    requires s.InsertEnable(step)
    ensures SlotEmpty(s.table[e]) && e != step.end
  {
   var table := s.table;
   var end := step.end;

    calc {
      TableQuantity(table);
      == 
      Capacity() - s.insert_capacity;
      <=
      Capacity() - 1;
      ==
      FixedSize() - 3;
    }
    assert TableQuantity(s.table) <= FixedSize() - 2;
    assert SlotEmpty(s.table[end]);

    if forall e : Index :: e != end ==> SlotFull(table[e]) {
      var input := step.input;
      var full := table[end := Some(Full(input.key, input.value))];
      FullTableQuantity(full);
      TableQuantityReplace1(full, table, end);
      assert false;
    }

    var empt : Index :| empt != end && !SlotFull(table[empt]);
    return empt;
  }

  lemma InsertPreservesKeySegment(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures ExistsHashSegment(s'.table, hash(step.input.key))
  {
    var InsertStep(rid, input, start, end) := step;
    var InsertInput(key, value) := input;

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

  lemma InsertPreservesOtherSegment(s: M, s': M, step: Step, h: Index)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    requires h != hash(step.input.key)
    ensures ExistsHashSegment(s'.table, h);
  {
    var InsertStep(rid, input, start, end) := step;
    var InsertInput(key, value) := input;
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

  lemma InsertPreservesValidPSL(s: M, s': M, step: Step, i: Index)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    requires s'.table[i].value.Full?
    ensures ValidPSL(s'.table, i); 
  {
    var InsertStep(rid, input, start, end) := step;
    var InsertInput(key, value) := input;
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

  lemma InsertPreservesInv(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    var InsertStep(rid, input, start, end) := step;
    var InsertInput(key, value) := input;
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

  lemma OverwritePreservesInv(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.OverwriteStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    var OverwriteStep(rid, input, end) := step;
    var InsertInput(key, value) := input;
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

  lemma RemovePreservesKeySegment(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    ensures ExistsHashSegment(s'.table, hash(step.input.key))
  {
    var table, table' := s.table, s'.table;
    var RemoveStep(rid, input, start, end) := step;
    var key := input.key;
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

  lemma RemovePreservesOtherSegment(s: M, s': M, step: Step, h: Index)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    requires h != hash(step.input.key)
    ensures ExistsHashSegment(s'.table, h)
  {
    var table, table' := s.table, s'.table;
    var RemoveStep(rid, input, start, end) := step;
    var key := input.key;

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

  lemma RemovePreservesValidPSL(s: M, s': M, step: Step, i: Index)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    requires SlotFull(s'.table[i])
    ensures ValidPSL(s'.table, i)
  {
    var RemoveStep(rid, input, start, end) := step;
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

  lemma RemovePreservesInv(s: M, s': M, step: Step)
    requires Inv(s)
    requires step.RemoveStep? && NextStep(s, s', step)
    ensures Inv(s')
  {
    assert KeysUnique(s'.table);
    
    forall h: Index
      ensures ExistsHashSegment(s'.table, h);
    {
      if h == hash(step.input.key) {
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

  lemma NextStepPreservesInv(s: M, s': M)
  requires Inv(s)
  requires Internal(s, s')
  ensures Inv(s')
  {
    var step :| NextStep(s, s', step);
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

  lemma TransitionFailEquivalent(a: M, b: M, c: M)
    requires Internal(a, b)
    requires Inv(dot(a, c))
    ensures dot(b, c).Variables?
  {
    assert forall i: Index :: a.table[i].Some? <==> b.table[i].Some?;
    assert nonoverlapping(a.table, c.table) <==> nonoverlapping(b.table, c.table);
    var step :| NextStep(a, b, step);
    var rid := step.rid;
    assert rid !in c.resps;
  }

  lemma RemoveMonotonic(a: M, b: M, c: M, step: Step)
    requires NextStep(a, b, step)
    requires step.RemoveStep?
    requires Inv(dot(a, c))
    ensures NextStep(dot(a, c), dot(b, c), step)
  {
    var RemoveStep(rid, input, start, end) := step;
    var a' := dot(a, c);
    assert a.RemoveEnable(step);
    assert a'.RemoveEnable(step);
  }

  lemma InsertMonotonic(a: M, b: M, c: M, step: Step)
    requires NextStep(a, b, step)
    requires step.InsertStep?
    requires Inv(dot(a, c))
    ensures NextStep(dot(a, c), dot(b, c), step)
  {
    var InsertStep(rid, input, start, end) := step;
    var a' := dot(a, c);
    assert a.InsertEnable(step);
    assert a'.InsertEnable(step);
  }

  lemma TransitionMonotonic(a: M, b: M, c: M)
  requires Internal(a, b)
  requires Inv(dot(a, c))
  ensures Internal(dot(a, c), dot(b, c))
  {
    TransitionFailEquivalent(a, b, c);
    var step :| NextStep(a, b, step);
    if step.RemoveStep? {
      RemoveMonotonic(a, b, c, step);
    } else if step.InsertStep? {
      InsertMonotonic(a, b, c, step);
    } else {
      assert NextStep(dot(a, c), dot(b, c), step);
    }
  }

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  {
    TransitionMonotonic(shard, shard', rest);
    NextStepPreservesInv(dot(shard, rest), dot(shard', rest));
  }

  // lemma CompleteFullRangeImpossible(v: M, i: Index)
  //   requires Valid(v)
  //   requires v.table[PrevIndex(i)].Some?
  //   requires RangeFull(v.table, Partial(i, PrevIndex(i)))
  //   ensures SlotEmpty(v.table[PrevIndex(i)])
  // {
  //   var t :| Inv(add(v, t));

  //   var table1, table2 := v.table, t.table;
  //   var table3 := fuse_seq(table1, table2);
  //   assert TableInv(table3);
  //   assert table1 == table3;

  //   var last := PrevIndex(i);

  //   if table1[last].value.Full? {
  //     var e := InvImpliesEmptySlot(add(v, t));
  //     assert false;
  //   }
  // }

  lemma AlmostCompleteFullRangeImpossible(v: M, range: Range)
    requires exists t:M :: Inv(dot(v,t))
    requires range.AlmostComplete()
    requires v.table[range.end].Some?
    requires RangeFull(v.table, range)
    ensures false;
  {
    var t :| Inv(dot(v, t));

    var table1, table2 := v.table, t.table;
    var table3 := fuse_seq(table1, table2);
    assert TableInv(table3);
    assert table1 == table3;

    var e1, e2 := InvImpliesEmptySlots(dot(v, t));
    assert false;
  }

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  {
    assert dot(whole, Ticket(rid, input)) == 
      whole.(reqs := whole.reqs[rid := input]);
  }

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output, stub: M)
  {
    assert dot(whole', Stub(rid, output)) == 
      whole'.(resps := whole'.resps[rid := output]);
  }

  lemma dot_unit(x: M) {}

  lemma commutative(x: M, y: M)
  {
    if x.Variables? && y.Variables?
      && nonoverlapping(x.table, y.table)
      && x.reqs.Keys !! y.reqs.Keys
      && x.resps.Keys !! y.resps.Keys
    {
      assert fuse_seq(x.table, y.table) == fuse_seq(y.table, x.table);
      assert dot(x, y).reqs == dot(y, x).reqs;
      assert dot(x, y).resps == dot(y, x).resps;
    }
  }

  lemma associative(x: M, y: M, z: M)
  {
    if x.Variables? && y.Variables? && z.Variables?
    && nonoverlapping(x.table, y.table)
    && nonoverlapping(fuse_seq(x.table, y.table), z.table)
    && x.reqs.Keys !! y.reqs.Keys !! z.reqs.Keys
    && x.resps.Keys !! y.resps.Keys !! z.resps.Keys
    {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }

  lemma exists_inv_state() returns (s: M)
  {
    s := Variables(EmptyTable(), Capacity(), map[], map[]);
    assert s == Init();
    InitImpliesInv(s);
  }
}