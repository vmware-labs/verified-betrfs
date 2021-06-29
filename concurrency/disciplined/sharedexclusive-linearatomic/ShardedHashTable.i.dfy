include "../../../lib/Lang/NativeTypes.s.dfy"
include "../../../lib/Base/Option.s.dfy"
include "../../../lib/Base/sequences.i.dfy"
include "../common/ConcurrencyModel.s.dfy"
include "../common/AppSpec.s.dfy"
include "../common/CountMonoid.i.dfy"

module ShardedHashTable refines ShardedStateMachine {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Limits
  import MapIfc
  import Count

//////////////////////////////////////////////////////////////////////////////
// Data structure definitions
//////////////////////////////////////////////////////////////////////////////

  import opened KeyValueType

  function DummyKey() : Key

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  type Index = i: int | 0 <= i < FixedSize()

  function NextIndex(i: Index): Index
  {
    if i == FixedSize() - 1 then 0 else i + 1
  }

  function PrevIndex(i: Index): Index
  {
    if i == 0 then FixedSize() - 1 else i - 1
  }

  function method hash(key: Key) : Index

  // This is the thing that's stored in the hash table at this row.
  datatype Entry =
    | Full(key: Key, value: Value)
    | Empty

  type Table = seq<Option<Entry>>

  type FixedTable = t: Table
    | |t| == FixedSize() witness *

  predicate Complete(table: FixedTable)
  {
    forall i: Index :: table[i].Some?
  }

  function unitTable(): Table
  {
    seq(FixedSize(), i => None)
  }

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
    Variables(unitTable(), Count.Variables(0), multiset{}, multiset{})
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

  function add(x: Variables, y: Variables) : Variables {
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
    && in_r.table == unitTable()
    && in_r.insert_capacity.value == 0
    && in_r.tickets == multiset { Ticket(rid, input) }
    && in_r.stubs == multiset { }
  }

//////////////////////////////////////////////////////////////////////////////
// Transition definitions
//////////////////////////////////////////////////////////////////////////////

  datatype Step =
    | InsertStep(ticket: Ticket, kv: (Key, Value), range: Range)
    | OverwriteStep(ticket: Ticket, kv: (Key, Value), end: Index)

    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveFoundStep(ticket: Ticket, range: Range)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

  function PSL(key: Key, i: Index): nat
  {
    var h := hash(key);
    if h <= i then
      i - h
    else
      FixedSize() - h + i
  }

  function SlotKeyHash(table: FixedTable, i: Index): Index
    requires table[i].Some? && table[i].value.Full?
  {
    hash(table[i].value.key)
  }

  function SlotPSL(table: FixedTable, i: Index): nat
    requires table[i].Some? && table[i].value.Full?
  {
    PSL(table[i].value.key, i)
  }

  type EntryPredicate = (Option<Entry>, Index, Key) -> bool

  // when start == end, we have a confusing case:
  // * it can be false (if we define the range to be nothing)
  // * it can be true (if we define the range to be everything)
  // we use the nothing definition for now, all is specified
  datatype Range =
    | Partial(start: Index, end: Index)
    | Complete
  {
    predicate Contains(i: Index)
    {
      if Complete? then
        true
      else if start <= end then
        (start <= i < end)
      else
        (start <= i || i < end)
    }

    function Complement(): Range
    {
      if Complete? then
        Partial(0, 0)
      else if start == end then
        Range.Complete
      else
        Partial(end, start)
    }
  }

  // if i is not in range, then i is in the copmlement (vice versa)
  lemma RangeComplement(i: Index, range: Range)
    ensures !range.Contains(i) == range.Complement().Contains(i);
  { 
  }

  predicate TrueInRange(table: FixedTable, range: Range, key: Key, p: EntryPredicate)
  {
    forall i: Index | range.Contains(i) :: p(table[i], i, key)
  }

// Insert transition definitions

  // NOTE: dummy_key does nothing here
  predicate SlotFull(entry: Option<Entry>, slot_index: Index, dummy_key: Key)
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

  predicate SlotShouldSkip(entry: Option<Entry>, slot_index: Index, insert_key: Key)
  {
    && SlotFullKeyNotFound(entry, slot_index, insert_key)
    // the psl at the slot is greater than the psl of the insert
    && PSL(entry.value.key, slot_index) > PSL(insert_key, slot_index)
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

  predicate IsTableRightShift(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index)
  {
    && (start <= end ==>
      && (forall i | 0 <= i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < |table'| :: table'[i] == table[i]))
    && (start > end ==>
      && table'[0] == table[ |table| - 1]
      && (forall i | 0 < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i < |table'| :: table'[i] == table[i-1]))
  }

  function TableRightShift(table: FixedTable, inserted: Option<Entry>, start: Index, end: Index) : (table': FixedTable)
    ensures IsTableRightShift(table, table', inserted, start, end)
  {
    if start <= end then
      table[..start] + [inserted] + table[start..end] + table[end+1..]
    else
      var last_index := |table| - 1;
      [table[last_index]] + table[..end] + table[end+1..start] + [inserted] + table[start..last_index]
  }

  predicate InsertEnable(v: Variables, step: Step)
  {
    && step.InsertStep?
    && var InsertStep(ticket, (key, _), range) := step;
    && v.Variables?
    && var table := v.table;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    && v.insert_capacity.value >= 1

    && range.Partial?
    && var Partial(start, end) := range;
    // skip upto (not including) start
    && RangeShouldSkip(table, Partial(hash(key), start), key)
    // insert at start
    && SlotShouldSwap(table[start], start, key)
    // this part is full
    && RangeFull(table, Partial(start, end))
    // but the end is empty 
    && table[end].Some?
    && table[end].value.Empty?
  }

  function Insert(v: Variables, step: Step): Variables
    requires InsertEnable(v, step)
  {
    var InsertStep(ticket, kv, range) := step;
    var table' := TableRightShift(v.table, Some(Full(kv.0, kv.1)), range.start, range.end);
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

  predicate IsTableLeftShift(table: FixedTable, table': FixedTable, start: Index, end: Index)
  {
    && (start <= end ==>
      && (forall i | 0 <= i < start :: table'[i] == table[i]) 
      && (forall i | start <= i < end :: table'[i] == table[i+1]) 
      && table'[end] == Some(Empty)
      && (forall i | end < i < |table'| :: table'[i] == table[i]))
    && (start > end ==>
      && (forall i | 0 <= i < end :: table'[i] == table[i+1])
      && table'[end] == Some(Empty)
      && (forall i | end < i < start :: table'[i] == table[i])
      && (forall i | start <= i < |table'| - 1 :: table'[i] == table[i+1])
      && table'[ |table'| - 1 ] == table[0])
  }

  function TableLeftShift(table: FixedTable, start: Index, end: Index): (table': FixedTable)
    ensures IsTableLeftShift(table, table', start, end)
  {
    if start <= end then
      table[..start] + table[start+1..end+1] + [Some(Empty)] + table[end+1..]
    else
      table[1..end+1] + [Some(Empty)] + table[end+1..start] + table[start+1..] + [table[0]]
  }

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

  // Keys are unique, although we don't count entries being removed
  predicate KeysUnique(table: FixedTable)
    requires Complete(table)
  {
    forall i: Index, j: Index | 
        && i != j
        && table[i].value.Full?
        && table[j].value.Full?
      :: table[i].value.key != table[j].value.key
  }

  predicate IsHashSegment(table: FixedTable, hash: Index, range: Range)
  requires Complete(table)
  {
    && range.Partial?
    // the hash is found in this range
    && (forall i: Index | range.Contains(i) ::
        && table[i].value.Full?
        && SlotKeyHash(table, i) == hash)
    // and no where else
    && (forall i: Index | !range.Contains(i) ::
        (table[i].value.Full? ==> 
        SlotKeyHash(table, i) != hash))
  }

  predicate ExistsHashSegment(table: FixedTable, hash: Index)
  requires Complete(table)
  {
    // there exists a segment of slots that has the matching hash (could be empty)
    exists range: Range :: IsHashSegment(table, hash, range)
  }

  predicate ValidHashSegments(table: FixedTable)
  requires Complete(table)
  {
    forall hash: Index :: ExistsHashSegment(table, hash)
  }

  function GetHashSegment(table: FixedTable, hash: Index): (Range)
  requires Complete(table)
  requires ValidHashSegments(table)
  ensures IsHashSegment(table, hash, GetHashSegment(table, hash))
  {
    assert ExistsHashSegment(table, hash);
    var range: Range :|
      IsHashSegment(table, hash, range);
    range
  }

  lemma ValidHashSegmentsImpliesDisjoint(table: FixedTable, h0: Index, h1: Index)
    requires h0 != h1
    requires Complete(table)
    requires ValidHashSegments(table)
    ensures !exists i : Index ::
      (&& GetHashSegment(table, h0).Contains(i)
      && GetHashSegment(table, h1).Contains(i))
  {
    var range0 := GetHashSegment(table, h0);
    var range1 := GetHashSegment(table, h1);

    forall i : Index | range0.Contains(i)
      ensures !range1.Contains(i)
    {
      assert table[i].value.Full?;
      assert SlotKeyHash(table, i) == h0;
      assert SlotKeyHash(table, i) != h1;
    }

    forall i : Index | range1.Contains(i)
      ensures !range0.Contains(i)
    {
      assert table[i].value.Full?;
      assert SlotKeyHash(table, i) == h1;
      assert SlotKeyHash(table, i) != h0;
    }
  }

  predicate ValidOrdering(table: FixedTable, h0: Index)
  requires Complete(table)
  requires ValidHashSegments(table)
  {
    var h1 := NextIndex(h0);
    var range0 := GetHashSegment(table, h0);
    var range1 := GetHashSegment(table, h1);

    // this part should all be empty (we won't have a segment in between)
    && (forall i : Index | Partial(range0.end, range1.start).Contains(i) ::
      table[i].value.Empty?)
  }

  predicate ValidPSL(table: FixedTable, i: Index)
    requires Complete(table)
  {
    table[i].value.Full? ==>
    (
      var key := table[i].value.key;
      var ih := SlotKeyHash(table, i);
      forall j: Index :: Partial(ih, i).Contains(j) ==> 
      (
        && table[j].value.Full?
        && SlotPSL(table, j) >= PSL(key, j)
      )
    )
  }

  predicate InvTable(table: FixedTable)
  {
    && Complete(table)
    && KeysUnique(table)
    && ValidHashSegments(table)
    && (forall h: Index :: ValidOrdering(table, h))
    && (forall i: Index :: ValidPSL(table, i))
  }

  function EntryQuantity(entry: Option<Entry>): nat
  {
    if entry.Some? && entry.value.Full? then 1 else 0
  }

  function {:opaque} TableQuantity(s: Table) : nat
  {
    if s == [] then
      0
    else
      (TableQuantity(s[..|s| - 1]) + EntryQuantity(Last(s)))
  }

  predicate TableQuantityInv(s: Variables)
  {
    && s.Variables?
    && TableQuantity(s.table) + s.insert_capacity.value == Capacity()
  }

  predicate Inv(s: Variables)
  {
    && s.Variables?
    && InvTable(s.table)
    && TableQuantityInv(s)
  }

  lemma FullTableQuantity(table: Table)
    requires forall i: int :: 
      0 <= i < |table| ==> (table[i].Some? && table[i].value.Full?)
    ensures TableQuantity(table) == |table|
  {
    reveal TableQuantity();
  }

  // lemma InvImpliesEmptySlot(s: Variables) returns (e: Index)
  //   requires Inv(s)
  //   ensures s.table[e].value.Empty?;
  // {
  //   var table := s.table;
  //   assert TableQuantity(table) <= Capacity();
  //   if forall i: Index :: table[i].value.Full? {
  //     FullTableQuantity(table);
  //     assert TableQuantity(table) == FixedSize();
  //     assert false;
  //   }
  //   assert exists e: Index :: table[e].value.Empty?;
  //   e :| table[e].value.Empty?;
  // }

//////////////////////////////////////////////////////////////////////////////
// Proof that Init && Next maintains Inv
//////////////////////////////////////////////////////////////////////////////

  lemma TableQuantityReplace1(t: Table, t': Table, i: Index)
    requires 0 <= i < |t| == |t'|
    requires forall j | 0 <= j < |t| :: i != j ==> t[j] == t'[j]
    ensures TableQuantity(t') == TableQuantity(t) + EntryQuantity(t'[i]) - EntryQuantity(t[i])
  {
    reveal_TableQuantity();
    var end := |t| - 1;
    if i == end {
      assert t[..end] == t'[..end];
    } else {
      TableQuantityReplace1(t[..end], t'[..end], i);
    }
  }

  lemma TableQuantityConcat(t1: Table, t2: Table)
    decreases |t2|
    ensures TableQuantity(t1) + TableQuantity(t2) == TableQuantity(t1 + t2)
  {
    var t := t1 + t2;

    if |t1| == 0 || |t2| == 0 {
      assert t == if |t1| == 0 then t2 else t1;
      reveal TableQuantity();
      return;
    }

    calc == {
      TableQuantity(t);
      {
        reveal TableQuantity();
      }
      TableQuantity(t[..|t| - 1]) + EntryQuantity(Last(t));
      {
        assert Last(t) == Last(t2);
      }
      TableQuantity(t[..|t| - 1]) + EntryQuantity(Last(t2));
      TableQuantity((t1 + t2)[..|t| - 1]) + EntryQuantity(Last(t2));
      {
        assert (t1 + t2)[..|t| - 1] == t1 + t2[..|t2| - 1];
      }
      TableQuantity(t1 + t2[..|t2| - 1]) + EntryQuantity(Last(t2));
      {
        TableQuantityConcat(t1, t2[..|t2| - 1]);
      }
      TableQuantity(t1) +  TableQuantity(t2[..|t2| - 1]) + EntryQuantity(Last(t2));
      {
        reveal TableQuantity();
      }
      TableQuantity(t1) +  TableQuantity(t2);
    }
  }

  lemma InsertStepPreservesTableQuantityInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    ensures  TableQuantityInv(s')
  {
    var InsertStep(ticket, kv, Partial(start, end)) := step;
    var table, table' := s.table, s'.table;
    var inserted := Some(Full(kv.0, kv.1));

    if start == end {
      TableQuantityReplace1(table, table', end);
      assert TableQuantityInv(s');
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

  lemma InsertStepPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires step.InsertStep? && NextStep(s, s', step)
    // ensures Inv(s')
  {
    var InsertStep(ticket, (key, _), range) := step;
    var Partial(start, end) := range;
    var table, table' := s.table, s'.table;

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

    // forall h: Index 
    //   ensures ExistsHashSegment(table', h)
    // {
    //   if h != hash(key) {
    //     assert ExistsHashSegment(table, h);
    //   } else {
    //     assume false;
    //   }
    // }

    // forall  ValidHashSegments(table');


    // if exists i : Index :: !ValidOrdering(table', i) {
    //   var i : Index, j: Index, ih: Index :|
    //     && table'[i].value.Full?
    //     && ih == SlotKeyHash(table', i)
    //     && Between(j, ih, i)
    //     && (
    //       || table'[j].value.Empty?
    //       || SlotPSL(table', j) < SlotPSL(table', i)
    //     );
      
    //   assume start <= end;
    //   // var i_next := NextIndex(i);
    //   var i_prev := PrevIndex(i);

    //   if table'[j].value.Empty? {
    //     assert ValidOrdering(table, i);
    //     assert table'[j] == table[j];
    //     assert Between(j, NextIndex(end), start);
    //     assert Between(i, start, NextIndex(end));
    //     assert ValidOrdering(table, i_prev);
    //     assert false;
    //   } else {
    //     if Between(i, NextIndex(end), start) {
    //       assert table[i] == table'[i];
    //       assert ValidOrdering(table, i);
    //       assert Between(ih, i, end);
    //       assert false;
    //     } else if Between(i, NextIndex(start), NextIndex(end)) {
    //       assert table[i_prev] == table'[i];
    //       assert ValidOrdering(table, i_prev);
    //       assert Between(ih, NextIndex(end), i);
    //       assert Between(j, ih, i);
    //     }
    //   }
    // }

    InsertStepPreservesTableQuantityInv(s, s', step);
  }
/*
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
    var RemoveFoundStep(ticket, start, end) := step;
    var key := ticket.input.key;
    var table, table' := s.table, s'.table;

    assert KeysUnique(table');

    assert table'[end].value.Empty?;

    if start <= end {
      if exists j: Index :: !ContiguousToEntry(table', j)
      {
        var j: Index, k: Index :|
          && table'[j].value.Full?
          && Between(k, hash(table'[j].value.key), j)
          && table'[k].value.Empty?;
        
        var l := NextIndex(end);
  
        if k != end {
          var j_prev := PrevIndex(j);
          var j_next := NextIndex(j);
          assert ContiguousToEntry(table, j);
          assert ContiguousToEntry(table, j_prev);
          assert ContiguousToEntry(table, j_next);
          assert false;
        } else {
          assume exists e0 : Index ::
            && table[e0].value.Empty?
            && (end < e0 || e0 < start);

          var e0 : Index :| table[e0].value.Empty?
            && (end < e0 || e0 < start);

          if j < start {
            assert table[j] == table'[j];
            assert ContiguousToEntry(table, j);
            var jh := SlotKeyHash(table, j);
            
            if e0 > end {
              assert ValidHashInSlot(table, e0, j);
              assert adjust(jh, e0) <= adjust(j, e0);
              assert false;
            }
      
            assert e0 < jh <= end;
            assert j < e0 < start; 
            assert table[l].value.Full?;
            assert ValidOrdering(table, e0, l, j);
            assert false;
          } else if j <= end {
            var j_prev := PrevIndex(j);
            // assert ContiguousToEntry(table, j);
            // assert ContiguousToEntry(table, j_prev);
            // assert table[l].value.Full?;
            // assert ValidOrdering(table, e0, l, j);
            // assert ValidOrdering(table, e0, l, j_prev);
            // assert false;
          }
          // var e := RemoveFoundStepPreservesEmptySlot(s, s', step);

          assume false;
        }
      }
    }


    // forall j: Index
    //   ensures true
    // {
    //   if start <= end {
    //     if 0 <= j < start {
    //       assert ContiguousToEntry(table, j);
    //       assert ContiguousToEntry(table', j);
    //     }
    //   } else {
    //     assume false;
    //   }
    //   // var e := InvImpliesEmptySlot(s);

    // }

    // forall e: Index, i: Index
    //   ensures ValidHashInSlot(table', e, i)
    // {
    //   var i_prev := PrevIndex(i);
    //   var i_next := NextIndex(i);
    //   assert ValidHashInSlot(table, e, i);
    //   assert ValidHashInSlot(table, e, i_prev);
    //   assert ValidHashInSlot(table, e, i_next);
    //   assert ContiguousToEntry(table', i);
    // }
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
*/
}
