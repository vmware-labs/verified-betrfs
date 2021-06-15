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

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  type Index = i: int | 0 <= i < FixedSize()

  datatype LeftShift = LeftShift(start: int, end: int)

  function method hash(key: Key) : Index

  // This is the thing that's stored in the hash table at this row.
  datatype Entry =
    | Full(key: Key, value: Value)
    | Empty

  type Table = seq<Option<Entry>>

  type FixedTable = t: Table
    | |t| == FixedSize() witness *

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

  function unitTable(): Table
  {
    seq(FixedSize(), i => None)
  }

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
    | InsertStep(ticket: Ticket, start: Index, end: Index)
    | OverwriteStep(ticket: Ticket, i: Index)

    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveStep(ticket: Ticket, start: Index, end: Index)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

// Insert transition definitions

  // unwrapped_index
  function adjust(i: Index, root: Index) : int
  {
    if i <= root then FixedSize() + i else i
  }

  // insert_h: hash of the key we are trying to insert
  // slot_h : hash of the key at slot_index
  // returns insert_h should go before slot_h 
  predicate ShouldHashGoBefore(search_h: int, slot_h: int, slot_idx: int)
  {
    || search_h < slot_h <= slot_idx // normal case
    || slot_h <= slot_idx < search_h // search_h wraps around the end of array
    || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  }

  type EntryPredicate = (Option<Entry>, Index, Key) -> bool

  predicate TrueInSubTableNoWrap(table: FixedTable, start: Index, end: int, key: Key, p: EntryPredicate)
    requires start <= end <= FixedSize();
  {
    forall i | start <= i < end :: p(table[i], i, key)
  }

  predicate IndexInRange(i: Index, start: Index, end: Index)
  {
    if start <= end then
      start <= i < end
    else
      start <= i < FixedSize() || 0 <= i < end
  }

  predicate TrueInSubTable(table: FixedTable, start: Index, end: Index, key: Key, p: EntryPredicate)
  {
    if start <= end then
      TrueInSubTableNoWrap(table, start, end, key, p)
    else (
      && TrueInSubTableNoWrap(table, start, FixedSize(), key, p)
      && TrueInSubTableNoWrap(table, 0, end, key, p)
    )
  }

  predicate TrueInTable(table: FixedTable, key: Key, p: EntryPredicate)
  {
    TrueInSubTableNoWrap(table, 0, FixedSize(), key, p)
  }

  // NOTE: key does nothing here
  predicate SlotFull(entry: Option<Entry>, slot_index: Index, key: Key)
  {
    entry.Some? && entry.value.Full?
  }

  // NOTE: key does nothing here
  predicate SubTableFull(table: FixedTable, start: Index, end: Index, key: Key)
  {
    TrueInSubTable(table, start, end, key, SlotFull)
  }

  predicate SlotFullKeyNotFound(entry: Option<Entry>, slot_index: Index, key: Key)
  {
    && SlotFull(entry, slot_index, key)
    && entry.value.key != key
  }

  predicate SubTableFullKeyNotFound(table: FixedTable, start: Index, end: Index, key: Key)
  {
    TrueInSubTable(table, start, end, key, SlotFullKeyNotFound)
  }

  predicate SlotShouldSkip(entry: Option<Entry>, slot_index: Index, insert_key: Key)
  {
    && SlotFullKeyNotFound(entry, slot_index, insert_key)
    && var insert_h := hash(insert_key);
    && var slot_h := hash(entry.value.key);
    !ShouldHashGoBefore(insert_h, slot_h, slot_index)
  }

  predicate SubTableShouldSkip(table: FixedTable, start: Index, end: Index, insert_key: Key)
  {
    TrueInSubTable(table, start, end, insert_key, SlotShouldSkip)
  }

  predicate SlotShouldSwap(entry: Option<Entry>, slot_index: Index, insert_key: Key)
  {
    && SlotFullKeyNotFound(entry, slot_index, insert_key)
    && ShouldHashGoBefore(hash(insert_key), hash(entry.value.key), slot_index)
  }

  predicate Complete(table: FixedTable)
  {
    forall i: Index :: table[i].Some?
  }

  predicate IsTableRightShift(table: FixedTable, table': FixedTable, inserted: Option<Entry>, start: Index, end: Index)
  {
    && (start <= end ==>
      && (forall i | 0 <= i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < |table'| :: table'[i] == table[i])
    )
    && (start > end ==>
      && table'[0] == table[ |table| - 1]
      && (forall i | 0 < i <= end :: table'[i] == table[i-1])
      && (forall i | end < i < start :: table'[i] == table[i])
      && table'[start] == inserted
      && (forall i | start < i < |table'| :: table'[i] == table[i-1])
    )
  }

  function TableRightShift(table: FixedTable, inserted: Option<Entry>, start: Index, end: Index) : (table': FixedTable)
    ensures IsTableRightShift(table, table', inserted, start, end)
  {
    if start == end then
      table[start := inserted]
    else if start < end then
      table[..start] + [inserted] + table[start..end] + table[end+1..]
    else
      var last_index := |table| - 1;
      [table[last_index]] + table[..end] + table[end+1..start] + [inserted] + table[start..last_index]
  }

  predicate InsertEnable(v: Variables, ticket: Ticket, kv: (Key, Value), start: Index, end: Index)
  {
    var (key, value) := kv;
    && v.Variables?
    && var table := v.table;
    && ticket in v.tickets
    && ticket.input.InsertInput?
    && v.insert_capacity.value >= 1

    // skip upto (not including) start
    && SubTableShouldSkip(table, hash(key), start, key)
    // insert at start
    && SlotShouldSwap(table[start], start, key)
    // this subtable is full
    && SubTableFull(table, start, end, key)
    // but the end is empty 
    && table[end].Some?
    && table[end].value.Empty?
  }
  
  function Insert(v: Variables, ticket: Ticket, kv: (Key, Value), start: Index, end: Index) : Variables
    requires InsertEnable(v, ticket, kv, start, end)
  {
    var table' := TableRightShift(v.table, Some(Full(kv.0, kv.1)), start, end);
    v.(tickets := v.tickets - multiset{ticket})
      .(insert_capacity := Count.Variables(v.insert_capacity.value - 1))
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
      .(table := table')
  }

  predicate IsInsert(v: Variables, v': Variables, ticket: Ticket, kv: (Key, Value), start: Index, end: Index)
  {
    && InsertEnable(v, ticket, kv, start, end)
    && v' == Insert(v, ticket, kv, start, end)
  }

//   predicate TableOverwriteEnable(table: FixedTable, key: Key, end: Index)
//   {
//     // the entry at end index has the same key
//     && table[end].Some?
//     && table[end].value.Full?
//     && table[end].value.key == key
//   }

//   predicate Overwrite(v: Variables, v': Variables, ticket: Ticket, kv: (Key, Value), end: Index)
//   {
//     var (key, value) := kv;
//     && v.Variables?
//     && ticket in v.tickets
//     && ticket.input.InsertInput?

//     && TableOverwriteEnable(v.table, key, end)

//     && v' == v
//       .(tickets := v.tickets - multiset{ticket})
//       .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
//       .(table := v.table[end := Some(Full(key, value))])
//   }

// // Query transition definitions

//   predicate QueryFound(v: Variables, v': Variables, ticket: Ticket, i: Index)
//   {
//     && v.Variables?
//     && v'.Variables?
//     && ticket in v.tickets
//     && ticket.input.QueryInput?
//     && v.table[i].Some?
//     && v.table[i].value.Full?
//     && v.table[i].value.key == ticket.input.key
//     && v' == v
//       .(tickets := v.tickets - multiset{ticket})
//       .(stubs := v.stubs + multiset{
//         Stub(ticket.rid, MapIfc.QueryOutput(Found(v.table[i].value.value)))})
//   }
  
//   predicate QueryNoutFound(v: Variables, v': Variables, ticket: Ticket, end: Index)
//   {
//     && v.Variables?
//     && v'.Variables?
//     && ticket in v.tickets
//     && ticket.input.QueryInput?

//     && v.table[end].Some?
//     && v.table[end].value.Empty?

//     && KeyNotFound(v.table, hash(ticket.input.key), end, ticket.input.key)
//     && v' == v
//       .(tickets := v.tickets - multiset{ticket})
//       .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.QueryOutput(NotFound))})
//   }

// // Remove transition definitions

//   predicate RemoveNotFound(v: Variables, v': Variables, ticket: Ticket, end: Index)
//   {
//     && v.Variables?
//     && v'.Variables?
//     && ticket in v.tickets
//     && ticket.input.RemoveInput?

//     && v.table[end].Some?
//     && v.table[end].value.Empty?

//     && KeyNotFound(v.table, hash(ticket.input.key), end, ticket.input.key)
//     && v' == v
//       .(tickets := v.tickets - multiset{ticket})
//       .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(false))})
//   }

//   predicate TableLeftShift(table: FixedTable, table': FixedTable, start: Index, end: Index)
//   {
//     && (start <= end ==>
//       && (forall i | 0 <= i < start :: table'[i] == table[i]) 
//       // shifted entries
//       && (forall i | start <= i < end :: table'[i] == table[i+1] && table'[i].Some?) 
//       && table'[end] == Some(Empty) 
//       && (forall i | end < i < |table'| :: table'[i] == table[i]) // untouched things
//     )
//     && (start > end ==>
//       && (forall i | 0 <= i < end :: table'[i] == table[i+1]) // shift second half 
//       && table'[end] == Some(Empty) // the end should be empty 
//       && (forall i | end < i < start :: table'[i] == table[i]) // untouched things
//       && (forall i | start <= i < |table'| - 1 :: table'[i] == table[i+1] && table'[i].Some?) // shift first half 
//       && table'[ |table'| - 1 ] == table[0] // shift around the wrap 
//     )
//   }

//   predicate Remove(v: Variables, v': Variables, ticket: Ticket, start: Index, end: Index)
//   {
//     && v.Variables?
//     && v'.Variables?
//     && ticket in v.tickets
//     && ticket.input.RemoveInput?
//     && v.table[start].Some?
//     && v.table[start].value.Full?
//     && v.table[start].value.key == ticket.input.key
//     && TableLeftShift(v.table, v'.table, start, end)
//     && v' == v.(table := v'.table)
//         .(tickets := v.tickets - multiset{ticket})
//         .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(true))})
//   }

// // All transitions

//   // predicate NextStep(v: Variables, v': Variables, step: Step)
//   // {
//   //   match step {
//   //     case InsertStep(ticket, stutters) => Insert(v, v', ticket, stutters)
//   //     case OverwriteStep(ticket, stutter) => Overwrite(v, v', ticket, stutter)
//   //     case QueryFoundStep(ticket, i) => QueryFound(v, v', ticket, i)
//   //     case QueryNotFoundStep(ticket, end) => QueryNotFound(v, v', ticket, end)
//   //     case RemoveStep(ticket, i, end) => Remove(v, v', ticket, i, end)
//   //     case RemoveNotFoundStep(ticket, end) => RemoveNotFound(v, v', ticket, end)
//   //   }
//   // }

//   // predicate Next(s: Variables, s': Variables)
//   // {
//   //   exists step :: NextStep(s, s', step)
//   // }

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

  predicate ValidHashInSlot(table: FixedTable, e: Index, i: Index)
    requires Complete(table)
  {
    // No matter which empty pivot cell 'e' we choose, every entry is 'downstream'
    // of the place that it hashes to.
    // Likewise for insert pointers and others
    (table[e].value.Empty? && table[i].value.Full?)
      ==>
    (
      var h := hash(table[i].value.key);
      adjust(h, e) <= adjust(i, e)
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashOrdering(table: FixedTable, e: Index, j: Index, k: Index)
    requires Complete(table)
  {
    (
      && table[e].value.Empty?
      && table[j].value.Full?
      && table[k].value.Full?
      && adjust(j, e) < adjust(k, e) 
    )
      ==>
    (
      var hj := hash(table[j].value.key);
      var hk := hash(table[k].value.key);
      adjust(hj, e) <= adjust(hk, e)
    )
  }

  predicate ContiguousToEntry(table: FixedTable, i: Index)
    requires Complete(table)
  {
    table[i].value.Full? ==>
    (
      var key := table[i].value.key;
      SubTableFullKeyNotFound(table, hash(key), i, key)
    )
  }

  predicate InvTable(table: FixedTable)
  {
    && Complete(table)
    && KeysUnique(table)
    && (forall e: Index, i: Index :: ValidHashInSlot(table, e, i))
    && (forall e: Index, j: Index, k: Index :: ValidHashOrdering(table, e, j, k))
    && (forall i: Index :: ContiguousToEntry(table, i))
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

// // //////////////////////////////////////////////////////////////////////////////
// // // Proof that Init && Next maintains Inv
// // //////////////////////////////////////////////////////////////////////////////

//   // lemma TableQuantityReplace1(t: Table, t': Table, i: Index)
//   //   requires 0 <= i < |t| == |t'|
//   //   requires forall j | 0 <= j < |t| :: i != j ==> t[j] == t'[j]
//   //   ensures TableQuantity(t') == TableQuantity(t) + EntryQuantity(t'[i]) - EntryQuantity(t[i])
//   // {
//   //   reveal_TableQuantity();
//   //   var end := |t| - 1;
//   //   if i == end {
//   //     assert t[..end] == t'[..end];
//   //   } else {
//   //     TableQuantityReplace1(t[..end], t'[..end], i);
//   //   }
//   // }

//   // lemma OverwriteStepPreservesInv(s: Variables, s': Variables, ticket: Ticket, kv: (Key, Value), end: Index)
//   //   requires Inv(s)
//   //   requires Overwrite(s, s', ticket, kv, end)
//   //   ensures Inv(s')
//   // {
//   //   var table, table' := s.table, s'.table;

//   //   forall e: Index, i: Index
//   //     ensures ValidHashInSlot(table', e, i)
//   //   {
//   //     assert ValidHashInSlot(table, e, i);
//   //   }

//   //   forall e: Index, j: Index, k: Index
//   //     ensures ValidHashOrdering(table', e, j, k)
//   //   {
//   //     assert ValidHashOrdering(table, e, j, k);
//   //     assert ValidHashInSlot(table, e, j);
//   //     assert ValidHashInSlot(table, e, k);
//   //   }

//   //   forall j : Index 
//   //     ensures ContiguousToEntry(table', j)
//   //   {
//   //     assert ContiguousToEntry(table, j);
//   //   }

//   //   TableQuantityReplace1(table, table', end);
//   // }

  lemma InsertStepPreservesInv(s: Variables, s': Variables, ticket: Ticket, kv: (Key, Value), start: Index, end: Index)
    requires Inv(s)
    requires IsInsert(s, s', ticket, kv, start, end)
  {
    var table, table' := s.table, s'.table;
    var key := kv.0;

    if !SubTableFullKeyNotFound(table, start, end, key) {
      var i: Index, entry: Option<Entry> :|
        && IndexInRange(i, start, end)
        && entry == table[i]
        && !SlotFullKeyNotFound(entry, i, key);
      assert SlotFull(entry, i, key);
      assert entry.value.key == key;
      assert ValidHashOrdering(table, end, start, i);
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
      assert ContiguousToEntry(table, index);
      assert ValidHashInSlot(table, end, index);
      assert false;
    }

    // HELP: after condensing this proof I am not sure whats going on
    forall e: Index, j: Index
      ensures ValidHashInSlot(table', e, j)
    {
      var j_prev := if j > 0 then j - 1 else |table| - 1;
      var j_next := if j + 1 < |table| then j + 1 else 0;
      assert ValidHashInSlot(table, e, j_prev);
      assert ValidHashInSlot(table, e, j);

      if table'[j].value.Full? && table'[j_next].value.Full? {
        if j != start && j_next != start && j == end {
          // two previously-separate contiguous regions are now joining.
          assert ContiguousToEntry(table, j_next);
        }
        assert ValidHashInSlot(table', e, j);
      }
    }

    // HELP: no idea whats going on
    if exists e: Index, j: Index, k: Index
      :: !ValidHashOrdering(table', e, j, k)
    {
      var e: Index, j: Index, k: Index :|
        && table'[e].value.Empty?
        && table'[j].value.Full?
        && table'[k].value.Full?
        && adjust(j, e) < adjust(k, e)
        && adjust(hash(table'[j].value.key), e) > adjust(hash(table'[k].value.key), e);
      
      var j_prev := if j > 0 then j - 1 else |table| - 1;
      var j_next := if j + 1 < |table| then j + 1 else 0;

      var k_prev := if k > 0 then k - 1 else |table| - 1;
      var k_next := if k + 1 < |table| then k + 1 else 0;

      assert ValidHashOrdering(table, e, j, k);
      assert ValidHashOrdering(table, e, j, k_prev);
      assert ValidHashOrdering(table, e, j, k_next);
      assert ValidHashOrdering(table, e, j_prev, k);
      assert ValidHashOrdering(table, e, j_prev, k_prev);
      assert ValidHashOrdering(table, e, j_prev, k_next);
      assert ValidHashOrdering(table, e, j_next, k);
      assert ValidHashOrdering(table, e, j_next, k_prev);
      assert ValidHashOrdering(table, e, j_next, k_next);
      assert ValidHashOrdering(table, end, j, k);
      assert ValidHashOrdering(table, end, j, k_prev);
      assert ValidHashOrdering(table, end, j, k_next);
      assert ValidHashOrdering(table, end, j_prev, k);
      assert ValidHashOrdering(table, end, j_prev, k_prev);
      assert ValidHashOrdering(table, end, j_prev, k_next);
      assert ValidHashOrdering(table, end, j_next, k);
      assert ValidHashOrdering(table, end, j_next, k_prev);
      assert ValidHashOrdering(table, end, j_next, k_next);
  
      assert ValidHashInSlot(table, e, j);
      assert ValidHashInSlot(table, e, j_prev);
      assert ValidHashInSlot(table, e, j_next);
  
      assert ValidHashInSlot(table, e, k);
      assert ValidHashInSlot(table, e, k_next);
      assert ValidHashInSlot(table, e, k_prev);
  
      assert ValidHashInSlot(table, end, j);
      assert ValidHashInSlot(table, end, j_prev);
      assert ValidHashInSlot(table, end, j_next);
  
      assert ValidHashInSlot(table, end, k);
      assert ValidHashInSlot(table, end, k_next);
      assert ValidHashInSlot(table, end, k_prev);

      assert false;
    }

    forall j : Index 
    ensures ContiguousToEntry(table', j)
    {
      var j_prev := if j > 0 then j - 1 else |table| - 1;
      var j_next := if j + 1 < |table| then j + 1 else 0;
      assert ContiguousToEntry(table, j);
      assert ContiguousToEntry(table, j_prev);
      assert ContiguousToEntry(table, j_next);
    }
  }

// //   lemma RemoveStepPreservesInv(s: Variables, s': Variables, ticket: Ticket, i: Index, end: Index)
// //     requires Inv(s)
// //     requires Remove(s, s',ticket, i, end)
// //     ensures Inv(s')
// //   {
// //     assume false;
// //   }

// //   lemma NextStepPreservesInv(s: Variables, s': Variables, step: Step)
// //   requires Inv(s)
// //   requires NextStep(s, s', step)
// //   ensures Inv(s')
// //   {
// //     match step {
// //       case InsertStep(ticket, stutters) => assume false;
// //       case OverwriteStep(ticket, stutter) => 
// //         OverwriteStepPreservesInv(s, s', ticket, stutter);
// //       case RemoveStep(ticket, i, end) =>
// //         RemoveStepPreservesInv(s, s', ticket, i, end);
// //       case _ => assert Inv(s');
// //     }
// //   }

// // //   lemma Next_PreservesInv(s: Variables, s': Variables)
// // //   requires Inv(s)
// // //   requires Next(s, s')
// // //   ensures Inv(s')
// // //   {
// // //     var step :| NextStep(s, s', step);
// // //     NextStep_PreservesInv(s, s', step);
// // //   }

// // // //////////////////////////////////////////////////////////////////////////////
// // // // fragment-level validity defined wrt Inv
// // // //////////////////////////////////////////////////////////////////////////////
// // //   predicate Valid(s: Variables)
// // //     ensures Valid(s) ==> s.Variables?
// // //   {
// // //     && s.Variables?
// // //     && exists t :: Inv(add(s, t))
// // //   }

// // //   lemma InvImpliesValid(s: Variables)
// // //     requires Inv(s)
// // //     ensures Valid(s)
// // //   {
// // //     // reveal Valid();
// // //     add_unit(s);
// // //   }

// // //   lemma EmptyTableQuantityIsZero(infos: Table)
// // //     requires (forall i | 0 <= i < |infos| :: infos[i] == Some(Empty))
// // //     ensures TableQuantity(infos) == 0
// // //   {
// // //     reveal_TableQuantity();
// // //   }

// // //   lemma InitImpliesValid(s: Variables)
// // //   //requires Init(s)
// // //   //ensures Valid(s)
// // //   {
// // //     EmptyTableQuantityIsZero(s.table);
// // //     InvImpliesValid(s);
// // //   }

// // //   lemma NextPreservesValid(s: Variables, s': Variables)
// // //   //requires Next(s, s')
// // //   //requires Valid(s)
// // //   ensures Valid(s')
// // //   {
// // //     // reveal Valid();
// // //     var t :| Inv(add(s, t));
// // //     InvImpliesValid(add(s, t));
// // //     update_monotonic(s, s', t);
// // //     Next_PreservesInv(add(s, t), add(s', t));
// // //   }

// // //   predicate TransitionEnable(s: Variables, step: Step)
// // //   {
// // //     match step {
// // //     }
// // //   }

// // //   function GetTransition(s: Variables, step: Step): (s': Variables)
// // //     requires TransitionEnable(s, step)
// // //     ensures NextStep(s, s', step);
// // //   {
// // //     match step {
// // //     }
// // //   }

// // //   // Reduce boilerplate by letting caller provide explicit step, which triggers a quantifier for generic Next()
// // //   glinear method easy_transform_step(glinear b: Variables, ghost step: Step)
// // //   returns (glinear c: Variables)
// // //     requires TransitionEnable(b, step)
// // //     ensures c == GetTransition(b, step)
// // //   {
// // //     var e := GetTransition(b, step);
// // //     c := do_transform(b, e);
// // //   }

// // //   lemma NewTicketPreservesValid(r: Variables, id: int, input: Ifc.Input)
// // //     //requires Valid(r)
// // //     ensures Valid(add(r, input_ticket(id, input)))
// // //   {
// // //     // reveal Valid();
// // //     var ticket := input_ticket(id, input);
// // //     var t :| Inv(add(r, t));

// // //     assert add(add(r, ticket), t).table == add(r, t).table;
// // //     assert add(add(r, ticket), t).insert_capacity == add(r, t).insert_capacity;
// // //   }

// // //   // Trusted composition tools. Not sure how to generate them.
// // //   glinear method {:extern} enclose(glinear a: Count.Variables) returns (glinear h: Variables)
// // //     requires Count.Valid(a)
// // //     ensures h == unit().(insert_capacity := a)

// // //   glinear method {:extern} declose(glinear h: Variables) returns (glinear a: Count.Variables)
// // //     requires h.Variables?
// // //     requires h.table == unitTable() // h is a unit() except for a
// // //     requires h.tickets == multiset{}
// // //     requires h.stubs == multiset{}
// // //     ensures a == h.insert_capacity
// // // */  
}
