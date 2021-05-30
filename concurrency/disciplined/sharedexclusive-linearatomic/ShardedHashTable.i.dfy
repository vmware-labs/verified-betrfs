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

  // function oneRowTable(k: nat, entry: Entry) : Table
  // requires 0 <= k < FixedSize()
  // {
  //   seq(FixedSize(), i => if i == k then Some(entry) else None)
  // }

  // function oneRowResource(k: nat, entry: Entry, cap: nat) : Variables 
  // requires 0 <= k < FixedSize()
  // {
  //   Variables(oneRowTable(k, entry), Count.Variables(cap), multiset{}, multiset{})
  // }

  // function twoRowsTable(k1: nat, entry1: Entry, k2: nat, entry2: Entry) : Table
  // requires 0 <= k1 < FixedSize()
  // requires 0 <= k2 < FixedSize()
  // requires k1 != k2
  // {
  //   seq(FixedSize(), i => if i == k1 then Some(entry1) else if i == k2 then Some(entry2) else None)
  // }

  // function twoRowsResource(k1: nat, entry1: Entry, k2: nat, entry2: Entry, cap: nat) : Variables 
  // requires 0 <= k1 < FixedSize()
  // requires 0 <= k2 < FixedSize()
  // requires k1 != k2
  // {
  //   Variables(twoRowsTable(k1, entry1, k2, entry2), Count.Variables(cap), multiset{}, multiset{})
  // }

  predicate IsInputResource(in_r: Variables, rid: int, input: Ifc.Input)
  {
    && in_r.Variables?
    && in_r.table == unitTable()
    && in_r.insert_capacity.value == 0
    && in_r.tickets == multiset { Ticket(rid, input) }
    && in_r.stubs == multiset { }
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

//////////////////////////////////////////////////////////////////////////////
// Transition definitions
//////////////////////////////////////////////////////////////////////////////

  datatype Step =
    | QueryFoundStep(ticket: Ticket, i: Index)
    | QueryNotFoundStep(ticket: Ticket, end: Index)

    | RemoveStep(ticket: Ticket, i: Index, end: Index)
    | RemoveNotFoundStep(ticket: Ticket, end: Index)

    // | OverwriteStep(ticket: Ticket, i: int)
    // | InsertStep(ticket: Ticket, i: int)

  // insert_h: hash of the key we are trying to insert
  // slot_h : hash of the key at slot_index
  // returns insert_h should go before slot_h 
  // predicate ShouldHashGoBefore(insert_h: int, slot_h : int, slot_index: int)
  // {
  //   || insert_h < slot_h  <= slot_index // normal case
  //   || slot_h <= slot_index < insert_h // insert_h wraps around the end of array
  //   || slot_index < insert_h < slot_h // insert_h, slot_h  wrap around the end of array
  // }

  // predicate ShouldKeyGoBefore(insert_key: Key, slot_key: Key, slot_index: Index)
  // {
  //   && var insert_h := hash(insert_key)
  //   && var slot_h := hash(slot_key)
  //   (
  //     || insert_h < slot_h <= slot_index // normal case
  //     || slot_h <= slot_index < insert_h // insert_h wraps around the end of array
  //     || slot_index < insert_h < slot_h // insert_h, slot_h  wrap around the end of array
  //   )
  // }

  // Query

  predicate QueryFound(v: Variables, v': Variables, ticket: Ticket, i: Index)
  {
    && v.Variables?
    && v'.Variables?
    && ticket in v.tickets
    && ticket.input.QueryInput?
    && v.table[i].Some?
    && v.table[i].value.Full?
    && v.table[i].value.key == ticket.input.key
    && v' == v
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid,
          MapIfc.QueryOutput(Found(v.table[i].value.value)))})
  }

  predicate KeyNotFound(table: FixedTable, key: Key, end: Index)
  {
    && table[end].Some?
    && table[end].value.Empty?
    && var h := hash(key) as int;
    && (h <= end ==> forall j | h <= j < end     :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
    && (h > end  ==> forall j | h <= j < |table| :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
    && (h > end  ==> forall j | 0 <= j < end     :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
  }

  predicate QueryNotFound(v: Variables, v': Variables, ticket: Ticket, end: Index)
  {
    && v.Variables?
    && v'.Variables?
    && ticket in v.tickets
    && ticket.input.QueryInput?
    && KeyNotFound(v.table, ticket.input.key, end)
    && v' == v
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.QueryOutput(NotFound))})
  }

  // insert

  datatype InsertStutter = InsertStutter(key: Key, val: Value, start: Index, end: Index)

  predicate ShouldSkipSlot(table: FixedTable, insert_key: Key, slot_index: Index)
  {
    && table[slot_index].Some?
    && table[slot_index].value.Full?
    && var insert_h := hash(insert_key);
    && var slot_h := hash(table[slot_index].value.key);
    (
      || insert_h < slot_h <= slot_index // normal case
      || slot_h <= slot_index < insert_h // insert_h wraps around the end of array
      || slot_index < insert_h < slot_h // insert_h, slot_h  wrap around the end of array
    )
  }

  predicate ShouldSkipSlotsNoWrap(table: FixedTable, insert_key: Key, start: Index, end: int)
    requires start <= end <= FixedSize();
  {
    forall i | start <= i < end :: ShouldSkipSlot(table, insert_key, i)
  }

  predicate ShouldSkipSlots(table: FixedTable, step: InsertStutter)
  {
    var InsertStutter(insert_key, _, start, end) := step;
    && table[end].Some?
    && (if start <= end then
      ShouldSkipSlotsNoWrap(table, insert_key, start, end)
    else (
      && ShouldSkipSlotsNoWrap(table, insert_key, start, FixedSize())
      && ShouldSkipSlotsNoWrap(table, insert_key, 0, end)
    ))
  }

  predicate TableInsertSwapEnable(table: FixedTable, step: InsertStutter)
  {
    var InsertStutter(insert_key, _, _, end) := step;
    // we should skip these
    && ShouldSkipSlots(table, step)
    // the entry at end index should be swapped out
    && table[end].value.Full?
    && table[end].value.key != insert_key
    && !ShouldSkipSlot(table, insert_key, end)
  }

  predicate TableInsertDoneEnable(table: FixedTable, step: InsertStutter)
  {
    // we should skip these
    && ShouldSkipSlots(table, step)
    // the entry at end index is empty
    && table[step.end].value.Empty?
  }

  predicate TableInsertUpdateEnable(table: FixedTable, step: InsertStutter)
  {
    var InsertStutter(insert_key, _, _, end) := step;
    // we should skip these
    && ShouldSkipSlots(table, step) // TODO: we might not need this?
    // the entry at end index has the same key
    && table[end].value.Full?
    && table[end].value.key == insert_key
  }

  function TableInsertTransition(table: FixedTable, step: InsertStutter) : FixedTable
    requires 
      || TableInsertSwapEnable(table, step)
      || TableInsertDoneEnable(table, step)
      || TableInsertUpdateEnable(table, step)
  {
    var InsertStutter(key, val, _, end) := step;
    table[end := Some(Full(key, val))]
  }

  // predicate TableInsertEnable(table: FixedTable, stutters: seq<InsertStutter>)
  // {
  //   && |stutters| >= 1
  //   // the first one starts at the key hash
  //   && var first := stutters[0];
  //     first.start == hash(first.key)
  //   // the last one should be Done/Update
  //   && (
  //       var last := stutters[ |stutters| - 1 ];
  //       || TableInsertDoneEnable(table, last)
  //       || TableInsertUpdateEnable(table, last)
  //     )
  //   // the intermediate ones are swaps
  //   && (forall i | 1 <= i < |stutters| ::
  //       && stutters[i-1].end == stutters[i].start
  //       && TableInsertSwapEnable(table, stutters[i])
  //     )
  // }

  predicate TableInsertEnableRec(table: FixedTable, stutters: seq<InsertStutter>)
    requires |stutters| >= 1
    decreases |stutters|
  {
    var curr := stutters[0];
    if |stutters| == 1 then
      (
        || TableInsertDoneEnable(table, curr)
        || TableInsertUpdateEnable(table, curr)
      )
    else
      (
        // next starts at current end
        && curr.end == stutters[1].start
        && TableInsertSwapEnable(table, curr)
        && var table' := TableInsertTransition(table, curr);
        // recurse on the rest of the steps
        && TableInsertEnableRec(table', stutters[1..])
      )
  }

  function TableInsert(table: FixedTable, stutters: seq<InsertStutter>): FixedTable
    requires |stutters| >= 1
    requires TableInsertEnableRec(table, stutters)
    decreases |stutters|
  {
    var curr := stutters[0];
    if |stutters| == 1 then
      TableInsertTransition(table, curr)
    else
      var table' := TableInsertTransition(table, curr);
      TableInsert(table', stutters[1..])
  }

  // Insert
  predicate Insert(v: Variables, v': Variables, ticket: Ticket, stutters: seq<InsertStutter>)
  {
    && v.Variables?
    && ticket in v.tickets
    && ticket.input.InsertInput?

    && |stutters| >= 1
    // the first step starts at the insert key hash
    && var first := stutters[0];
    && first.start == hash(first.key)
    && first.key == ticket.input.key

    && TableInsertEnableRec(v.table, stutters)

    && v' == v
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
      .(table := TableInsert(v.table, stutters))
  }

  // predicate Overwrite(v: Variables, v': Variables, ticket: Ticket, i: int)
  // {
  //   && v.Variables?
  //   && v'.Variables?
  //   && ticket in v.tickets
  //   && ticket.input.InsertInput?
  //   && 0 <= i < |v.table|
  //   && v.table[i].Some?
  //   && v.table[i].value.Full?
  //   && v.table[i].value.key == ticket.input.key
  //   && v' == v
  //     .(tickets := v.tickets - multiset{ticket})
  //     .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
  //     .(table := v.table[i := Some(Full(ticket.input.key, ticket.input.value))])
  // }

  // predicate Insert(v: Variables, v': Variables, ticket: Ticket, i: int, end: int)
  // {
  //   && v.Variables?
  //   && v'.Variables?
  //   && ticket in v.tickets
  //   && ticket.input.InsertInput?

  //   && 0 <= i < |v.table|
  //   && 0 <= end < |v.table|
  //   // && v.table[i].Some?
  //   // && v.table[i].value.Full?
  //   // && var insert_h := hash(ticket.input.key) as int;
  //   // && var slot_h  := hash(v.table[i].value.key) as int;

  //   // && ShouldHashGoBefore(insert_h, slot_h , i)
  //   // && LeftShift_PartialState(v.table, v'.table, RobinHood.LeftShift(i, end))
  //   && v' == v.(table := v'.table)
  //       .(tickets := v.tickets - multiset{ticket})
  //       .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput(true))})
  // }

  // predicate RightShift_PartialState(table: Table, table': Table, shift: LeftShift)
  // {
  //   && 0 <= shift.start < |table|
  //   && 0 <= shift.end < |table|
  //   && |table'| == |table|

  //   && (shift.start <= shift.end ==>
  //     && (forall i | 0 <= i < shift.start :: table'[i] == table[i]) // untouched things
  //     && (forall i | shift.start <= i < shift.end :: table'[i] == table[i+1] && table'[i].Some?) // touched things
  //     && table'[shift.end] == Some(Empty) // the end should be empty
  //     && (forall i | shift.end < i < |table'| :: table'[i] == table[i]) // untouched things
  //   )

  //   && (shift.start > shift.end ==>
  //     && (forall i | 0 <= i < shift.end :: table'[i] == table[i+1]) // shift second half 
  //     && table'[shift.end] == Some(Empty) // the end should be empty 
  //     && (forall i | shift.end < i < shift.start :: table'[i] == table[i]) // untouched things
  //     && (forall i | shift.start <= i < |table'| - 1 :: table'[i] == table[i+1] && table'[i].Some?) // shift first half 
  //     && table'[ |table'| - 1 ] == table[0] // shift around the wrap 
  //   )
  // }


  // Remove

  predicate RemoveNotFound(v: Variables, v': Variables, ticket: Ticket, end: Index)
  {
    && v.Variables?
    && v'.Variables?
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && KeyNotFound(v.table, ticket.input.key, end)
    && v' == v
      .(tickets := v.tickets - multiset{ticket})
      .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(false))})
  }

  predicate LeftShift_PartialState(table: Table, table': Table, shift: LeftShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|
    && |table'| == |table|

    && (shift.start <= shift.end ==>
      && (forall i | 0 <= i < shift.start :: table'[i] == table[i]) // untouched things
      && (forall i | shift.start <= i < shift.end :: table'[i] == table[i+1] && table'[i].Some?) // touched things
      && table'[shift.end] == Some(Empty) // the end should be empty
      && (forall i | shift.end < i < |table'| :: table'[i] == table[i]) // untouched things
    )

    && (shift.start > shift.end ==>
      && (forall i | 0 <= i < shift.end :: table'[i] == table[i+1]) // shift second half 
      && table'[shift.end] == Some(Empty) // the end should be empty 
      && (forall i | shift.end < i < shift.start :: table'[i] == table[i]) // untouched things
      && (forall i | shift.start <= i < |table'| - 1 :: table'[i] == table[i+1] && table'[i].Some?) // shift first half 
      && table'[ |table'| - 1 ] == table[0] // shift around the wrap 
    )
  }

  predicate Remove(v: Variables, v': Variables, ticket: Ticket, i: int, end: int)
  {
    && v.Variables?
    && v'.Variables?
    && ticket in v.tickets
    && ticket.input.RemoveInput?
    && 0 <= i < |v.table|
    && v.table[i].Some?
    && v.table[i].value.Full?
    && v.table[i].value.key == ticket.input.key
    && LeftShift_PartialState(v.table, v'.table, LeftShift(i, end))
    && v' == v.(table := v'.table)
        .(tickets := v.tickets - multiset{ticket})
        .(stubs := v.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput(true))})
  }

/*
  // All together
  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      case QueryFoundStep(ticket, i) => QueryFound(v, v', ticket, i)
      case QueryNotFoundStep(ticket, end) => QueryNotFound(v, v', ticket, end)
      case OverwriteStep(ticket, i) => Overwrite(v, v', ticket, i)
      case RemoveStep(ticket, i, end) => Remove(v, v', ticket, i, end)
      case RemoveNotFoundStep(ticket, end) => RemoveNotFound(v, v', ticket, end)
      case InsertStep(ticket, i) => Insert(v, v', ticket, i)
    }
  }

  predicate Next(s: Variables, s': Variables)
  {
    exists step :: NextStep(s, s', step)
  }

//////////////////////////////////////////////////////////////////////////////
// global-level Invariant proof
//////////////////////////////////////////////////////////////////////////////

  predicate Complete(table: Table)
  {
    && (forall i | 0 <= i < |table| :: table[i].Some?)
  }

  // unwrapped_index
  function adjust(i: int, root: int) : int
  requires 0 <= i < FixedSize()
  requires 0 <= root <= FixedSize()
  {
    if i < root then FixedSize() + i else i
  }

  // Keys are unique, although we don't count entries being removed
  predicate KeysUnique(table: Table)
  requires Complete(table)
  {
    forall i, j | 0 <= i < |table| && 0 <= j < |table| && i != j
      && table[i].value.Full? && table[j].value.Full?
        :: table[i].value.key != table[j].value.key
  }

  predicate ValidHashInIndex(table: Table, e: int, i: int)
  requires |table| == FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= i < |table|
  {
    // No matter which empty pivot cell 'e' we choose, every entry is 'downstream'
    // of the place that it hashes to.
    // Likewise for insert pointers and others

    table[e].value.Empty? && table[i].value.Full? ==> (
      var h := hash(table[i].value.key) as int;
      && adjust(h, e+1) <= adjust(i, e+1)
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashOrdering(table: Table, e: int, j: int, k: int)
  requires |table| == FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.Empty? && table[j].value.Full? && adjust(j, e + 1) < adjust(k, e + 1) ==> (
      var hj := hash(table[j].value.key) as int;
      (table[k].value.Full? ==> (
        var hk := hash(table[k].value.key) as int;
        && adjust(hj, e + 1) <= adjust(hk, e + 1)
      ))
    ))
  }

  predicate InvTable(table: Table)
  {
    && |table| == FixedSize()
    && Complete(table)
    //&& ExistsEmptyEntry(table)
    && KeysUnique(table)
    && (forall e, i | 0 <= e < |table| && 0 <= i < |table|
        :: ValidHashInIndex(table, e, i))
    && (forall e, j, k | 0 <= e < |table| && 0 <= j < |table| && 0 <= k < |table|
        :: ValidHashOrdering(table, e, j, k))
  }

  function {:opaque} TableQuantity(s: Table) : nat {
    if s == [] then 0 else TableQuantity(s[..|s|-1]) + (if Last(s).value.Full? then 1 else 0)
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

  //////////////////////////////////////////////////////////////////////////////
  // Proof that Init && []Next maintains Inv
  //////////////////////////////////////////////////////////////////////////////

  lemma NextStep_PreservesInv(s: Variables, s': Variables, step: Step)
  requires Inv(s)
  requires NextStep(s, s', step)
  ensures Inv(s')
  {
    match step {
    }
  }

  lemma Next_PreservesInv(s: Variables, s': Variables)
  requires Inv(s)
  requires Next(s, s')
  ensures Inv(s')
  {
    var step :| NextStep(s, s', step);
    NextStep_PreservesInv(s, s', step);
  }

//////////////////////////////////////////////////////////////////////////////
// fragment-level validity defined wrt Inv
//////////////////////////////////////////////////////////////////////////////
  predicate Valid(s: Variables)
    ensures Valid(s) ==> s.Variables?
  {
    && s.Variables?
    && exists t :: Inv(add(s, t))
  }

  lemma InvImpliesValid(s: Variables)
    requires Inv(s)
    ensures Valid(s)
  {
    // reveal Valid();
    add_unit(s);
  }

  lemma EmptyTableQuantityIsZero(infos: Table)
    requires (forall i | 0 <= i < |infos| :: infos[i] == Some(Empty))
    ensures TableQuantity(infos) == 0
  {
    reveal_TableQuantity();
  }

  lemma InitImpliesValid(s: Variables)
  //requires Init(s)
  //ensures Valid(s)
  {
    EmptyTableQuantityIsZero(s.table);
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
    Next_PreservesInv(add(s, t), add(s', t));
  }

  predicate TransitionEnable(s: Variables, step: Step)
  {
    match step {
    }
  }

  function GetTransition(s: Variables, step: Step): (s': Variables)
    requires TransitionEnable(s, step)
    ensures NextStep(s, s', step);
  {
    match step {
    }
  }

  // Reduce boilerplate by letting caller provide explicit step, which triggers a quantifier for generic Next()
  glinear method easy_transform_step(glinear b: Variables, ghost step: Step)
  returns (glinear c: Variables)
    requires TransitionEnable(b, step)
    ensures c == GetTransition(b, step)
  {
    var e := GetTransition(b, step);
    c := do_transform(b, e);
  }

  lemma NewTicketPreservesValid(r: Variables, id: int, input: Ifc.Input)
    //requires Valid(r)
    ensures Valid(add(r, input_ticket(id, input)))
  {
    // reveal Valid();
    var ticket := input_ticket(id, input);
    var t :| Inv(add(r, t));

    assert add(add(r, ticket), t).table == add(r, t).table;
    assert add(add(r, ticket), t).insert_capacity == add(r, t).insert_capacity;
  }

  // Trusted composition tools. Not sure how to generate them.
  glinear method {:extern} enclose(glinear a: Count.Variables) returns (glinear h: Variables)
    requires Count.Valid(a)
    ensures h == unit().(insert_capacity := a)

  glinear method {:extern} declose(glinear h: Variables) returns (glinear a: Count.Variables)
    requires h.Variables?
    requires h.table == unitTable() // h is a unit() except for a
    requires h.tickets == multiset{}
    requires h.stubs == multiset{}
    ensures a == h.insert_capacity
*/  
}
