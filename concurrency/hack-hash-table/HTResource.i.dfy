include "ApplicationResourceSpec.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "MapSpec.s.dfy"

module HTResource refines ApplicationResourceSpec {
  import opened NativeTypes
  import opened Options

  import opened KeyValueType
  import MapIfc

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  function FixedSize() : (n: nat)
  ensures n > 1

  function Capacity() : (n: nat)
  {
    FixedSize() - 1
  }

  function method FixedSizeImpl() : (n: uint32)
  ensures n as int == FixedSize()

  predicate ValidHashIndex(h:int) {
    0 <= h as int < FixedSize()
  }

  function method hash(key: Key) : (h:uint32)
    ensures ValidHashIndex(h as int)

  datatype KV = KV(key: Key, val: Value)

  // This is the thing that's stored in the hash table at this row.
  datatype Entry =
    | Full(kv: KV)
    | Empty

  // This is what some thread's stack thinks we're doing at this row.
  // TODO rename ActiveOp or Underway or something
  // The information embedded in these state objects form a richer invariant
  // that paves over the temporary gaps in the "idle invariant" that should
  // apply when no threads are operating)
  datatype State =
    | Free
    | Inserting(rid: int, kv: KV, initial_key: Key)
    | Removing(rid: int, key: Key)
    | RemoveTidying(rid: int, initial_key: Key, found_value: Value)

      // Why do we need to store query state to support an invariant over the
      // hash table interpretation, since query is a read-only operation?
      // Because the query's result is defined at the moment it begins (its
      // serialization point), which is to say the proof ghostily knows the
      // answer when the query begins. We need to show inductively that that
      // answer stays the same with each step of any thread, until the impl
      // gets far enough to discover the answer in the real data structure.
      // We're showing that we inductively preserve the value of the
      // interpretation of the *answer* to query #rid.
    | Querying(rid: int, key: Key)

  // TODO rename
  datatype Info = Info(entry: Entry, state: State)

  datatype PreR =
      | R(table: seq<Option<Info>>,
          insert_capacity: nat,
          tickets: multiset<Ticket>,
          stubs: multiset<Stub>)
      | Fail
        // The UpdateStep disjunct is complex, but we'll show that as long
        // as the impl obeys them, it'll never land in Fail.
        // The state is here to "leave slack" in the defenition of add(),
        // so that we can push off the proof that we never end up failing
        // until UpdatePreservesValid. If we didn't do it this way, we'd
        // have to show that add is complete, which would entail sucking
        // the definition of update and proof of UpdatePreservesValid all
        // into the definition of add().
  type R = r: PreR | (r.R? ==> |r.table| == FixedSize()) witness Fail

  function unitTable(): seq<Option<Info>>
  {
    seq(FixedSize(), i => None)
  }

  function unit() : R {
    R(unitTable(), 0, multiset{}, multiset{})
  }

  function oneRowTable(k: nat, info: Info) : seq<Option<Info>>
    requires 0 <= k < FixedSize()
  {
    seq(FixedSize(), i => if i == k then Some(info) else None)
  }

  function oneRowResource(k: nat, info: Info, cap: nat) : R 
    requires 0 <= k < FixedSize()
  {
    R(oneRowTable(k, info), cap, multiset{}, multiset{})
  }

  // predicate resourceHasSingleRow(r: R, k: nat, info: Info)
  //   requires 0 <= k < FixedSize()
  // {
  //   && r.R?
  //   && (forall i:nat | i < FixedSize() :: if i == k then r.table[i].Some? else r.table[i].None?)
  //   && r.table[k].value == info
  //   && r.tickets == multiset{}
  //   && r.stubs == multiset{}
  // }

  function twoRowsTable(k1: nat, info1: Info, k2: nat, info2: Info) : seq<Option<Info>>
    requires 0 <= k1 < FixedSize()
    requires 0 <= k2 < FixedSize()
    requires k1 != k2
  {
    seq(FixedSize(), i => if i == k1 then Some(info1) else if i == k2 then Some(info2) else None)
  }

  function twoRowsResource(k1: nat, info1: Info, k2: nat, info2: Info, cap: nat) : R 
    requires 0 <= k1 < FixedSize()
    requires 0 <= k2 < FixedSize()
    requires k1 != k2
  {
    R(twoRowsTable(k1, info1, k2, info2), cap, multiset{}, multiset{})
  }

  predicate isInputResource(in_r: R, rid: int, input: Ifc.Input)
  {
    && in_r.R?
    && in_r.table == unitTable()
    && in_r.insert_capacity == 0
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

  function add(x: R, y: R) : R {
    if x.R? && y.R? && nonoverlapping(x.table, y.table) then (
      R(fuse_seq(x.table, y.table),
          x.insert_capacity + y.insert_capacity,
          x.tickets + y.tickets,
          x.stubs + y.stubs)
    ) else (
      Fail
    )
  }

  lemma add_unit(x: R)
  ensures add(x, unit()) == x
  {
  }

  lemma commutative(x: R, y: R)
  ensures add(x, y) == add(y, x)
  {
    if x.R? && y.R? && nonoverlapping(x.table, y.table) {
      /*assert nonoverlapping(y.table, x.table);
      forall i | 0 <= i < FixedSize()
      ensures add(x,y).table[i] == add(y,x).table[i]
      {
        assert fuse(x.table[i], y.table[i]) == fuse(y.table[i], x.table[i]);
      }*/
      assert fuse_seq(x.table, y.table) == fuse_seq(y.table, x.table);
      assert add(x, y).tickets == add(y, x).tickets;
      assert add(x, y).stubs == add(y, x).stubs;
    }
  }

  lemma associative(x: R, y: R, z: R)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
    if x.R? && y.R? && z.R? && nonoverlapping(x.table, y.table)
        && nonoverlapping(fuse_seq(x.table, y.table), z.table)
    {
      /*forall i | 0 <= i < FixedSize()
      ensures add(x, add(y, z)).table[i] == add(add(x, y), z).table[i]
      {
      }
      //assert fuse_seq(fuse_seq(x.table, y.table), z.table)
      //    == fuse_seq(x.table, fuse_seq(y.table, z.table));
      assert add(x, add(y, z)).table == add(add(x, y), z).table;*/
      assert add(x, add(y, z)) == add(add(x, y), z);
    } else {
    }
  }

  predicate Init(s: R) {
    && s.R?
    && (forall i | 0 <= i < |s.table| :: s.table[i] == Some(Info(Empty, Free)))
    && s.insert_capacity == Capacity()
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  datatype Step =
    | ProcessInsertTicketStep(insert_ticket: Ticket)
    | InsertSkipStep(pos: nat)
    | InsertSwapStep(pos: nat)
    | InsertDoneStep(pos: nat)
    | InsertUpdateStep(pos: nat)

    | ProcessRemoveTicketStep(insert_ticket: Ticket)
    | RemoveSkipStep(pos: nat)
    | RemoveFoundItStep(pos: nat)
    | RemoveNotFoundStep(pos: nat)
    | RemoveTidyStep(pos: nat)
    | RemoveDoneStep(pos: nat)

    | ProcessQueryTicketStep(query_ticket: Ticket)
    | QuerySkipStep(pos: nat)
    | QueryDoneStep(pos: nat)
    | QueryNotFoundStep(pos: nat)

  predicate ProcessInsertTicket(s: R, s': R, insert_ticket: Ticket)
  {
    && !s.Fail?
    && insert_ticket.input.InsertInput?
    && insert_ticket in s.tickets
    && var key := insert_ticket.input.key;
    && var h: uint32 := hash(key);
    && 0 <= h as int < |s.table|
    && s.table[h].Some?
    && s.table[h].value.state.Free?
    && s.insert_capacity >= 1
    && (s' == s
      .(tickets := s.tickets - multiset{insert_ticket})
      .(insert_capacity := s.insert_capacity - 1)
      .(table := s.table[h := Some(
          s.table[h].value.(
              state := Inserting(insert_ticket.rid,
              KV(key, insert_ticket.input.value),key)))]))
  }

  lemma ProcessInsertTicketPreservesValid(s: R, t: R, insert_ticket: Ticket)
    requires ProcessInsertTicket(s, t, insert_ticket)
    requires Valid(s)
    ensures Valid(t)
  {
    reveal_TableQuantity();
    var h := hash(insert_ticket.input.key) as nat;
    var spre := s.table[..h];
    var sat := s.table[h..h+1];
    var spost := s.table[h+1..];
    assert spre + (sat + spost) == s.table;
    var tat := t.table[h..h+1];
    assert spre + (tat + spost) == t.table;
    var oldAtCount := if sat[0].value.entry.Full? then 1 else 0;
    assert TableQuantity(sat) == oldAtCount;
    assert TableQuantity(tat) == oldAtCount+1;
    calc {
      TableQuantity(s.table) + 1;
        { TableQuantityDistributive(spre, sat+spost); }
      TableQuantity(spre) + TableQuantity(sat+spost) + 1;
        { TableQuantityDistributive(sat, spost); }
      TableQuantity(spre) + TableQuantity(sat) + TableQuantity(spost) + 1;
      TableQuantity(spre) + oldAtCount + TableQuantity(spost) + 1;
      TableQuantity(spre) + TableQuantity(tat) + TableQuantity(spost);
        { TableQuantityDistributive(tat, spost); }
      TableQuantity(spre) + TableQuantity(tat+spost);
        { TableQuantityDistributive(spre, tat+spost); }
      TableQuantity(t.table);
    }

    var s' :| TableQuantityInv(add(s, s'));

    calc {
      TableQuantity(add(s, s').table) + add(s, s').insert_capacity;
        { ResourceTableQuantityDistributive(s, s'); }
      TableQuantity(s.table) + TableQuantity(s'.table) + s.insert_capacity + s'.insert_capacity;
      TableQuantity(t.table) + TableQuantity(s'.table) + t.insert_capacity + s'.insert_capacity;
        { ResourceTableQuantityDistributive(t, s'); }
      TableQuantity(add(t, s').table) + add(t, s').insert_capacity;
    }

    assert TableQuantityInv(add(t, s'));
  }

  predicate ProcessInsertTicketFail(s: R, s': R, insert_ticket: Ticket)
  {
    && !s.Fail?
    && insert_ticket.input.InsertInput?
    && insert_ticket in s.tickets
    // && s.insert_capacity == 1
    && (s' == s
      .(tickets := s.tickets - multiset{insert_ticket})
      .(stubs := s.stubs + multiset{Stub(insert_ticket.rid, MapIfc.InsertOutput(false))}))
  }

  // search_h: hash of the key we are trying to insert
  // slot_h: hash of the key at slot_idx
  // returns search_h should go before slot_h
  predicate ShouldHashGoBefore(search_h: int, slot_h: int, slot_idx: int)
  {
    || search_h < slot_h <= slot_idx // normal case
    || slot_h <= slot_idx < search_h // search_h wraps around the end of array
    || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) >= hash(pos j)
  // we skip item i and move to i+1.
  predicate InsertSkip(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && s'.R?
    && 0 <= pos < FixedSize()
    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && s.table[pos].Some?
    && s.table[pos'].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    // This isn't a matching key...
    && s.table[pos].value.state.kv.key
        != s.table[pos].value.entry.kv.key
    // ...and we need to keep searching because of the Robin Hood rule.
    && !ShouldHashGoBefore(
        hash(s.table[pos].value.state.kv.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[pos'].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos' := Some(s.table[pos'].value.(state := s.table[pos].value.state))])
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) < hash(pos j)
  // in this case we do the swap and keep moving forward
  // with the swapped-out item.
  predicate InsertSwap(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && s.table[pos].Some?
    && s.table[pos'].Some?
    && var state := s.table[pos].value.state;
    && state.Inserting?
    && s.table[pos].value.entry.Full?
    && ShouldHashGoBefore(
        hash(state.kv.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[pos'].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(Info(
          Full(state.kv),
          Free))]
        [pos' := Some(s.table[pos'].value.(state :=
          Inserting(
            state.rid,
            s.table[pos].value.entry.kv, state.initial_key)))])
  }

  // Slot is empty. Insert our element and finish.
  predicate InsertDone(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Empty?
    && s' == s
      .(table := s.table
        [pos := Some(Info(
            Full(s.table[pos].value.state.kv),
            Free))])
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))})
  }

  predicate InsertUpdate(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.entry.kv.key == s.table[pos].value.state.kv.key
    && s' == s
      .(table := s.table
        [pos := Some(Info(
            Full(s.table[pos].value.state.kv),
            Free))])
      .(insert_capacity := s.insert_capacity + 1) // we reserved the capacity at the begining, but later discover we don't need it
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))})
  }

  // Remove

  // We know about row h (our thread is working on it),
  // and we know that it's free (we're not already claiming to do something else with it).
  predicate KnowRowIsFree(s: R, h: int)
    requires !s.Fail?
    requires ValidHashIndex(h)
  {
    && s.table[h].Some?
    && s.table[h].value.state.Free?
  }

  predicate ProcessRemoveTicket(s: R, s': R, remove_ticket: Ticket)
  {
    && !s.Fail?
    && remove_ticket.input.RemoveInput?
    && remove_ticket in s.tickets
    && var h: uint32 := hash(remove_ticket.input.key);
    && KnowRowIsFree(s, h as int)
    && s' == s
      .(tickets := s.tickets - multiset{remove_ticket})
      .(table := s.table[h := Some(
          s.table[h].value.(state :=
            Removing(remove_ticket.rid,
              remove_ticket.input.key)))])
  }

  predicate RemoveInspectEnabled(s: R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    // Know row pos, and it's the thing we're removing, and it's full...
    && s.table[pos].Some?
    && s.table[pos].value.state.Removing?
  }

  predicate RemoveSkipEnabled(s: R, pos: nat)
  {
    && RemoveInspectEnabled(s, pos)
    && s.table[pos].value.entry.Full?
    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && KnowRowIsFree(s, pos')
    // ...and the key it's full of sorts before the thing we're looking to remove.
    && !ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
  }

  predicate RemoveSkip(s: R, s': R, pos: nat)
  {
    && RemoveSkipEnabled(s, pos)
    // The hash is equal, but this isn't the key we're trying to remove.
    && s.table[pos].value.entry.kv.key != s.table[pos].value.state.key
    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);

    // Advance the pointer to the next row.
    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos' := Some(s.table[pos'].value.(state := s.table[pos].value.state))])
  }

  predicate RemoveNotFound(s: R, s': R, pos: nat)
  {
    && RemoveInspectEnabled(s, pos)
    && (if s.table[pos].value.entry.Full? then // the key we are looking for goes before the one in the slot, so it must be absent
      && ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
      && s.table[pos].value.entry.kv.key != s.table[pos].value.state.key
      else true // the key would have been in this empty spot
    )
    && s' == s
      .(table := s.table[pos := Some(Info(s.table[pos].value.entry, Free))])
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))})
  }

  predicate RemoveFoundIt(s: R, s': R, pos: nat)
  {
    && RemoveSkipEnabled(s, pos)
    // This IS the key we want to remove!
    && var initial_key := s.table[pos].value.state.key;
    && s.table[pos].value.entry.kv.key == initial_key

    // Change the program counter into RemoveTidying mode
    && var rid := s.table[pos].value.state.rid;
    // Note: it doesn't matter what we set the entry to here, since we're going
    // to overwrite it in the next step either way.
    // (Might be easier to leave the entry as it is rather than set it to Empty?)
    && s' == s.(table := s.table[pos := Some(Info(Empty,
        RemoveTidying(rid, initial_key, s.table[pos].value.entry.kv.val)))])
  }

  predicate TidyEnabled(s: R, pos: nat)
  {
    && !s.Fail?
    && ValidHashIndex(pos)
    // The row that needs backfilling is known and we're pointing at it
    && s.table[pos].Some?
    && s.table[pos].value.state.RemoveTidying?
    && s.table[pos].value.entry.Empty?  // Should be an invariant, actually
    && (pos < FixedSize() - 1 ==> s.table[pos+1].Some?) // if a next row, we know it
  }

  predicate DoneTidying(s: R, pos: nat)
    requires TidyEnabled(s, pos)
  {
    var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && KnowRowIsFree(s, pos')
    && (
      || s.table[pos'].value.entry.Empty?                     // Next row is empty
      || pos' == hash(s.table[pos'].value.entry.kv.key) as nat  // Next row's key can't move back
    )
  }

  predicate RemoveTidy(s: R, s': R, pos: nat)
  {
    && TidyEnabled(s, pos)
    && !DoneTidying(s, pos)

    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && KnowRowIsFree(s, pos')

    // Pull the entry back one slot, and push the state pointer forward one slot.
    && s' == s.(table := s.table
      [pos := Some(Info(s.table[pos'].value.entry, Free))]
      [pos' := Some(Info(Empty, s.table[pos].value.state))]
      )
  }

  predicate RemoveDone(s: R, s': R, pos: nat)
  {
    && TidyEnabled(s, pos)
    && DoneTidying(s, pos)
    && !s'.Fail?
    // Clear the pointer, return the stub.
    && s' == s
      .(table := s.table[pos := Some(Info(s.table[pos].value.entry, Free))])
      .(insert_capacity := s.insert_capacity + 1)
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(true))})
  }

  // Query

  predicate ProcessQueryTicket(s: R, s': R, query_ticket: Ticket)
  {
    && !s.Fail?
    && query_ticket.input.QueryInput?
    && query_ticket in s.tickets
    && var h: uint32 := hash(query_ticket.input.key);
    && 0 <= h as int < FixedSize()
    && s.table[h].Some?
    && s.table[h].value.state.Free?
    && s' == s
      .(tickets := s.tickets - multiset{query_ticket})
      .(table := s.table[h := Some(
          s.table[h].value.(state :=
            Querying(query_ticket.rid, query_ticket.input.key)))])
  }

  function NextPos(pos: nat) : nat {
    if pos < FixedSize() - 1 then pos + 1 else 0
  }

  predicate QuerySkipEnabled(s: R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[NextPos(pos)].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    // Not the key we're looking for
    && s.table[pos].value.state.key != s.table[pos].value.entry.kv.key
    // But we haven't passed by the key we want yet (Robin Hood rule)
    && !ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[NextPos(pos)].value.state.Free?
  }

  predicate QuerySkip(s: R, s': R, pos: nat)
  {
    && QuerySkipEnabled(s, pos)

    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [NextPos(pos) := Some(s.table[NextPos(pos)].value.(state := s.table[pos].value.state))])
  }

  predicate QueryDone(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key == s.table[pos].value.entry.kv.key
    && var stub := Stub(s.table[pos].value.state.rid, MapIfc.QueryOutput(Found(s.table[pos].value.entry.kv.val)));
    && s' == s
      .(table := s.table[pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{stub})
  }

  predicate QueryNotFound(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Querying?
    // We're allowed to do this step if it's empty, or if the hash value we
    // find is bigger than the one we're looking for
    && (s.table[pos].value.entry.Full? ==>
      ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos))
      // TODO: we have replaced the following predicate, so wrap around is considered
      // hash(s.table[pos].value.state.key) < hash(s.table[pos].value.entry.kv.key))
    && s' == s
      .(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{
        Stub(s.table[pos].value.state.rid, MapIfc.QueryOutput(NotFound))
       })
  }

  predicate QueryFullHashTable(s: R, s': R, pos: nat)
  {
    && QuerySkipEnabled(s, pos)

    // And we've gone in an entire circle; another step would put us
    // back where we entered the hash table.
    && NextPos(pos) == hash(s.table[pos].value.state.key) as int

    && s' == s
      .(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{
        Stub(s.table[pos].value.state.rid, MapIfc.QueryOutput(NotFound))
       })
  }

  predicate UpdateStep(s: R, s': R, step: Step)
  {
    match step {
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicket(s, s', insert_ticket)
      case InsertSkipStep(pos) => InsertSkip(s, s', pos)
      case InsertSwapStep(pos) => InsertSwap(s, s', pos)
      case InsertDoneStep(pos) => InsertDone(s, s', pos)
      case InsertUpdateStep(pos) => InsertUpdate(s, s', pos)

      case ProcessRemoveTicketStep(remove_ticket) => ProcessRemoveTicket(s, s', remove_ticket)
      case RemoveSkipStep(pos) => RemoveSkip(s, s', pos)
      case RemoveFoundItStep(pos) => RemoveFoundIt(s, s', pos)
      case RemoveNotFoundStep(pos) => RemoveNotFound(s, s', pos)
      case RemoveTidyStep(pos) => RemoveTidy(s, s', pos)
      case RemoveDoneStep(pos) => RemoveDone(s, s', pos)

      case ProcessQueryTicketStep(query_ticket) => ProcessQueryTicket(s, s', query_ticket)
      case QuerySkipStep(pos) => QuerySkip(s, s', pos)
      case QueryDoneStep(pos) => QueryDone(s, s', pos)
      case QueryNotFoundStep(pos) => QueryNotFound(s, s', pos)
    }
  }

  predicate Update(s: R, s': R) {
    exists step :: UpdateStep(s, s', step)
  }

  function InfoQuantity(s: Option<Info>) : nat {
    if s.None? then 0 else (
      (if s.value.state.Inserting? then 1 else 0) +
      (if s.value.state.RemoveTidying? || s.value.entry.Full? then 1 else 0)
    )
  }

  function {:opaque} TableQuantity(s: seq<Option<Info>>) : nat {
    if s == [] then 0 else TableQuantity(s[..|s|-1]) + InfoQuantity(s[|s| - 1])
  }

  predicate TableQuantityInv(s: R)
  {
    && s.R?
    && TableQuantity(s.table) + s.insert_capacity == Capacity()
  }

  predicate Valid(s: R) {
    && s.R?
    && exists s' :: TableQuantityInv(add(s, s'))
  }

  lemma valid_monotonic(x: R, y: R)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
    var xy' :| TableQuantityInv(add(add(x, y), xy'));
    associative(x, y, xy');
    assert TableQuantityInv(add(x, add(y, xy')));
  }

  lemma update_monotonic(x: R, y: R, z: R)
  //requires Update(x, y)
  //requires Valid(add(x, z))
  ensures Update(add(x, z), add(y, z))
  {
    var step :| UpdateStep(x, y, step);
    assert UpdateStep(add(x, z), add(y, z), step);
  }

  function input_ticket(id: int, input: Ifc.Input) : R
  {
    unit().(tickets := multiset{Ticket(id, input)})
  }

  function output_stub(id: int, output: Ifc.Output) : R
  {
    unit().(stubs := multiset{Stub(id, output)})
  }

  lemma NewTicketPreservesValid(r: R, id: int, input: Ifc.Input)
  //requires Valid(r)
  ensures Valid(add(r, input_ticket(id, input)))
  {
    var r' :| TableQuantityInv(add(r, r'));
    var out_r := add(r, input_ticket(id, input));
    assert out_r.table == r.table by { reveal_TableQuantity(); }
    assert add(out_r, r').table == add(r, r').table by { reveal_TableQuantity(); }
  }

  lemma EmptyTableQuantityIsZero(infos: seq<Option<Info>>)
    requires (forall i | 0 <= i < |infos| :: infos[i] == Some(Info(Empty, Free)))
    ensures TableQuantity(infos) == 0
  {
    reveal_TableQuantity();
  }

  lemma InitImpliesValid(s: R)
  //requires Init(s)
  //ensures Valid(s)
  {
    reveal_TableQuantity();
    EmptyTableQuantityIsZero(s.table);
    add_unit(s);
    assert TableQuantityInv(add(s, unit()));
  }

  lemma TableQuantityDistributive(a: seq<Option<Info>>, b: seq<Option<Info>>)
    ensures TableQuantity(a + b) == TableQuantity(a) + TableQuantity(b)
  {
    reveal_TableQuantity();
  }

  lemma ResourceTableQuantityDistributive(x: R, y: R)
    requires add(x, y).R?
    ensures TableQuantity(add(x, y).table) == TableQuantity(x.table) + TableQuantity(y.table)
  {
    reveal_TableQuantity();
    var t := fuse_seq(x.table, y.table);
    var i := 0;
    while i < |x.table|
      invariant i <= |x.table|
      invariant TableQuantity(t[..i]) == TableQuantity(x.table[..i]) + TableQuantity(y.table[..i])
    {
      calc {
        TableQuantity(t[..i+1]);
        {
          assert t[..i] + t[i..i+1] == t[..i+1];
          TableQuantityDistributive(t[..i], t[i..i+1]); 
        }
        TableQuantity(t[..i]) + TableQuantity(t[i..i+1]);
        TableQuantity(x.table[..i]) + TableQuantity(y.table[..i]) + TableQuantity(t[i..i+1]);
        {
          assert TableQuantity(t[i..i+1]) == TableQuantity(x.table[i..i+1]) + TableQuantity(y.table[i..i+1]);
        }
        TableQuantity(x.table[..i]) + TableQuantity(y.table[..i]) + TableQuantity(x.table[i..i+1]) + TableQuantity(y.table[i..i+1]);
        {
          assert x.table[..i] + x.table[i..i+1] == x.table[..i+1];
          TableQuantityDistributive(x.table[..i], x.table[i..i+1]); 
        }
        TableQuantity(x.table[..i+1]) + TableQuantity(y.table[..i]) + TableQuantity(y.table[i..i+1]);
        {
          assert y.table[..i] + y.table[i..i+1] == y.table[..i+1];
          TableQuantityDistributive(y.table[..i], y.table[i..i+1]); 
        }
        TableQuantity(x.table[..i+1]) + TableQuantity(y.table[..i+1]);
      }
      i := i + 1;
    }
    assert t[..i] == add(x, y).table;
    assert x.table[..i] == x.table;
    assert y.table[..i] == y.table;
  }

  lemma UpdatePreservesValid(s: R, t: R)
  //requires Update(s, t)
  //requires Valid(s)
  ensures Valid(t)
  {
    var step :| UpdateStep(s, t, step);
    match step {
      case ProcessInsertTicketStep(insert_ticket) => {
        ProcessInsertTicketPreservesValid(s, t, insert_ticket);
      }
      case _ => {
        assume false;
      }
      // case InsertSkipStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case InsertSwapStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case InsertDoneStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case InsertUpdateStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case ProcessRemoveTicketStep(remove_ticket) => {
      //   assert s.table == t.table;
      // }
      // case RemoveSkipStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case RemoveFoundItStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case RemoveNotFoundStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case RemoveTidyStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case RemoveDoneStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case ProcessQueryTicketStep(query_ticket) => {
      //   assert s.table == t.table;
      // }
      // case QuerySkipStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case QueryDoneStep(pos) => {
      //   assert s.table == t.table;
      // }
      // case QueryNotFoundStep(pos) => {
      //   assert s.table == t.table;
      // }
    }
    // var s' :| TableQuantityInv(add(s, s'));
    // assert TableQuantityInv(add(t, s')) by { reveal_TableQuantity(); }
  }

  glinear method easy_transform(
      glinear b: R,
      ghost expected_out: R)
  returns (glinear c: R)
  requires Update(b, expected_out)
  ensures c == expected_out
  // travis promises to supply this

  // Reduce boilerplate by letting caller provide explicit step, which triggers a quantifier for generic Update()
  glinear method easy_transform_step(
      glinear b: R,
      ghost expected_out: R,
      ghost step: Step)
  returns (glinear c: R)
  requires UpdateStep(b, expected_out, step) 
  ensures c == expected_out
  {
    c := easy_transform(b, expected_out);
  }
}
