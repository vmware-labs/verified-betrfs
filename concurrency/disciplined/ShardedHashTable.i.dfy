include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "ConcurrencyModel.s.dfy"
include "AppSpec.s.dfy"

module Limits {
  import opened NativeTypes

  function FixedSize() : (n: nat)
    ensures n > 1

  function Capacity() : (n: nat)
  {
    FixedSize() - 1
  }

  function method FixedSizeImpl() : (n: uint32)
    ensures n as int == FixedSize()

  function method CapacityImpl(): (s: uint32)
    ensures s as nat == Capacity()
}

// Build up the insert_capacity monoid first so we can talk about it separately
// in the CapacityAllocator impl, and not have to cart around an entire ShardedHashTable.
module Count refines PartialCommutativeMonoid {
  import opened Limits

  datatype Variables = Variables(value: nat)

  function unit() : Variables { Variables(0) }

  function add(x: Variables, y: Variables) : Variables {
    Variables(x.value + y.value)
  }

  lemma add_unit(x: Variables)
  ensures add(x, unit()) == x
  {
  }

  lemma commutative(x: Variables, y: Variables)
  ensures add(x, y) == add(y, x)
  {
  }

  lemma associative(x: Variables, y: Variables, z: Variables)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
  }

  predicate Inv(s: Variables)
  {
    s.value <= Capacity()
  }

  predicate Valid(s: Variables)
  {
    exists t :: Inv(add(s, t))
  }

  function {:opaque} GetRemainder(s: Variables): (t: Variables)
    requires Valid(s)
    ensures Inv(add(s, t))
  {
    // reveal Valid();
    var t :| Inv(add(s, t));
    t
  }

  lemma valid_monotonic(x: Variables, y: Variables)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
  }
}

// TODO(jonh): refactor ShardedHashTable into this module chain:

module ShardedSMTransitions  {
  // Extracted from 
}

module ShardedSMInvProof {
  // what was ResourceStateMachine
}

module UnifiedSM {
  // Reason about all the shards at once
}

module MonoidalSM {
  // Show the validity requirement from ApplicationResourcesSpec
}

module ShardedHashTable refines ShardedStateMachine {
  import opened NativeTypes
  import opened Options
  import opened Limits
  import MapIfc
  import Count

//////////////////////////////////////////////////////////////////////////////
// Data structure definitions & transitions
//////////////////////////////////////////////////////////////////////////////

  import opened KeyValueType

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  predicate ValidHashIndex(h:int)
  {
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
      | Variables(table: seq<Option<Info>>,
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
  type Variables = r: PreR | (r.Variables? ==> |r.table| == FixedSize()) witness Fail

  function unitTable(): seq<Option<Info>>
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

  function oneRowTable(k: nat, info: Info) : seq<Option<Info>>
  requires 0 <= k < FixedSize()
  {
    seq(FixedSize(), i => if i == k then Some(info) else None)
  }

  function oneRowResource(k: nat, info: Info, cap: nat) : Variables 
  requires 0 <= k < FixedSize()
  {
    Variables(oneRowTable(k, info), Count.Variables(cap), multiset{}, multiset{})
  }

  function twoRowsTable(k1: nat, info1: Info, k2: nat, info2: Info) : seq<Option<Info>>
  requires 0 <= k1 < FixedSize()
  requires 0 <= k2 < FixedSize()
  requires k1 != k2
  {
    seq(FixedSize(), i => if i == k1 then Some(info1) else if i == k2 then Some(info2) else None)
  }

  function twoRowsResource(k1: nat, info1: Info, k2: nat, info2: Info, cap: nat) : Variables 
  requires 0 <= k1 < FixedSize()
  requires 0 <= k2 < FixedSize()
  requires k1 != k2
  {
    Variables(twoRowsTable(k1, info1, k2, info2), Count.Variables(cap), multiset{}, multiset{})
  }

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

  lemma associative(x: Variables, y: Variables, z: Variables)
  ensures add(x, add(y, z)) == add(add(x, y), z)
  {
    if x.Variables? && y.Variables? && z.Variables? && nonoverlapping(x.table, y.table)
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

  predicate Init(s: Variables)
  {
    && s.Variables?
    && (forall i | 0 <= i < |s.table| :: s.table[i] == Some(Info(Empty, Free)))
    && s.insert_capacity.value == Capacity()
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

  function NextPos(pos: nat) : nat
  {
    if pos < FixedSize() - 1 then pos + 1 else 0
  }

  predicate ProcessInsertTicketEnable(s: Variables, insert_ticket: Ticket)
  {
    && !s.Fail?
    && insert_ticket.input.InsertInput?
    && insert_ticket in s.tickets
    && var key := insert_ticket.input.key;
    && var h: uint32 := hash(key);
    && 0 <= h as int < |s.table|
    && s.table[h].Some?
    && s.table[h].value.state.Free?
    && s.insert_capacity.value >= 1
  }

  function ProcessInsertTicketTransition(s: Variables, insert_ticket: Ticket): (s': Variables)
    requires ProcessInsertTicketEnable(s, insert_ticket)
  {
    var key := insert_ticket.input.key;
    var h: uint32 := hash(key);
    s.(tickets := s.tickets - multiset{insert_ticket})
      .(insert_capacity := Count.Variables(s.insert_capacity.value - 1))
      .(table := s.table[h := Some(
          s.table[h].value.(
              state := Inserting(insert_ticket.rid,
              KV(key, insert_ticket.input.value), key)))])
  }

  predicate ProcessInsertTicket(s: Variables, s': Variables, insert_ticket: Ticket)
  {
    && ProcessInsertTicketEnable(s, insert_ticket)
    && s' == ProcessInsertTicketTransition(s, insert_ticket)
  }

  predicate ProcessInsertTicketFail(s: Variables, s': Variables, insert_ticket: Ticket)
  {
    && !s.Fail?
    && insert_ticket.input.InsertInput?
    && insert_ticket in s.tickets
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

  predicate InsertSkipEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && var pos' := NextPos(pos);
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
}

  function InsertSkipTransition(s: Variables, pos: nat): Variables
    requires InsertSkipEnable(s, pos)
  {
    var pos' := NextPos(pos);
    s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos' := Some(s.table[pos'].value.(state := s.table[pos].value.state))])
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) >= hash(pos j)
  // we skip item i and move to i+1.
  predicate InsertSkip(s: Variables, s': Variables, pos: nat)
  {
    && InsertSkipEnable(s, pos)
    && s' == InsertSkipTransition(s, pos)
  }

  predicate InsertSwapEanble(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && var pos' := NextPos(pos);
    && s.table[pos].Some?
    && s.table[pos'].Some?
    && var state := s.table[pos].value.state;
    && state.Inserting?
    && s.table[pos].value.entry.Full?
    && ShouldHashGoBefore(
        hash(state.kv.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[pos'].value.state.Free?
  }

  function InsertSwapTransition(s: Variables, pos: nat): Variables
    requires InsertSwapEanble(s, pos)
  {
    var pos' := NextPos(pos);
    var state := s.table[pos].value.state;
    s.(table := s.table
        [pos := Some(Info(Full(state.kv), Free))]
        [pos' := Some(s.table[pos'].value.(state :=
          Inserting(state.rid, s.table[pos].value.entry.kv, state.initial_key)))])
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) < hash(pos j)
  // in this case we do the swap and keep moving forward
  // with the swapped-out item.
  predicate InsertSwap(s: Variables, s': Variables, pos: nat)
  {
    && InsertSwapEanble(s, pos)
    && s' == InsertSwapTransition(s, pos)
  }

  predicate InsertDoneEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Empty?
  }

  function InsertDoneTransition(s: Variables, pos: nat): Variables
    requires InsertDoneEnable(s, pos)
  {
    s.(table := s.table
        [pos := Some(Info(Full(s.table[pos].value.state.kv), Free))])
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))})
  }

  // Slot is empty. Insert our element and finish.
  predicate InsertDone(s: Variables, s': Variables, pos: nat)
  {
    && InsertDoneEnable(s, pos)
    && s' == InsertDoneTransition(s, pos)
  }

  predicate InsertUpdateEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.entry.kv.key == s.table[pos].value.state.kv.key
  }

  function InsertUpdateTransition(s: Variables, pos: nat): Variables
    requires InsertUpdateEnable(s, pos)
  {
    s.(table := s.table
        [pos := Some(Info(Full(s.table[pos].value.state.kv), Free))])
      // we reserved the capacity at the begining, but later discover we don't need it
      .(insert_capacity := Count.Variables(s.insert_capacity.value + 1)) 
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput(true))})
  }

  predicate InsertUpdate(s: Variables, s': Variables, pos: nat)
  {
    && InsertUpdateEnable(s, pos)
    && s' == InsertUpdateTransition(s, pos)
  }

  // Remove

  // We know about row h (our thread is working on it),
  // and we know that it's free (we're not already claiming to do something else with it).
  predicate KnowRowIsFree(s: Variables, h: int)
    requires !s.Fail?
    requires ValidHashIndex(h)  
  {
    && s.table[h].Some?
    && s.table[h].value.state.Free?
  }

  predicate ProcessRemoveTicketEnable(s: Variables, remove_ticket: Ticket)
  {
    && !s.Fail?
    && remove_ticket.input.RemoveInput?
    && remove_ticket in s.tickets
    && var h: uint32 := hash(remove_ticket.input.key);
    && KnowRowIsFree(s, h as int)
  }

  function ProcessRemoveTicketTransition(s: Variables, remove_ticket: Ticket): Variables
    requires ProcessRemoveTicketEnable(s, remove_ticket)
  {
    var h: uint32 := hash(remove_ticket.input.key);
    s.(tickets := s.tickets - multiset{remove_ticket})
      .(table := s.table[h :=
        Some(s.table[h].value.(state := Removing(remove_ticket.rid, remove_ticket.input.key)))])
  }

  predicate ProcessRemoveTicket(s: Variables, s': Variables, remove_ticket: Ticket)
  {
    && ProcessRemoveTicketEnable(s, remove_ticket)
    && s' == ProcessRemoveTicketTransition(s, remove_ticket)
  }

  predicate RemoveInspectEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    // Know row pos, and it's the thing we're removing, and it's full...
    && s.table[pos].Some?
    && s.table[pos].value.state.Removing?
  }

  predicate RemoveSkipEnableCore(s: Variables, pos: nat)
  {
    && RemoveInspectEnable(s, pos)
    && s.table[pos].value.entry.Full?
    && var pos' := NextPos(pos);
    && KnowRowIsFree(s, pos')
    // ...and the key it's full of sorts before the thing we're looking to remove.
    && !ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
  }

  predicate RemoveSkipEnable(s: Variables, pos: nat)
  {
    && RemoveSkipEnableCore(s, pos)
    // The hash is equal, but this isn't the key we're trying to remove.
    // Advance the pointer to the next row.
    && s.table[pos].value.entry.kv.key != s.table[pos].value.state.key
  }

  function RemoveSkipTransition(s: Variables, pos: nat): Variables
    requires RemoveSkipEnable(s, pos)
  {
    var pos' := NextPos(pos);
    s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos' := Some(s.table[pos'].value.(state := s.table[pos].value.state))])
  }

  predicate RemoveSkip(s: Variables, s': Variables, pos: nat)
  {
    && RemoveSkipEnable(s, pos)
    && s' == RemoveSkipTransition(s, pos)
  }

  predicate RemoveNotFoundEnable(s: Variables, pos: nat)
  {
    && RemoveInspectEnable(s, pos)
    && (if s.table[pos].value.entry.Full? then // the key we are looking for goes before the one in the slot, so it must be absent
      && ShouldHashGoBefore(
        hash(s.table[pos].value.state.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
      && s.table[pos].value.entry.kv.key != s.table[pos].value.state.key
      else true // the key would have been in this empty spot
    )
  }

  function RemoveNotFoundTransition(s: Variables, pos: nat): Variables
    requires RemoveNotFoundEnable(s, pos)
  {
    s.(table := s.table[pos := Some(Info(s.table[pos].value.entry, Free))])
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(false))})
  }

  predicate RemoveNotFound(s: Variables, s': Variables, pos: nat)
  {
    && RemoveNotFoundEnable(s, pos)
    && s' == RemoveNotFoundTransition(s, pos)
  }

  predicate RemoveFoundItEnable(s: Variables, pos: nat)
  {
    && RemoveSkipEnableCore(s, pos)
    // This IS the key we want to remove!
    && var initial_key := s.table[pos].value.state.key;
    && s.table[pos].value.entry.kv.key == initial_key
  }

  function RemoveFoundItTransition(s: Variables, pos: nat): Variables
    requires RemoveFoundItEnable(s, pos)
  {
    var initial_key := s.table[pos].value.state.key;
    // Change the program counter into RemoveTidying mode
    var rid := s.table[pos].value.state.rid;
    // Note: it doesn't matter what we set the entry to here, since we're going
    // to overwrite it in the next step either way.
    // (Might be easier to leave the entry as it is rather than set it to Empty?)
    s.(table := s.table[pos := Some(Info(Empty,
        RemoveTidying(rid, initial_key, s.table[pos].value.entry.kv.val)))])
  }

  predicate RemoveFoundIt(s: Variables, s': Variables, pos: nat)
  {
    && RemoveFoundItEnable(s, pos)
    && s' == RemoveFoundItTransition(s, pos)
  }

  predicate TidyEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && ValidHashIndex(pos)
    // The row that needs backfilling is known and we're pointing at it
    && s.table[pos].Some?
    && s.table[pos].value.state.RemoveTidying?
    && s.table[pos].value.entry.Empty?  // Should be an invariant, actually
    && (pos < FixedSize() - 1 ==> s.table[pos+1].Some?) // if a next row, we know it
  }

  predicate DoneTidying(s: Variables, pos: nat)
    requires TidyEnable(s, pos)
  {
    var pos' := NextPos(pos);
    && KnowRowIsFree(s, pos')
    && (
      || s.table[pos'].value.entry.Empty?                     // Next row is empty
      || pos' == hash(s.table[pos'].value.entry.kv.key) as nat  // Next row's key can't move back
    )
  }

  predicate RemoveTidyEnable(s: Variables, pos: nat)
  {
    && TidyEnable(s, pos)
    && !DoneTidying(s, pos)

    && var pos' := NextPos(pos);
    && KnowRowIsFree(s, pos')
  }

  function RemoveTidyTransition(s: Variables, pos: nat): Variables
    requires RemoveTidyEnable(s, pos)
  {
    var pos' := NextPos(pos);
    // Pull the entry back one slot, and push the state pointer forward one slot.
    s.(table := s.table
      [pos := Some(Info(s.table[pos'].value.entry, Free))]
      [pos' := Some(Info(Empty, s.table[pos].value.state))])
  }

  predicate RemoveTidy(s: Variables, s': Variables, pos: nat)
  {
    && RemoveTidyEnable(s, pos)
    && s' == RemoveTidyTransition(s, pos)
  }

  predicate RemoveDoneEnable(s: Variables, pos: nat)
  {
    && TidyEnable(s, pos)
    && DoneTidying(s, pos)
  }

  function RemoveDoneTransition(s: Variables, pos: nat): Variables
    requires RemoveDoneEnable(s, pos)
  {
    // Clear the pointer, return the stub.
    s.(table := s.table[pos := Some(Info(s.table[pos].value.entry, Free))])
      .(insert_capacity := Count.Variables(s.insert_capacity.value + 1))
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput(true))})
  }

  predicate RemoveDone(s: Variables, s': Variables, pos: nat)
  {
    && RemoveDoneEnable(s, pos)
    && s' == RemoveDoneTransition(s, pos)
  }

  // Query

  predicate ProcessQueryTicketEnable(s: Variables, query_ticket: Ticket)
  {
    && !s.Fail?
    && query_ticket.input.QueryInput?
    && query_ticket in s.tickets
    && var h: uint32 := hash(query_ticket.input.key);
    && 0 <= h as int < FixedSize()
    && s.table[h].Some?
    && s.table[h].value.state.Free?
  }
  
  function ProcessQueryTicketTransition(s: Variables, query_ticket: Ticket): Variables
    requires ProcessQueryTicketEnable(s, query_ticket)
  {
    var h: uint32 := hash(query_ticket.input.key);
    s.(tickets := s.tickets - multiset{query_ticket})
      .(table := s.table[h :=
        Some(s.table[h].value.(state := Querying(query_ticket.rid, query_ticket.input.key)))])
  }

  predicate ProcessQueryTicket(s: Variables, s': Variables, query_ticket: Ticket)
  {
    && ProcessQueryTicketEnable(s, query_ticket)
    && s' == ProcessQueryTicketTransition(s, query_ticket)
  }

  predicate QuerySkipEnable(s: Variables, pos: nat)
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

  function QuerySkipTransition(s: Variables, pos: nat): Variables
    requires QuerySkipEnable(s, pos)
  {
    s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [NextPos(pos) := Some(s.table[NextPos(pos)].value.(state := s.table[pos].value.state))])
  }

  predicate QuerySkip(s: Variables, s': Variables, pos: nat)
  {
    && QuerySkipEnable(s, pos)
    && s' == QuerySkipTransition(s, pos)
  }

  predicate QueryDoneEnable(s: Variables, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key == s.table[pos].value.entry.kv.key
  }

  function QueryDoneTransition(s: Variables, pos: nat): Variables
    requires QueryDoneEnable(s, pos)
  {
    var stub := Stub(s.table[pos].value.state.rid, MapIfc.QueryOutput(Found(s.table[pos].value.entry.kv.val)));
    s.(table := s.table[pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{stub})
  }

  predicate QueryDone(s: Variables, s': Variables, pos: nat)
  {
    && QueryDoneEnable(s, pos)
    && s' == QueryDoneTransition(s, pos)
  }

  predicate QueryNotFoundEnable(s: Variables, pos: nat)
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
  }

  function QueryNotFoundTransition(s: Variables, pos: nat): Variables
    requires QueryNotFoundEnable(s, pos)
  {
    s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.QueryOutput(NotFound))})
  }

  predicate QueryNotFound(s: Variables, s': Variables, pos: nat)
  {
    && QueryNotFoundEnable(s, pos)
    && s' == QueryNotFoundTransition(s, pos)
  }

  predicate NextStep(s: Variables, s': Variables, step: Step)
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

  predicate Next(s: Variables, s': Variables)
  {
    exists step :: NextStep(s, s', step)
  }

//////////////////////////////////////////////////////////////////////////////
// global-level Invariant proof
//////////////////////////////////////////////////////////////////////////////

  ////// Invariant

  predicate Complete(table: seq<Option<Info>>)
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
  predicate KeysUnique(table: seq<Option<Info>>)
  requires Complete(table)
  {
    forall i, j | 0 <= i < |table| && 0 <= j < |table| && i != j
      && table[i].value.entry.Full? && table[j].value.entry.Full?
      && !table[i].value.state.RemoveTidying? && !table[j].value.state.RemoveTidying?
        :: table[i].value.entry.kv.key != table[j].value.entry.kv.key
  }

  predicate ValidHashInSlot(table: seq<Option<Info>>, e: int, i: int)
  requires |table| == FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= i < |table|
  {
    // No matter which empty pivot cell 'e' we choose, every entry is 'downstream'
    // of the place that it hashes to.
    // Likewise for insert pointers and others

    table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? ==> (
      && (table[i].value.entry.Full? ==> (
        var h := hash(table[i].value.entry.kv.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
      && (table[i].value.state.Inserting? ==> (
        var h := hash(table[i].value.state.kv.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
      && ((table[i].value.state.Removing? || table[i].value.state.Querying?) ==> (
        var h := hash(table[i].value.state.key) as int;
        && adjust(h, e+1) <= adjust(i, e+1)
      ))
    )
  }

  // 'Robin Hood' order
  // It's not enough to say that hash(entry[i]) <= hash(entry[i+1])
  // because of wraparound. We do a cyclic comparison 'rooted' at an
  // arbitrary empty element, given by e.
  predicate ValidHashOrdering(table: seq<Option<Info>>, e: int, j: int, k: int)
  requires |table| == FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? && table[j].value.entry.Full? && adjust(j, e + 1) < adjust(k, e + 1) ==> (
      var hj := hash(table[j].value.entry.kv.key) as int;

      && (table[k].value.entry.Full? ==> (
        var hk := hash(table[k].value.entry.kv.key) as int;
        && adjust(hj, e + 1) <= adjust(hk, e + 1)
      ))

      // If entry 'k' has an 'Inserting' action on it, then that action must have
      // gotten past entry 'j'.
      && (table[k].value.state.Inserting? ==> (
        var ha := hash(table[k].value.state.kv.key) as int;
        && adjust(hj, e+1) <= adjust(ha, e+1)
      ))

      && ((table[k].value.state.Removing? || table[k].value.state.Querying?) ==> (
        var ha := hash(table[k].value.state.key) as int;
        && adjust(hj, e+1) <= adjust(ha, e+1)
      ))
    ))
  }

  predicate ActionNotPastKey(table: seq<Option<Info>>, e: int, j: int, k: int)
  requires |table| == FixedSize()
  requires Complete(table)
  requires 0 <= e < |table|
  requires 0 <= j < |table|
  requires 0 <= k < |table|
  {
    (table[e].value.entry.Empty? && !table[e].value.state.RemoveTidying? && table[j].value.entry.Full? && adjust(j, e + 1) < adjust(k, e + 1) ==> (
      // If entry 'k' has an 'Inserting' action on it, then that action must not have
      // gotten past entry 'j'.
      && (table[k].value.state.Inserting? ==> (
        table[k].value.state.kv.key != table[j].value.entry.kv.key
      ))
      && ((table[k].value.state.Removing? || table[k].value.state.Querying?) ==> (
        table[k].value.state.key != table[j].value.entry.kv.key
      ))
    ))
  }

  /*predicate ExistsEmptyEntry(table: seq<Option<Info>>)
  {
    exists e :: 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
  }*/

  function InfoQuantity(s: Option<Info>) : nat {
    if s.None? then 0 else (
      (if s.value.state.Inserting? then 1 else 0) +
      (if s.value.state.RemoveTidying? || s.value.entry.Full? then 1 else 0)
    )
  }

  function {:opaque} TableQuantity(s: seq<Option<Info>>) : nat {
    if s == [] then 0 else TableQuantity(s[..|s|-1]) + InfoQuantity(s[|s| - 1])
  }

  predicate TableQuantityInv(s: Variables)
  {
    && s.Variables?
    && TableQuantity(s.table) + s.insert_capacity.value == Capacity()
  }

  predicate InvTable(table: seq<Option<Info>>)
  {
    && |table| == FixedSize()
    && Complete(table)
    //&& ExistsEmptyEntry(table)
    && KeysUnique(table)
    && (forall e, i | 0 <= e < |table| && 0 <= i < |table|
        :: ValidHashInSlot(table, e, i))
    && (forall e, j, k | 0 <= e < |table| && 0 <= j < |table| && 0 <= k < |table|
        :: ValidHashOrdering(table, e, j, k))
    && (forall e, j, k | 0 <= e < |table| && 0 <= j < |table| && 0 <= k < |table|
        :: ActionNotPastKey(table, e, j, k))
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


  lemma TableQuantity_replace1(s: seq<Option<Info>>, s': seq<Option<Info>>, i: int)
  requires 0 <= i < |s| == |s'|
  requires forall j | 0 <= j < |s| :: i != j ==> s[j] == s'[j]
  ensures TableQuantity(s') == TableQuantity(s) + InfoQuantity(s'[i]) - InfoQuantity(s[i])
  {
    reveal_TableQuantity();
    if i == |s| - 1 {
      assert s[..|s|-1] == s'[..|s|-1];
    } else {
      TableQuantity_replace1(s[..|s|-1], s'[..|s'|-1], i);
    }
  }

  lemma TableQuantity_replace2(s: seq<Option<Info>>, s': seq<Option<Info>>, i: int)
  requires 0 <= i < |s| == |s'|
  requires |s| > 1
  requires
      var i' := (if i == |s| - 1 then 0 else i + 1);
      forall j | 0 <= j < |s| :: i != j && i' != j ==> s[j] == s'[j]
  ensures
      var i' := (if i == |s| - 1 then 0 else i + 1);
    TableQuantity(s') == TableQuantity(s)
        + InfoQuantity(s'[i]) - InfoQuantity(s[i])
        + InfoQuantity(s'[i']) - InfoQuantity(s[i'])
  {
    var s0 := s[i := s'[i]];
    TableQuantity_replace1(s, s0, i);
    var i' := (if i == |s| - 1 then 0 else i + 1);
    TableQuantity_replace1(s0, s', i');
  }

  function {:opaque} get_empty_cell(table: seq<Option<Info>>) : (e: int)
  requires InvTable(table)
  requires TableQuantity(table) < |table|
  ensures 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
  {
    assert exists e' :: 0 <= e' < |table| && table[e'].Some? && table[e'].value.entry.Empty?
        && !table[e'].value.state.RemoveTidying? by {
      var t := get_empty_cell_other_than_insertion_cell_table(table);
    }
    var e' :| 0 <= e' < |table| && table[e'].Some? && table[e'].value.entry.Empty?
        && !table[e'].value.state.RemoveTidying?;
    e'
  }

  lemma get_empty_cell_other_than_insertion_cell_table(table: seq<Option<Info>>)
  returns (e: int)
  requires Complete(table)
  requires TableQuantity(table) < |table|
  ensures 0 <= e < |table| && table[e].Some? && table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
        && !table[e].value.state.Inserting?
  {
    reveal_TableQuantity();
    e := |table| - 1;
    if table[e].value.entry.Empty?
        && !table[e].value.state.RemoveTidying?
        && !table[e].value.state.Inserting? {
      return;
    } else {
      e := get_empty_cell_other_than_insertion_cell_table(table[..|table| - 1]);
    }
  }

  lemma get_empty_cell_other_than_insertion_cell(s: Variables)
  returns (e: int)
  requires Inv(s)
  ensures 0 <= e < |s.table| && s.table[e].Some? && s.table[e].value.entry.Empty?
        && !s.table[e].value.state.RemoveTidying?
        && !s.table[e].value.state.Inserting?
  {
    e := get_empty_cell_other_than_insertion_cell_table(s.table);
  }

  lemma ProcessInsertTicket_PreservesInv(s: Variables, s': Variables, insert_ticket: Ticket)
  requires Inv(s)
  requires ProcessInsertTicket(s, s', insert_ticket)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;
    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := hash(insert_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
  }

  lemma InsertSkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires InsertSkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);

      //var k' := if k > 0 then k - 1 else |s.table| - 1;

      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);

      /*if j == pos && (pos == FixedSize() - 1 ==> k == 0) && (pos < FixedSize() - 1 ==> k == j + 1) {
        assert ValidHashOrdering(s'.table, e, j, k);
      } else if j == pos {
        assert ValidHashOrdering(s'.table, e, j, k);
      } else if (pos == FixedSize() - 1 ==> k == 0) && (pos < FixedSize() - 1 ==> k == pos + 1) {
        if s'.table[e].value.entry.Empty? && s'.table[j].value.entry.Full? && adjust(j, e) <= adjust(k, e) && s'.table[k].value.state.Inserting? {
          if j == k {
            assert ValidHashOrdering(s'.table, e, j, k);
          } else {
            assert hash(s.table[j].value.entry.kv.key)
                == hash(s'.table[j].value.entry.kv.key);
            assert hash(s.table[pos].value.state.kv.key)
                == hash(s'.table[k].value.state.kv.key);

            assert s.table[e].value.entry.Empty?;
            assert s.table[j].value.entry.Full?;
            assert adjust(j, e) <= adjust(pos, e);
            assert s.table[pos].value.state.Inserting?;

            assert ValidHashOrdering(s.table, e, j, pos);
            assert ValidHashOrdering(s'.table, e, j, k);
          }
        }
      } else {
        assert ValidHashOrdering(s'.table, e, j, k);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, pos);

      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma InsertSwap_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires InsertSwap(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s.table[i].value.entry.Empty? ==> s'.table[i].value.entry.Empty?;
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);

      var k' := if k > 0 then k - 1 else |s.table| - 1;

      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, pos);

      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);

      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
    }

    forall i | 0 <= i < |s.table| && s.table[i].value.entry.Full?
    ensures s.table[i].value.entry.kv.key != s.table[pos].value.state.kv.key
    {
      //var e :| 0 <= e < |s.table| && s.table[e].value.entry.Empty?
      //  && !s.table[e].value.state.RemoveTidying?;
      var e := get_empty_cell_other_than_insertion_cell(s);
      assert ActionNotPastKey(s.table, e, i, pos);
      //assert ValidHashInSlot(s.table, e, i);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, pos, i);
      //assert ValidHashOrdering(s.table, e, i, pos);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma InsertDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires InsertDone(s, s', pos)
  ensures Inv(s')
  {
    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
      //assert ValidHashInSlot(s.table, e, pos);
      //assert ValidHashOrdering(s.table, e, j, pos);
      //assert ValidHashOrdering(s.table, e, pos, k);

      //assert ActionNotPastKey(s.table, e, j, pos);

      //assert ActionNotPastKey(s.table, pos, j, k);
      //assert ActionNotPastKey(s.table, pos, k, j);

      //assert ValidHashOrdering(s.table, pos, j, k);
      //assert ValidHashOrdering(s.table, pos, k, j);

      //assert ValidHashInSlot(s.table, pos, j);
      assert ValidHashInSlot(s.table, pos, k);
    }

    /*assert ExistsEmptyEntry(s'.table) by {
      var e' := get_empty_cell_other_than_insertion_cell(s);
      assert 0 <= e' < |s'.table| && s'.table[e'].Some? && s'.table[e'].value.entry.Empty?
            && !s'.table[e'].value.state.RemoveTidying?;
    }*/

    forall i | 0 <= i < |s.table| && s.table[i].value.entry.Full?
    ensures s.table[i].value.entry.kv.key != s.table[pos].value.state.kv.key
    {
      //var e :| 0 <= e < |s.table| && s'.table[e].value.entry.Empty?
        //&& !s.table[e].value.state.RemoveTidying?;
      var e := get_empty_cell_other_than_insertion_cell(s);
      assert ActionNotPastKey(s.table, e, i, pos);
      //assert ActionNotPastKey(s.table, e, pos, i);
      assert ValidHashInSlot(s.table, e, pos);
      //assert ValidHashInSlot(s.table, e, i);
      //assert ValidHashOrdering(s.table, e, pos, i);
      //assert ValidHashOrdering(s.table, e, i, pos);

      //assert ActionNotPastKey(s.table, pos, i, pos);
      //assert ActionNotPastKey(s.table, pos, pos, i);
      //assert ValidHashInSlot(s.table, pos, pos);
      assert ValidHashInSlot(s.table, pos, i);
      //assert ValidHashOrdering(s.table, pos, pos, i);
      //assert ValidHashOrdering(s.table, pos, i, pos);
    }

    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);

      //assert ActionNotPastKey(s.table, e, j, pos);
      //assert ActionNotPastKey(s.table, e, k, pos);
      //assert ActionNotPastKey(s.table, e, pos, j);
      //assert ActionNotPastKey(s.table, e, pos, k);
      //assert ActionNotPastKey(s.table, e, j, k);
      //assert ActionNotPastKey(s.table, e, k, j);
      //assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashInSlot(s.table, e, j);
      //assert ValidHashInSlot(s.table, e, k);
      //assert ValidHashOrdering(s.table, e, pos, j);
      //assert ValidHashOrdering(s.table, e, j, pos);
      //assert ValidHashOrdering(s.table, e, pos, k);
      //assert ValidHashOrdering(s.table, e, k, pos);
      //assert ValidHashOrdering(s.table, e, j, k);
      //assert ValidHashOrdering(s.table, e, k, j);

      //assert ActionNotPastKey(s.table, pos, j, pos);
      //assert ActionNotPastKey(s.table, pos, pos, j);
      //assert ActionNotPastKey(s.table, pos, k, pos);
      //assert ActionNotPastKey(s.table, pos, pos, k);
      //assert ActionNotPastKey(s.table, pos, k, j);
      //assert ActionNotPastKey(s.table, pos, j, k);
      //assert ValidHashInSlot(s.table, pos, pos);
      //assert ValidHashInSlot(s.table, pos, j);
      assert ValidHashInSlot(s.table, pos, k);
      //assert ValidHashOrdering(s.table, pos, pos, j);
      //assert ValidHashOrdering(s.table, pos, j, pos);
      //assert ValidHashOrdering(s.table, pos, pos, k);
      //assert ValidHashOrdering(s.table, pos, k, pos);
      //assert ValidHashOrdering(s.table, pos, j, k);
      //assert ValidHashOrdering(s.table, pos, k, j);

    }

    TableQuantity_replace1(s.table, s'.table, pos);
  }

  lemma InsertUpdate_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires InsertUpdate(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s.table[i].value.entry.Empty? ==> s'.table[i].value.entry.Empty?;

    forall e, i | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace1(s.table, s'.table, pos);
  }

  lemma ProcessQueryTicket_PreservesInv(s: Variables, s': Variables, query_ticket: Ticket)
  requires Inv(s)
  requires ProcessQueryTicket(s, s', query_ticket)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := hash(query_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
  }

  lemma QuerySkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires QuerySkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, pos);
      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma QueryDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires QueryDone(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma QueryNotFound_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires QueryNotFound(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma ProcessRemoveTicket_PreservesInv(s: Variables, s': Variables, remove_ticket: Ticket)
  requires Inv(s)
  requires ProcessRemoveTicket(s, s', remove_ticket)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    var h := hash(remove_ticket.input.key) as int;
    TableQuantity_replace1(s.table, s'.table, h);
  }

  lemma RemoveSkip_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires RemoveSkip(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);

      var i' := if i > 0 then i - 1 else |s.table| - 1;
      assert ValidHashInSlot(s.table, e, i');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
      assert ValidHashInSlot(s.table, e, k);
      assert ValidHashInSlot(s.table, e, pos);
      assert ValidHashOrdering(s.table, e, j, pos);
      assert ValidHashOrdering(s.table, e, pos, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, pos);
      assert ActionNotPastKey(s.table, e, j, k);
      assert ValidHashInSlot(s.table, e, j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveFoundIt_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires RemoveFoundIt(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: i != pos ==> s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveNotFound_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires RemoveNotFound(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: i != pos ==> s'.table[i].value.entry == s.table[i].value.entry;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveTidy_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires RemoveTidy(s, s', pos)
  ensures Inv(s')
  {
    /*assert ExistsEmptyEntry(s'.table) by {
      var e :| 0 <= e < |s.table| && s.table[e].Some? && s.table[e].value.entry.Empty?
        && !s.table[e].value.state.RemoveTidying?;
      assert 0 <= e < |s'.table| && s'.table[e].Some? && s'.table[e].value.entry.Empty?
        && !s'.table[e].value.state.RemoveTidying?;
    }*/

    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      assert ValidHashInSlot(s.table, e, i);
      assert ValidHashInSlot(s.table, e, pos');
      //assert ValidHashOrdering(s.table, e, pos, pos');
      /*if i == pos {
        if s'.table[e].value.entry.Empty? && !s'.table[e].value.state.RemoveTidying?
            && s'.table[i].value.entry.Full? && s.table[pos'].value.entry.Full? {
          var h := hash(s'.table[i].value.entry.kv.key) as int;
          assert h == hash(s.table[pos'].value.entry.kv.key) as int;

          assert e < h <= pos'
           || h <= pos' < e
           || pos' < e < h;

          assert h != pos';

          assert e < h <= pos
           || h <= pos < e
           || pos < e < h;

          assert ValidHashInSlot(s'.table, e, i);
        }

        assert ValidHashInSlot(s'.table, e, i);
      } else {
        assert ValidHashInSlot(s'.table, e, i);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      assert ValidHashOrdering(s.table, e, j, k);
      assert ValidHashOrdering(s.table, e, pos', k);
      assert ValidHashOrdering(s.table, e, j, pos');
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      assert ActionNotPastKey(s.table, e, j, k);
      assert ActionNotPastKey(s.table, e, pos', k);
      assert ActionNotPastKey(s.table, e, j, pos');
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma RemoveDone_PreservesInv(s: Variables, s': Variables, pos: nat)
  requires Inv(s)
  requires RemoveDone(s, s', pos)
  ensures Inv(s')
  {
    assert forall i | 0 <= i < |s'.table| :: s'.table[i].value.entry == s.table[i].value.entry;

    var pos' := if pos < |s.table| - 1 then pos + 1 else 0;

    assert s'.table[pos].value.entry.Empty?;

    forall i, e | 0 <= i < |s'.table| && 0 <= e < |s'.table|
    ensures ValidHashInSlot(s'.table, e, i)
    {
      var e' := get_empty_cell(s.table);
      
      assert ValidHashInSlot(s.table, e, i);

      assert ValidHashInSlot(s.table, pos', i);
      assert ValidHashOrdering(s.table, e', pos', i);

      assert ValidHashInSlot(s.table, e', i);

      assert ValidHashInSlot(s.table, i, e');

      //assert ValidHashInSlot(s.table, e', pos');
      //assert ValidHashInSlot(s.table, pos', e');

      //assert ValidHashInSlot(s.table, i, e);
      //assert ValidHashOrdering(s.table, e', i, pos');
      //assert ValidHashInSlot(s.table, pos, i);
      //assert ValidHashOrdering(s.table, e', pos, i);
      //assert ValidHashOrdering(s.table, e', i, pos);

      /*var e1 := if e < |s.table| - 1 then e + 1 else 0;
 
      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashInSlot(s.table, pos', i);
      assert ValidHashOrdering(s.table, e1, pos', i);

      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashInSlot(s.table, i, e1);

      assert ValidHashInSlot(s.table, e1, pos');
      assert ValidHashInSlot(s.table, pos', e1);

      assert ValidHashInSlot(s.table, i, e);
      assert ValidHashOrdering(s.table, e1, i, pos');
      assert ValidHashInSlot(s.table, pos, i);
      assert ValidHashOrdering(s.table, e1, pos, i);
      assert ValidHashOrdering(s.table, e1, i, pos);

      assert ValidHashOrdering(s.table, e1, i, e);
      assert ValidHashOrdering(s.table, e1, e, i);
      assert ValidHashInSlot(s.table, e1, i);

      assert ValidHashOrdering(s.table, e', e, e1);

      assert ValidHashOrdering(s.table, e', e1, i);
      assert ValidHashInSlot(s.table, e', e1);

      assert ValidHashInSlot(s.table, e, e);
      assert ValidHashInSlot(s.table, e', e');
      assert ValidHashInSlot(s.table, e1, e1);

      assert ValidHashInSlot(s.table, e', i);

      assert ValidHashOrdering(s.table, e', e, i);*/


      /*if e == pos {
        if i == pos' {
          assert ValidHashInSlot(s'.table, e, i);
        } else {
          if s.table[pos'].value.entry.Full? {
            if adjust(i, pos) < adjust(e', pos) {
              assert ValidHashInSlot(s'.table, e, i);
            } else if i == e' {
              assert s.table[e1].value.entry.Full?  ==>
                  hash(s.table[e1].value.entry.kv.key) as int
                == e1;
              
              if s.table[e1].value.entry.Full? {
                if e == e' {
                  assert ValidHashInSlot(s'.table, e, i);
                } else {
                  assert ValidHashInSlot(s'.table, e, i);
                }
              } else {
                assert ValidHashInSlot(s'.table, e, i);
              }
            } else {
              assert ValidHashInSlot(s'.table, e, i);
            }
          } else {
            assert ValidHashInSlot(s'.table, e, i);
          }
        }
      } else {
        assert ValidHashInSlot(s'.table, e, i);
      }*/
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ValidHashOrdering(s'.table, e, j, k)
    {
      var e' := get_empty_cell(s.table);

      assert ValidHashOrdering(s.table, e, j, k);

      assert ValidHashOrdering(s.table, e', j, k);
      //assert ValidHashOrdering(s.table, e', k, j);

      assert ValidHashInSlot(s.table, pos', j);
      assert ValidHashOrdering(s.table, e', pos', j);
      //assert ValidHashInSlot(s.table, e', j);

      //assert ValidHashInSlot(s.table, pos', k);
      //assert ValidHashOrdering(s.table, e', pos', k);
      assert ValidHashInSlot(s.table, e', k);
    }
    forall e, j, k | 0 <= e < |s'.table| && 0 <= j < |s'.table| && 0 <= k < |s'.table|
    ensures ActionNotPastKey(s'.table, e, j, k)
    {
      var e' := get_empty_cell(s.table);

      assert ActionNotPastKey(s.table, e, j, k);

      //assert ValidHashOrdering(s.table, e, j, k);
      //assert ValidHashOrdering(s.table, e', j, k);
      assert ValidHashInSlot(s.table, pos', j);
      assert ValidHashOrdering(s.table, e', pos', j);
      assert ValidHashInSlot(s.table, e', k);

      //assert ActionNotPastKey(s.table, e, j, k);
      assert ActionNotPastKey(s.table, e', j, k);
      //assert ActionNotPastKey(s.table, e', pos', j);
    }

    TableQuantity_replace2(s.table, s'.table, pos);
  }

  lemma NextStep_PreservesInv(s: Variables, s': Variables, step: Step)
  requires Inv(s)
  requires NextStep(s, s', step)
  ensures Inv(s')
  {
    match step {
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicket_PreservesInv(s, s', insert_ticket);
      case InsertSkipStep(pos) => InsertSkip_PreservesInv(s, s', pos);
      case InsertSwapStep(pos) => InsertSwap_PreservesInv(s, s', pos);
      case InsertDoneStep(pos) => InsertDone_PreservesInv(s, s', pos);
      case InsertUpdateStep(pos) => InsertUpdate_PreservesInv(s, s', pos);

      case ProcessRemoveTicketStep(remove_ticket) => ProcessRemoveTicket_PreservesInv(s, s', remove_ticket);
      case RemoveSkipStep(pos) => RemoveSkip_PreservesInv(s, s', pos);
      case RemoveFoundItStep(pos) => RemoveFoundIt_PreservesInv(s, s', pos);
      case RemoveNotFoundStep(pos) => RemoveNotFound_PreservesInv(s, s', pos);
      case RemoveTidyStep(pos) => RemoveTidy_PreservesInv(s, s', pos);
      case RemoveDoneStep(pos) => RemoveDone_PreservesInv(s, s', pos);

      case ProcessQueryTicketStep(query_ticket) => ProcessQueryTicket_PreservesInv(s, s', query_ticket);
      case QuerySkipStep(pos) => QuerySkip_PreservesInv(s, s', pos);
      case QueryDoneStep(pos) => QueryDone_PreservesInv(s, s', pos);
      case QueryNotFoundStep(pos) => QueryNotFound_PreservesInv(s, s', pos);
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

  function {:opaque} GetRemainder(s: Variables): (t: Variables)
    requires Valid(s)
    ensures Inv(add(s, t))
  {
    // reveal Valid();
    var t :| Inv(add(s, t));
    t
  }

  lemma InvImpliesValid(s: Variables)
    requires Inv(s)
    ensures Valid(s)
  {
    // reveal Valid();
    add_unit(s);
  }

  lemma valid_monotonic(x: Variables, y: Variables)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
    // reveal Valid();
    var xy' :| Inv(add(add(x, y), xy'));
    associative(x, y, xy');
    assert Inv(add(x, add(y, xy')));
  }

  lemma update_monotonic(x: Variables, y: Variables, z: Variables)
  //requires Next(x, y)
  //requires Valid(add(x, z))
  ensures Next(add(x, z), add(y, z))
  {
    var step :| NextStep(x, y, step);
    assert NextStep(add(x, z), add(y, z), step);
  }

  lemma EmptyTableQuantityIsZero(infos: seq<Option<Info>>)
    requires (forall i | 0 <= i < |infos| :: infos[i] == Some(Info(Empty, Free)))
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
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicketEnable(s, insert_ticket)
      case InsertSkipStep(pos) => InsertSkipEnable(s, pos)
      case InsertSwapStep(pos) => InsertSwapEanble(s, pos)
      case InsertDoneStep(pos) => InsertDoneEnable(s, pos)
      case InsertUpdateStep(pos) => InsertUpdateEnable(s, pos)

      case ProcessRemoveTicketStep(remove_ticket) => ProcessRemoveTicketEnable(s, remove_ticket)
      case RemoveSkipStep(pos) => RemoveSkipEnable(s, pos)
      case RemoveFoundItStep(pos) => RemoveFoundItEnable(s, pos)
      case RemoveNotFoundStep(pos) => RemoveNotFoundEnable(s, pos)
      case RemoveTidyStep(pos) => RemoveTidyEnable(s, pos)
      case RemoveDoneStep(pos) => RemoveDoneEnable(s, pos)

      case ProcessQueryTicketStep(query_ticket) => ProcessQueryTicketEnable(s, query_ticket)
      case QuerySkipStep(pos) => QuerySkipEnable(s, pos)
      case QueryDoneStep(pos) => QueryDoneEnable(s, pos)
      case QueryNotFoundStep(pos) => QueryNotFoundEnable(s, pos)
    }
  }

  function GetTransition(s: Variables, step: Step): (s': Variables)
    requires TransitionEnable(s, step)
    ensures NextStep(s, s', step);
  {
    match step {
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicketTransition(s, insert_ticket)
      case InsertSkipStep(pos) => InsertSkipTransition(s, pos)
      case InsertSwapStep(pos) => InsertSwapTransition(s, pos)
      case InsertDoneStep(pos) => InsertDoneTransition(s, pos)
      case InsertUpdateStep(pos) => InsertUpdateTransition(s, pos)

      case ProcessRemoveTicketStep(remove_ticket) => ProcessRemoveTicketTransition(s, remove_ticket)
      case RemoveSkipStep(pos) => RemoveSkipTransition(s, pos)
      case RemoveFoundItStep(pos) => RemoveFoundItTransition(s, pos)
      case RemoveNotFoundStep(pos) => RemoveNotFoundTransition(s, pos)
      case RemoveTidyStep(pos) => RemoveTidyTransition(s, pos)
      case RemoveDoneStep(pos) => RemoveDoneTransition(s, pos)

      case ProcessQueryTicketStep(query_ticket) => ProcessQueryTicketTransition(s, query_ticket)
      case QuerySkipStep(pos) => QuerySkipTransition(s, pos)
      case QueryDoneStep(pos) => QueryDoneTransition(s, pos)
      case QueryNotFoundStep(pos) => QueryNotFoundTransition(s, pos)
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
    // ensures unit_r == unit()
}
