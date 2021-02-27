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

  predicate ValidHashIndex(h:int) {
    0 <= h as int < FixedSize()
  }

  function method hash(key: uint64) : (h:uint32)
    ensures ValidHashIndex(h as int)

  datatype KV = KV(key: uint64, val: Value)

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
    | Inserting(rid: int, kv: KV)
    | Removing(rid: int, key: uint64)
    | RemoveTidying(rid: int)

      // Why do we need to store query state to support an invariant over the
      // hash table interpretation, since query is a read-only operation?
      // Because the query's result is defined at the moment it begins (its
      // serialization point), which is to say the proof ghostily knows the
      // answer when the query begins. We need to show inductively that that
      // answer stays the same with each step of any thread, until the impl
      // gets far enough to discover the answer in the real data structure.
      // We're showing that we inductively preserve the value of the
      // interpretation of the *answer* to query #rid.
    | Querying(rid: int, key: uint64)

  // TODO rename
  datatype Info = Info(entry: Entry, state: State)

  datatype PreR =
      | R(table: seq<Option<Info>>,
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

  function unit() : R {
    R(seq(FixedSize(), i => None), multiset{}, multiset{})
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
    && (forall i | 0 < i < |s.table| :: s.table[i] == Some(Info(Empty, Free)))
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
    && var h: uint32 := hash(insert_ticket.input.key);
    && 0 <= h as int < |s.table|
    && s.table[h].Some?
    && s.table[h].value.state.Free?
    && s' == s
      .(tickets := s.tickets - multiset{insert_ticket})
      .(table := s.table[h := Some(
          s.table[h].value.(state :=
            Inserting(insert_ticket.rid,
              KV(insert_ticket.input.key, insert_ticket.input.value))))])
  }

  predicate ShouldHashGoBefore(search_h: int, slot_h: int, slot_idx: int)
  {
    || search_h < slot_h <= slot_idx
    || slot_h <= slot_idx < search_h
    || slot_idx < search_h < slot_h
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
    && !ShouldHashGoBefore(
        hash(s.table[pos].value.state.kv.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[pos].value.state.kv.key
        != s.table[pos].value.entry.kv.key
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
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    && ShouldHashGoBefore(
        hash(s.table[pos].value.state.kv.key) as int,
        hash(s.table[pos].value.entry.kv.key) as int, pos)
    && s.table[pos'].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(Info(
          Full(s.table[pos].value.state.kv),
          Free))]
        [pos' := Some(s.table[pos'].value.(state :=
          Inserting(
            s.table[pos].value.state.rid,
            s.table[pos].value.entry.kv)))])
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
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput)})
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
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.InsertOutput)})
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

  predicate RemoveSkipEnabled(s: R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize() - 1
    && KnowRowIsFree(s, pos+1)
    // Know row pos, and it's the thing we're removing, and it's full...
    && s.table[pos].Some?
    && s.table[pos].value.state.Removing?
    && s.table[pos].value.entry.Full?
    // ...and the key it's full of sorts before the thing we're looking to remove.
    && hash(s.table[pos].value.entry.kv.key) <= hash(s.table[pos].value.state.key)
  }

  predicate RemoveSkip(s: R, s': R, pos: nat)
  {
    && RemoveSkipEnabled(s, pos)
    // The hash is equal, but this isn't the key we're trying to remove.
    && s.table[pos].value.entry.kv.key != s.table[pos].value.state.key

    // Advance the pointer to the next row.
    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos + 1 := Some(s.table[pos + 1].value.(state := s.table[pos].value.state))])
  }

  predicate RemoveFoundIt(s: R, s': R, pos: nat)
  {
    && RemoveSkipEnabled(s, pos)
    // This IS the key we want to remove!
    && s.table[pos].value.entry.kv.key == s.table[pos].value.state.key

    // Change the program counter into RemoveTidying mode
    && var rid := s.table[pos].value.state.rid;
    && s' == s.(table := s.table[pos := Some(Info(Empty, RemoveTidying(rid)))])
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
    || (pos == FixedSize() - 1)
    || (
      && KnowRowIsFree(s, pos+1)                               // Next row is off end of the array
      && (
        || s.table[pos].value.entry.Empty?                     // Next row is empty
        || pos < hash(s.table[pos].value.entry.kv.key) as nat  // Next row's key can't move back
      )
    )
  }

  predicate RemoveTidy(s: R, s': R, pos: nat)
  {
    && TidyEnabled(s, pos)
    && !DoneTidying(s, pos)

    // Pull the entry back one slot, and push the state pointer forward one slot.
    && s' == s.(table := s.table
      [pos := Some(Info(s.table[pos+1].value.entry, Free))]
      [pos+1 := Some(Info(Empty, s.table[pos].value.state))]
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
      .(stubs := s.stubs + multiset{Stub(s.table[pos].value.state.rid, MapIfc.RemoveOutput)})
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

  predicate QuerySkip(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && var pos' := (if pos < FixedSize() - 1 then pos + 1 else 0);
    && s.table[pos].Some?
    && s.table[pos'].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key != s.table[pos].value.entry.kv.key
    && s.table[pos'].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos' := Some(s.table[pos'].value.(state := s.table[pos].value.state))])
  }

  predicate QueryDone(s: R, s': R, pos: nat)
  {
    && !s.Fail?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key == s.table[pos].value.entry.kv.key
    && s' == s
      .(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{
        Stub(s.table[pos].value.state.rid,
                  MapIfc.QueryOutput(Found(s.table[pos].value.entry.kv.val)))
       })
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
      hash(s.table[pos].value.state.key) < hash(s.table[pos].value.entry.kv.key))
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

  predicate Valid(s: R) {
    s.R?
  }

  lemma valid_monotonic(x: R, y: R)
  //requires Valid(add(x, y))
  ensures Valid(x)
  {
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
  }

  lemma InitImpliesValid(s: R)
  //requires Init(s)
  //ensures Valid(s)
  {
  }

  lemma UpdatePreservesValid(s: R, t: R)
  //requires Update(s, t)
  //requires Valid(s)
  ensures Valid(t)
  {
  }

  method easy_transform(
      linear b: R,
      ghost expected_out: R)
  returns (linear c: R)
  requires Update(b, expected_out)
  ensures c == expected_out
  // travis promises to supply this
}
