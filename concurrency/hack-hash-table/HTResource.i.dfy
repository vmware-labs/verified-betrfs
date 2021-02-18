include "../hack-concurrency-framework/ApplicationResourceSpec.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"

module HTResource refines ApplicationResourceSpec {
  import opened NativeTypes
  import opened Options

  type V(==)

  datatype Ticket =
    | InsertTicket(rid: int, key: uint64, val: V)
    | QueryTicket(rid: int, key: uint64)

  datatype QueryResult = Found(val: V) | NotFound

  datatype Stub =
    | InsertStub(rid: int)
    | QueryStub(rid: int, res: QueryResult)

  function method hash(key: uint64) : uint32

  function FixedSize() : nat

  datatype KV = KV(key: uint64, val: V)

  datatype Entry =
    | Full(kv: KV)
    | Empty
  datatype State =
    | Free
    | Inserting(rid: int, kv: KV)
    | Querying(rid: int, key: uint64)

  datatype Info = Info(entry: Entry, state: State)

  datatype PreR =
      | R(table: seq<Option<Info>>,
          tickets: multiset<Ticket>,
          stubs: multiset<Stub>)
      | Fail
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
    s == unit()
  }

  datatype Step =
    | ProcessInsertTicketStep(insert_ticket: Ticket)
    | InsertSkipStep(pos: nat)
    | InsertSwapStep(pos: nat)
    | InsertDoneStep(pos: nat)

    | ProcessQueryTicketStep(query_ticket: Ticket)
    | QuerySkipStep(pos: nat)
    | QueryDoneStep(pos: nat)
    | QueryNotFoundStep(pos: nat)

  predicate ProcessInsertTicket(s: R, s': R, insert_ticket: Ticket)
  {
    && s.R?
    && s'.R?
    && insert_ticket.InsertTicket?
    && insert_ticket in s.tickets
    && var h: uint32 := hash(insert_ticket.key);
    && 0 <= h as int < |s.table|
    && s.table[h].Some?
    && s.table[h].value.state.Free?
    && s' == s
      .(tickets := s.tickets - multiset{insert_ticket})
      .(table := s.table[h := Some(
          s.table[h].value.(state :=
            Inserting(insert_ticket.rid, KV(insert_ticket.key, insert_ticket.val))))])
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) >= hash(pos j)
  // we skip item i and move to i+1.
  predicate InsertSkip(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
    && 0 <= pos < FixedSize() - 1
    && s.table[pos].Some?
    && s.table[pos + 1].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    && hash(s.table[pos].value.state.kv.key) >= hash(s.table[pos].value.entry.kv.key)
    && s.table[pos + 1].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos + 1 := Some(s.table[pos].value.(state := s.table[pos].value.state))])
  }

  // We're trying to insert new_item at pos j
  // where hash(new_item) < hash(pos j)
  // in this case we do the swap and keep moving forward
  // with the swapped-out item.
  predicate InsertSwap(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
    && 0 <= pos < FixedSize() - 1
    && s.table[pos].Some?
    && s.table[pos + 1].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Full?
    && hash(s.table[pos].value.state.kv.key) < hash(s.table[pos].value.entry.kv.key)
    && s.table[pos + 1].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(Info(
          Full(s.table[pos].value.state.kv),
          Free))]
        [pos + 1 := Some(s.table[pos].value.(state :=
          Inserting(
            s.table[pos].value.state.rid,
            s.table[pos].value.entry.kv)))])
  }

  // Slot is empty. Insert our element and finish.
  predicate InsertDone(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Inserting?
    && s.table[pos].value.entry.Empty?
    && s' == s
      .(table := s.table
        [pos := Some(Info(
            Full(s.table[pos].value.state.kv),
            Free))])
      .(stubs := s.stubs + multiset{InsertStub(s.table[pos].value.state.rid)})
  }

  predicate ProcessQueryTicket(s: R, s': R, query_ticket: Ticket)
  {
    && s.R?
    && s'.R?
    && query_ticket.QueryTicket?
    && query_ticket in s.tickets
    && var h: uint32 := hash(query_ticket.key);
    && 0 <= h as int < FixedSize()
    && s.table[h].Some?
    && s' == s
      .(tickets := s.tickets - multiset{query_ticket})
      .(table := s.table[h := Some(
          s.table[h].value.(state :=
            Querying(query_ticket.rid, query_ticket.key)))])
  }

  predicate QuerySkip(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
    && 0 <= pos < FixedSize() - 1
    && s.table[pos].Some?
    && s.table[pos + 1].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key != s.table[pos].value.entry.kv.key
    && s.table[pos + 1].value.state.Free?

    && s' == s.(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))]
        [pos + 1 := Some(s.table[pos].value.(state := s.table[pos].value.state))])
  }

  predicate QueryDone(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
    && 0 <= pos < FixedSize()
    && s.table[pos].Some?
    && s.table[pos].value.state.Querying?
    && s.table[pos].value.entry.Full?
    && s.table[pos].value.state.key == s.table[pos].value.entry.kv.key
    && s' == s
      .(table := s.table
        [pos := Some(s.table[pos].value.(state := Free))])
      .(stubs := s.stubs + multiset{
        QueryStub(s.table[pos].value.state.rid,
                  Found(s.table[pos].value.entry.kv.val))
       })
  }

  predicate QueryNotFound(s: R, s': R, pos: nat)
  {
    && s.R?
    && s'.R?
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
        QueryStub(s.table[pos].value.state.rid, NotFound)
       })
  }

  predicate UpdateStep(s: R, s': R, step: Step)
  {
    match step {
      case ProcessInsertTicketStep(insert_ticket) => ProcessInsertTicket(s, s', insert_ticket)
      case InsertSkipStep(pos) => InsertSkip(s, s', pos)
      case InsertSwapStep(pos) => InsertSwap(s, s', pos)
      case InsertDoneStep(pos) => InsertDone(s, s', pos)

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
    match step {
      case ProcessInsertTicketStep(insert_ticket) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case InsertSkipStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case InsertSwapStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case InsertDoneStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case ProcessQueryTicketStep(query_ticket) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case QuerySkipStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case QueryDoneStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case QueryNotFoundStep(pos) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
    }
  }

  /*function input_ticket(id: int, input: Ifc.Input) : R {
    R(multiset{Ticket(id, input)}, multiset{}, 0, 0)
  }

  function output_stub(id: int, output: Ifc.Output) : R {
    R(multiset{}, multiset{Stub(id, output)}, 0, 0)
  }*/

  predicate Inv(s: R) {
    true
  }

  lemma UpdatePreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires Update(s, s')
  ensures Inv(s')
  {
  }

  lemma NewTicketPreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires NewTicket(s, s')
  ensures Inv(s')
  {
  }

  lemma ConsumeStubPreservesInv(s: R, s': R)
  //requires Inv(s)
  //requires ConsumeStub(s, s')
  ensures Inv(s')
  {
  }

  method easy_transform(
      linear b: R,
      ghost expected_out: R)
  returns (linear c: R)
  requires Update(b, expected_out)
  ensures c == expected_out
  {
    shared var u := get_unit_shared();
    ghost var a := u;
    forall a' | radical(a', a) && Valid(add(a', b))
    ensures Update(add(a', b), add(a', expected_out))
    {
      update_monotonic(b, expected_out, a');
      commutative(a', b);
      commutative(a', expected_out);
    }
    c := do_transform(u, b, expected_out);
  }

  /*method do_tr(linear t: R, linear s: R, ticket: Ticket, batches: nat)
  returns (linear stub: R, linear s': R)
  requires t == input_ticket(ticket.rid, ticket.input)
  requires batches <= ticket.input.sugar + s.sugar
  requires batches <= ticket.input.butter + s.butter
  ensures stub == output_stub(ticket.rid, Ifc.Output(6 * batches))
  ensures s' == s
    .(sugar := ticket.input.sugar + s.sugar - batches)
    .(butter := ticket.input.butter + s.butter - batches)
  {
    linear var total := join(t, s);
    ghost var total_exp := total
      .(tickets := total.tickets - multiset{ticket})
      .(stubs := total.stubs + multiset{Stub(ticket.rid, Ifc.Output(6 * batches))})
      .(sugar := ticket.input.sugar + s.sugar - batches)
      .(butter := ticket.input.butter + s.butter - batches);
    assert do_request(total, total_exp, ticket, batches);
    linear var total' := easy_transform(total, total_exp);
    stub, s' := split(total', 
        output_stub(ticket.rid, Ifc.Output(6 * batches)),
        s.(sugar := ticket.input.sugar + s.sugar - batches)
         .(butter := ticket.input.butter + s.butter - batches)
    );
  }*/
}
