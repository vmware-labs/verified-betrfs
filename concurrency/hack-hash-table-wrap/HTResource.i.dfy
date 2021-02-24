include "ApplicationResourceSpec.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "MapSpec.s.dfy"
include "RobinHood.i.dfy"

module HTResource refines ApplicationResourceSpec {
  import opened NativeTypes
  import opened Options

  import RobinHood

  import opened KeyValueType
  import MapIfc

  datatype Ticket =
    | Ticket(rid: int, input: MapIfc.Input)

  datatype Stub =
    | Stub(rid: int, output: MapIfc.Output)

  function FixedSize() : nat

  datatype Entry =
    | Full(key: uint64, value: Value)
    | Empty

  datatype PreR =
      | R(table: seq<Option<Entry>>,
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
    && s.R?
    && (forall i | 0 < i < |s.table| :: s.table[i] == Some(Empty))
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  datatype Step =
    | QueryFoundStep(ticket: Ticket, i: int)
    | QueryNotFoundStep(ticket: Ticket, end: int)

    | RemoveStep(ticket: Ticket, i: int, end: int)
    | RemoveNotFoundStep(ticket: Ticket, end: int)

    | OverwriteStep(ticket: Ticket, i: int)
    | InsertStep(ticket: Ticket, i: int)

  // Query

  predicate QueryFound(s: R, s': R, ticket: Ticket, i: int)
  {
    && s.R?
    && s'.R?
    && ticket in s.tickets
    && ticket.input.QueryInput?
    && 0 <= i < |s.table|
    && s.table[i].Some?
    && s.table[i].value.Full?
    && s.table[i].value.key == ticket.input.key
    && s' == s
      .(tickets := s.tickets - multiset{ticket})
      .(stubs := s.stubs + multiset{Stub(ticket.rid,
          MapIfc.QueryOutput(Found(s.table[i].value.value)))})
  }

  predicate KeyNotFound(table: seq<Option<Entry>>, key: Key, end: int)
  {
    && 0 <= end < |table|
    && table[end].Some?
    && table[end].value.Empty?
    && var h := RobinHood.hash(key) as int;
    && (h <= end ==> forall j | h <= j < end     :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
    && (h > end  ==> forall j | h <= j < |table| :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
    && (h > end  ==> forall j | 0 <= j < end     :: table[j].Some? && table[j].value.Full? && table[j].value.key != key)
  }

  predicate QueryNotFound(s: R, s': R, ticket: Ticket, end: int)
  {
    && s.R?
    && s'.R?
    && ticket in s.tickets
    && ticket.input.QueryInput?
    && KeyNotFound(s.table, ticket.input.key, end)
    && s' == s
      .(tickets := s.tickets - multiset{ticket})
      .(stubs := s.stubs + multiset{Stub(ticket.rid,
          MapIfc.QueryOutput(NotFound))})
  }

  // Insert

  predicate Overwrite(s: R, s': R, ticket: Ticket, i: int)
  {
    && s.R?
    && s'.R?
    && ticket in s.tickets
    && ticket.input.InsertInput?
    && 0 <= i < |s.table|
    && s.table[i].Some?
    && s.table[i].value.Full?
    && s.table[i].value.key == ticket.input.key
    && s' == s
      .(tickets := s.tickets - multiset{ticket})
      .(stubs := s.stubs + multiset{Stub(ticket.rid, MapIfc.InsertOutput)})
      .(table := s.table[i := Some(Full(ticket.input.key, ticket.input.value))])
  }

  // Remove

  predicate RemoveNotFound(s: R, s': R, ticket: Ticket, end: int)
  {
    && s.R?
    && s'.R?
    && ticket in s.tickets
    && ticket.input.RemoveInput?
    && KeyNotFound(s.table, ticket.input.key, end)
    && s' == s
      .(tickets := s.tickets - multiset{ticket})
      .(stubs := s.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput)})
  }

  predicate LeftShift_PartialState(table: seq<Option<Entry>>, table': seq<Option<Entry>>, shift: RobinHood.LeftShift)
  {
    && 0 <= shift.start < |table|
    && 0 <= shift.end < |table|
    && |table'| == |table|

    && (shift.start <= shift.end ==>
      && (forall i | 0 <= i < shift.start :: table'[i] == table[i])
      && (forall i | shift.start <= i < shift.end :: table'[i] == table[i+1] && table'[i].Some?)
      && table'[shift.end] == Some(Empty)
      && (forall i | shift.end < i < |table'| :: table'[i] == table[i])
    )

    && (shift.start > shift.end ==>
      && (forall i | 0 <= i < shift.end :: table'[i] == table[i+1])
      && table'[shift.end] == Some(Empty)
      && (forall i | shift.end < i < shift.start :: table'[i] == table[i])
      && (forall i | shift.start <= i < |table'| - 1 :: table'[i] == table[i+1] && table'[i].Some?)
      && table'[|table'| - 1] == table[0]
    )
  }

  predicate Remove(s: R, s': R, ticket: Ticket, i: int, end: int)
  {
    && s.R?
    && s'.R?
    && ticket in s.tickets
    && ticket.input.RemoveInput?
    && 0 <= i < |s.table|
    && s.table[i].Some?
    && s.table[i].value.Full?
    && s.table[i].value.key == ticket.input.key
    && LeftShift_PartialState(s.table, s'.table, RobinHood.LeftShift(i, end))
    && s' == s.(table := s'.table)
        .(tickets := s.tickets - multiset{ticket})
        .(stubs := s.stubs + multiset{Stub(ticket.rid, MapIfc.RemoveOutput)})
  }

  // All together

  predicate UpdateStep(s: R, s': R, step: Step)
  {
    match step {
      case QueryFoundStep(ticket, i) => QueryFound(s, s', ticket, i)
      case QueryNotFoundStep(ticket, end) => QueryNotFound(s, s', ticket, end)
      case OverwriteStep(ticket, i) => Overwrite(s, s', ticket, i)
      case RemoveStep(ticket, i, end) => Remove(s, s', ticket, i, end)
      case RemoveNotFoundStep(ticket, end) => RemoveNotFound(s, s', ticket, end)
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
      case QueryFoundStep(ticket, i) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case QueryNotFoundStep(ticket, end) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case OverwriteStep(ticket, i) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case RemoveStep(ticket, i, end) => {
        assume LeftShift_PartialState(
          fuse_seq(x.table, z.table),
          fuse_seq(y.table, z.table),
          RobinHood.LeftShift(i, end));
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      case RemoveNotFoundStep(ticket, end) => {
        assert UpdateStep(add(x, z), add(y, z), step);
      }
      /*case ProcessInsertTicketStep(insert_ticket) => {
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
      }*/
    }
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
}
