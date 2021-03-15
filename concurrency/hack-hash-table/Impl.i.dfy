include "../hack-cookies/Mutex.s.dfy"
include "HTResource.i.dfy"
include "Main.s.dfy"

module HTMutex refines AbstractMutex {
  import opened HTResource

  type ConstType = int  // the row in the hash table protected by this mutex

  linear datatype ValueType = Value(
      entry: HTResource.Entry,
      /* ghost */ linear resource: HTResource.R)

  predicate Inv(k: ConstType, v: ValueType) {
    && 0 <= k < FixedSize()
    && v.resource == singletonEntry(k as nat, Info(v.entry, Free))
  }
}

module Impl refines Main {
  import opened Options
  import opened NativeTypes
  import opened HTMutex
  import opened HTResource
  import opened KeyValueType

  type MutexTable = seq<HTMutex.Mutex>
  predicate Inv(o: MutexTable) {
    && |o| == HTResource.FixedSize()
    && (forall i: nat | i < |o| :: o[i].constant() == i)
  }

  predicate Init(s: ARS.R) {
    && s.R?
    && (forall i | 0 < i < |s.table| :: s.table[i] == Some(Info(Empty, Free)))
    && s.tickets == multiset{}
    && s.stubs == multiset{}
  }

  datatype Splitted = Splitted(r':ARS.R, ri:ARS.R)

  function Split(r:ARS.R, i:nat) : Splitted
    requires r.R?;
    requires r.tickets == multiset{}
    requires r.stubs == multiset{}
  {
    var r' := R(seq(|r.table|, (j) requires 0<=j<|r.table| => if j!=i then r.table[j] else None), multiset{}, multiset{});
    var ri := R(seq(|r.table|, (j) requires 0<=j<|r.table| => if j==i then r.table[j] else None), multiset{}, multiset{});
    Splitted(r', ri)
  }

  method init(linear in_r: ARS.R)
  returns (o: MutexTable, linear out_r: ARS.R)
  // requires ARS.Init(i)
  ensures Inv(o)
  ensures out_r == unit()
  {
    linear var remaining_r := in_r;
    o := [];
    var i:uint32 := 0;
    while i < FixedSizeImpl()
      invariant i as int == |o| <= FixedSize()
      invariant forall j:nat | j<i as int :: && o[j].constant() as int == j
      invariant remaining_r.R?
      invariant remaining_r.tickets == multiset{}
      invariant remaining_r.stubs == multiset{} 
      invariant forall k:nat | k < i as int :: remaining_r.table[k].None?
      invariant forall l:nat | i as int <= l < |remaining_r.table| :: remaining_r.table[l] == Some(Info(Empty, Free))
    {
      ghost var splitted := Split(remaining_r, i as int);
      linear var ri;
      remaining_r, ri := ARS.split(remaining_r, splitted.r', splitted.ri);
      var m := new_mutex(i as int, Value(Empty, ri));
      o := o + [m];
      i := i + 1;
    }

    out_r := remaining_r;

    assert forall i:nat | i < FixedSize() :: out_r.table[i].None?;
    assert out_r == unit();
  }

  method callQuery(mt: MutexTable, input: Ifc.Input, rid: int, /*ghost*/ linear query_ticket_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.QueryInput?
    requires query_ticket_r.R?
    requires forall i:nat | i < |query_ticket_r.table| :: query_ticket_r.table[i].None?
    requires query_ticket_r.tickets == multiset { Ticket(rid, input) }
    requires query_ticket_r.stubs == multiset { }
    // ensures out_r == ARS.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key := input.key;
    var h := hash(key);
    linear var row: HTMutex.ValueType := HTMutex.acquire(mt[h]);

    linear var Value(entry, row_r) := row;
    linear var r := ARS.join(query_ticket_r, row_r);
    ghost var r1 := singletonEntry(h as nat, Info(entry, Querying(query_ticket.rid, query_ticket.input.key)));
    assert UpdateStep(r, r1, ProcessQueryTicketStep(query_ticket)); // observe
    r := easy_transform(r, r1);

    if entry.Empty? {
      output := MapIfc.QueryOutput(NotFound);
      ghost var stub := Stub(rid, output);
      ghost var r2 := R(singletonTable(h as nat, Info(entry, Free)), multiset{}, multiset{stub}); 
      assert UpdateStep(r, r2, QueryNotFoundStep(h as nat)); // observe
      r := easy_transform(r, r2);

      linear var rmutex;

      ghost var left := ARS.output_stub(rid, output);
      ghost var right := singletonEntry(h as nat, Info(entry, Free));

      r, rmutex := ARS.split(r, left, right);
      release(mt[h], Value(entry, rmutex));

      assert r == ARS.output_stub(rid, output);
    }

    out_r := r;
  }

  method call_Insert(o: MutexTable, input: Ifc.Input, rid: int, /*ghost*/ linear insert_ticket: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires forall i:nat | i < |insert_ticket.table| :: insert_ticket.table[i].None?
    requires insert_ticket.tickets == multiset { Ticket(rid, input) }
    requires insert_ticket.stubs == multiset { }
  {
    out_r := insert_ticket;
  }

  method call(o: MutexTable, input: Ifc.Input,
      rid: int, linear in_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
  //requires Inv(o)
  //requires ticket == ARS.input_ticket(rid, key)
  ensures out_r == ARS.output_stub(rid, output)
  {
    // Find the ticket.
    assert |in_r.tickets| == 1;
    var the_ticket :| the_ticket in in_r.tickets;

    if the_ticket.input.QueryInput? {
      output, out_r := callQuery(o, input, rid, in_r);
    } else if the_ticket.input.InsertInput? {
      assume false;
      output, out_r := call_Insert(o, input, rid, in_r);
    } else if the_ticket.input.RemoveInput? {
      assume false;
      out_r := in_r;
      // call_Remove(o, input, rid, in_r);
    } else {
      out_r := in_r;
      assert false;
    }

//    linear var Value(sugar, butter, pantry_MutexTable) := p;
//
//    sugar := sugar + input.sugar;
//    butter := butter + input.butter;
//
//    var num_batches := if sugar < butter then sugar else butter;
//
//    sugar := sugar - num_batches;
//    butter := butter - num_batches;
//
//    output := Ifc.Output(num_batches * 6);
//
//    linear var cookies, new_pantry := CookieResource.do_tr( // ghost
//        ticket, pantry_MutexTable, CookieResource.Ticket(rid, input), num_batches);
//
//    stub := cookies;
//
//    CookieMutex.release(o, CookieMutex.Value(sugar, butter, new_pantry));
  }
}

