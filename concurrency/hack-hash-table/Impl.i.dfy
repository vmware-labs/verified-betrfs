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
    && v.resource == singleEntryResource(k as nat, Info(v.entry, Free))
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

  method queryNotFound(mt: MutexTable, rid: int, pos: uint32, key: uint64, /*ghost*/ linear r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires pos as nat < FixedSize()
    requires r == singleEntryResource(pos as nat, Info(Empty, Querying(rid, key)))
    ensures out_r == R(unitTable(), multiset{}, multiset{ Stub(rid, output) })
    ensures Inv(mt)
{
    output := MapIfc.QueryOutput(NotFound);
    ghost var stub := Stub(rid, output);
    ghost var r2 := R(singleEntryTable(pos as nat, Info(Empty, Free)), multiset{}, multiset{stub});

    assert QueryNotFound(r, r2, pos as nat);
    assert UpdateStep(r, r2, QueryNotFoundStep(pos as nat)); // observe

    linear var r := easy_transform(r, r2);
    linear var rmutex;

    ghost var left := ARS.output_stub(rid, output);
    ghost var right := singleEntryResource(pos as nat, Info(Empty, Free));

    out_r, rmutex := ARS.split(r, left, right);
    release(mt[pos], Value(Empty, rmutex));
  }

  method QueryDone(mt: MutexTable, rid: int, pos: uint32, key: uint64, value: Value , /*ghost*/ linear r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires pos as nat < FixedSize()
    requires r == singleEntryResource(pos as nat, Info(Full(KV(key, value)), Querying(rid, key)))
    ensures out_r == R(unitTable(), multiset{}, multiset{ Stub(rid, output) })
    ensures Inv(mt)
{
    output := MapIfc.QueryOutput(Found(value));
    var entry := Full(KV(key, value));
    ghost var stub := Stub(rid, output);
    ghost var r2 := R(singleEntryTable(pos as nat, Info(entry, Free)), multiset{}, multiset{stub}); 
    assert UpdateStep(r, r2, QueryDoneStep(pos as nat)); // observe

    linear var r := easy_transform(r, r2);
    linear var rmutex;

    ghost var left := ARS.output_stub(rid, output);
    ghost var right := singleEntryResource(pos as nat, Info(entry, Free));

    out_r, rmutex := ARS.split(r, left, right);
    release(mt[pos], Value(entry, rmutex));
  }

  predicate method shouldHashGoBefore(search_h: uint32, slot_h: uint32, slot_idx: uint32) 
    // ensures ShouldHashGoBefore(search_h as int, slot_h as int, slot_idx as int)
  {
    || search_h < slot_h <= slot_idx // normal case
    || slot_h <= slot_idx < search_h // search_h wraps around the end of array
    || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  }

  method callQuery(mt: MutexTable, input: Ifc.Input, rid: int,  /*ghost*/ linear in_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.QueryInput?
    requires in_r.R?
    requires forall i:nat | i < |in_r.table| :: in_r.table[i].None?
    requires in_r.tickets == multiset { Ticket(rid, input) }
    requires in_r.stubs == multiset { }
    // ensures out_r == ARS.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key := input.key;
    var hash_idx := hash(key);
    var slot_idx := hash_idx;
    linear var r := in_r;

    while true 
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant slot_idx == hash_idx ==> r == in_r;
      // invariant (slot_idx != hash_idx) ==> 
      //   resourceHasSingleEntry(r, slot_idx as nat, Querying(rid, key));
      decreases 
      if slot_idx >= hash_idx
        then (hash_idx as int - slot_idx as int + FixedSize() as int)
        else (hash_idx as int - slot_idx as int)
    {
      linear var row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx]);
      linear var Value(entry, row_r) := row;
      r := ARS.join(r, row_r);

      if slot_idx == hash_idx {
        ghost var r1 := singleEntryResource(hash_idx as nat, Info(entry, Querying(rid, key)));
        assert UpdateStep(r, r1, ProcessQueryTicketStep(query_ticket)); // observe
        r := easy_transform(r, r1);
      } else {
        // assert (slot_idx != hash_idx) ==> 
        // resourceHasSingleEntry(r, slot_idx as nat, Querying(rid, key));
        // assert resourceHasSingleEntry(r, slot_idx as nat, Querying(rid, key));
        assume resourceHasSingleEntry(r, slot_idx as nat, Querying(rid, key));
      }

      match entry {
        case Empty => {
          output, r := queryNotFound(mt, rid, slot_idx, key, r);
          break;
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            output, r := QueryDone(mt, rid, slot_idx, key, value , r);
            break;
          } else {
            
          }
        }
      }

      if slot_idx == FixedSizeImpl() - 1 {
        slot_idx := 0;
      } else {
        slot_idx := slot_idx + 1;
      }

      // assume resourceHasSingleEntry(r, slot_idx as nat, Querying(rid, key));

      if slot_idx == hash_idx {
        break;
      }
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
  }
}

