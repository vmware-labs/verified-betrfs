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
    && v.resource == oneRowResource(k as nat, Info(v.entry, Free))
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

  predicate method shouldHashGoBefore(search_h: uint32, slot_h: uint32, slot_idx: uint32) 
    ensures shouldHashGoBefore(search_h, slot_h, slot_idx) == ShouldHashGoBefore(search_h as int, slot_h as int, slot_idx as int)
  {
    || search_h < slot_h <= slot_idx // normal case
    || slot_h <= slot_idx < search_h // search_h wraps around the end of array
    || slot_idx < search_h < slot_h// search_h, slot_h wrap around the end of array
  }

  function method getNextIndex(slot_idx: uint32) : uint32
    requires slot_idx < FixedSizeImpl()
  {
    if slot_idx == FixedSizeImpl() - 1 then 0 else slot_idx + 1
  }

  function DistanceToSlot(src: uint32, dst: uint32) : nat
    requires src < FixedSizeImpl()
    requires dst < FixedSizeImpl()
  {
    if src >= dst
      then (dst as int - src as int + FixedSize() as int)
      else (dst as int - src as int)
  }

  method doQuery(mt: MutexTable, input: Ifc.Input, rid: int,  /*ghost*/ linear in_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.QueryInput?
    requires isInputResource(in_r, rid, input)
    ensures out_r == ARS.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key := input.key;
    var hash_idx := hash(key);
    var slot_idx := hash_idx;
    linear var r := in_r;

    linear var row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx]);
    linear var Value(entry, row_r) := row;
    r := ARS.join(r, row_r);

    ghost var r1 := oneRowResource(hash_idx as nat, Info(entry, Querying(rid, key)));
    assert UpdateStep(r, r1, ProcessQueryTicketStep(query_ticket)); // observe
    r := easy_transform(r, r1);

    while true 
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant resourceHasSingleRow(r, slot_idx as nat, entry, Querying(rid, key));
      decreases DistanceToSlot(slot_idx, hash_idx)
    {
      var query_not_found := false;

      match entry {
        case Empty => {
          query_not_found := true;
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            output := MapIfc.QueryOutput(Found(value));
            ghost var r2 := R(oneRowTable(slot_idx as nat, Info(entry, Free)), multiset{}, multiset{Stub(rid, output)}); 
            assert UpdateStep(r, r2, QueryDoneStep(slot_idx as nat)); // observe
            r := easy_transform(r, r2);

            linear var rmutex;
            r, rmutex := ARS.split(r, 
              ARS.output_stub(rid, output), 
              oneRowResource(slot_idx as nat, Info(entry, Free)));
            release(mt[slot_idx], Value(entry, rmutex));

            break;
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);
            var slot_idx' := getNextIndex(slot_idx);

            if !should_go_before {
              linear var next_row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx']);
              linear var Value(next_entry, next_row_r) := next_row;
              r := ARS.join(r, next_row_r);

              ghost var r2 := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Querying(rid, key)));
              assert UpdateStep(r, r2, QuerySkipStep(slot_idx as nat)); // observe

              r := easy_transform(r, r2);

              linear var rmutex;

              ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Querying(rid, key)));
              ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));

              r, rmutex := ARS.split(r, left, right);
              release(mt[slot_idx], Value(entry, rmutex));
              slot_idx := slot_idx';
              entry := next_entry;
              assert resourceHasSingleRow(r, slot_idx as nat, entry, Querying(rid, key));
            } else {
              query_not_found := true;
            }
          }
        }
      }

      // using a boolean to avoid copy pasting two branches that are NotFound
      if query_not_found {
        output := MapIfc.QueryOutput(NotFound);
        ghost var r2 := R(oneRowTable(slot_idx as nat, Info(entry, Free)), multiset{}, multiset{Stub(rid, output)});
        assert UpdateStep(r, r2, QueryNotFoundStep(slot_idx as nat)); // observe
        r := easy_transform(r, r2);

        linear var rmutex;
        r, rmutex := ARS.split(r,
          ARS.output_stub(rid, output),
          oneRowResource(slot_idx as nat, Info(entry, Free)));
        release(mt[slot_idx], Value(entry, rmutex));
        break;
      }

      if slot_idx == hash_idx {
        assume false; // TODO: add unreachable step in the sharded state machine
        break;
      }
    }

    out_r := r;
  }

  method doInsert(mt: MutexTable, input: Ifc.Input, rid: int, /*ghost*/ linear in_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.InsertInput?
    requires isInputResource(in_r, rid, input)
  // {

  //   // out_r := insert_ticket;
  // }

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
      output, out_r := doQuery(o, input, rid, in_r);
    } else if the_ticket.input.InsertInput? {
      assume false;
      output, out_r := doInsert(o, input, rid, in_r);
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

