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

    ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Querying(rid, key)));
    r := easy_transform_step(r, r', ProcessQueryTicketStep(query_ticket));

    while true 
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Querying(rid, key)));
      decreases DistanceToSlot(slot_idx, hash_idx)
    {
      var step;

      match entry {
        case Empty => {
          output := MapIfc.QueryOutput(NotFound);
          step := QueryNotFoundStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            step := QueryDoneStep(slot_idx as nat);
            output := MapIfc.QueryOutput(Found(value));
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);

            if !should_go_before {
              step := QuerySkipStep(slot_idx as nat);
            } else {
              output := MapIfc.QueryOutput(NotFound);
              step := QueryNotFoundStep(slot_idx as nat);
            }
          }
        }
      }

      if !step.QuerySkipStep? {
        // should be QueryNotFoundStep/QueryDoneStep
        r' := R(oneRowTable(slot_idx as nat, Info(entry, Free)), multiset{}, multiset{Stub(rid, output)}); 
        r := easy_transform_step(r, r', step);

        linear var rmutex;
        r, rmutex := ARS.split(r, 
          ARS.output_stub(rid, output), 
          oneRowResource(slot_idx as nat, Info(entry, Free)));
        release(mt[slot_idx], Value(entry, rmutex));
        break;
      }

      var slot_idx' := getNextIndex(slot_idx);

      linear var next_row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx']);
      linear var Value(next_entry, next_row_r) := next_row;
      r := ARS.join(r, next_row_r);

      if slot_idx' == hash_idx {
        output := MapIfc.QueryOutput(NotFound);

        r' := R(
          twoRowsTable(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Free)),
          multiset{},
          multiset{ Stub(rid, output) });

        // Take everything apart exactly as in QueryDone/QueryNotFound above
        step := QueryFullHashTableStep(slot_idx as nat);
        r := easy_transform_step(r, r', step);

        linear var rmutex;
        ghost var left := R(
          oneRowTable(slot_idx' as nat, Info(next_entry, Free)),
          multiset{},
          multiset{ Stub(rid, output) });
        ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));

        r, rmutex := ARS.split(r, left, right);
        release(mt[slot_idx], Value(entry, rmutex));

        r, rmutex := ARS.split(r, 
          ARS.output_stub(rid, output), 
          oneRowResource(slot_idx' as nat, Info(next_entry, Free)));
        release(mt[slot_idx'], Value(next_entry, rmutex));
        break;
      }

      r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Querying(rid, key)));
      r := easy_transform_step(r, r', step);

      linear var rmutex;
      ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Querying(rid, key)));
      ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));
      r, rmutex := ARS.split(r, left, right);
      release(mt[slot_idx], Value(entry, rmutex));

      slot_idx := slot_idx';
      entry := next_entry;
    }

    out_r := r;
  }

  method doInsert(mt: MutexTable, input: Ifc.Input, rid: int, /*ghost*/ linear in_r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.InsertInput?
    requires isInputResource(in_r, rid, input)
    ensures out_r == ARS.output_stub(rid, output)
  {
    var query_ticket := Ticket(rid, input);
    var key, inital_key := input.key, input.key;
    var kv := KV(key, input.value);
    output := MapIfc.InsertOutput;

    var hash_idx := hash(key);
    var initial_hash_idx := hash_idx;
    var slot_idx := hash_idx;

    linear var r := in_r;
    linear var row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx]);
    linear var Value(entry, row_r) := row;
    r := ARS.join(r, row_r);

    ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Inserting(rid, kv, inital_key)));
    r := easy_transform_step(r, r', ProcessInsertTicketStep(query_ticket));

    while true 
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Inserting(rid, kv, inital_key)))
      invariant kv.key == key
      invariant hash_idx == hash(key)
      decreases DistanceToSlot(slot_idx, initial_hash_idx)
    {
      var step, new_kv;

      match entry {
        case Empty => {
          step := InsertDoneStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          new_kv := KV(entry_key, value);
          if entry_key == key {
            step := InsertUpdateStep(slot_idx as nat);
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);
            if !should_go_before {
              step := InsertSkipStep(slot_idx as nat);
            } else {
              step := InsertSwapStep(slot_idx as nat);
            }
          }
        }
      }

      if step.InsertDoneStep? || step.InsertUpdateStep? {
        r' := R(oneRowTable(slot_idx as nat, Info(Full(kv), Free)), multiset{}, multiset{Stub(rid, output)});
        r := easy_transform_step(r, r', step);

        linear var rmutex;
        r, rmutex := ARS.split(r, ARS.output_stub(rid, output), 
          oneRowResource(slot_idx as nat, Info(Full(kv), Free)));
        release(mt[slot_idx], Value(Full(kv), rmutex));
        break;
      }

      var slot_idx' := getNextIndex(slot_idx);

      if slot_idx' == initial_hash_idx {
        // why do we have code here if this is supposed to be unreachable?
        // shouldn't we just throw an exception?
        r' := R(oneRowTable(slot_idx as nat, Info(Full(new_kv), Free)), multiset{}, multiset{Stub(rid, output)});
        r := easy_transform_step(r, r', InsertFullHashTableStep(slot_idx as nat));

        linear var rmutex;
        r, rmutex := ARS.split(r, ARS.output_stub(rid, output), 
          oneRowResource(slot_idx as nat, Info(Full(new_kv), Free)));
        release(mt[slot_idx], Value(Full(new_kv), rmutex));
        break;
      }

      linear var next_row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx']);
      linear var Value(next_entry, next_row_r) := next_row;
      r := ARS.join(r, next_row_r);

      if step.InsertSwapStep? {
        entry := Full(kv);
        kv := new_kv;
        key := new_kv.key;
      }
  
      r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Inserting(rid, kv, inital_key)));
      r := easy_transform_step(r, r', step);

      linear var rmutex;
      ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Inserting(rid, kv, inital_key)));
      ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));

      r, rmutex := ARS.split(r, left, right);
      release(mt[slot_idx], Value(entry, rmutex));
 
      slot_idx := slot_idx';
      entry := next_entry;
      hash_idx := hash(key);
    }

    out_r := r;
  }

  method doRemoveTidy(mt: MutexTable, rid: int, 
    slot_idx: uint32,
    hash_idx: uint32,
    inital_key: Key,
    entry: Entry,
    next_entry: Entry,
    /*ghost*/ linear r: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires TidyEnabled(r, slot_idx as nat)
    requires r == twoRowsResource(slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key)), NextPos(slot_idx as nat), Info(next_entry, Free));
    requires 0 <= slot_idx < FixedSizeImpl()
    requires 0 <= hash_idx < FixedSizeImpl()
    ensures out_r == ARS.output_stub(rid, output)
  {
    var slot_idx := slot_idx;
    var next_entry := next_entry;
    linear var r := r;
    while true
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl()
      invariant r == twoRowsResource(slot_idx as nat, Info(Empty, RemoveTidying(rid, inital_key)), NextPos(slot_idx as nat), Info(next_entry, Free))
      decreases DistanceToSlot(slot_idx, hash_idx)
    {
      var slot_idx' := getNextIndex(slot_idx);

      if next_entry.Empty? || hash(next_entry.kv.key) == slot_idx' {
        assert DoneTidying(r, slot_idx as nat);
        break;
      }

      ghost var r' := twoRowsResource(slot_idx as nat, Info(next_entry, Free), slot_idx' as nat, Info(Empty, RemoveTidying(rid, inital_key)));
      r := easy_transform_step(r, r', RemoveTidyStep(slot_idx as nat));

      linear var rmutex;
      ghost var left := oneRowResource(slot_idx' as nat, Info(Empty, RemoveTidying(rid, inital_key)));
      ghost var right := oneRowResource(slot_idx as nat, Info(next_entry, Free));

      r, rmutex := ARS.split(r, left, right);
      release(mt[slot_idx], Value(next_entry, rmutex));

      slot_idx := slot_idx';
      slot_idx' := getNextIndex(slot_idx);

      linear var next_row := HTMutex.acquire(mt[slot_idx']);
      linear var Value(next_entry', next_row_r) := next_row;
      next_entry := next_entry';
      r := ARS.join(r, next_row_r);

      if slot_idx == hash_idx {
        assume false; // TODO: add unreachable step in the sharded state machine
        break;
      }
    }

    assert DoneTidying(r, slot_idx as nat);

    var slot_idx' := getNextIndex(slot_idx);
    output := MapIfc.RemoveOutput(true);
    ghost var r' := R(
      twoRowsTable(slot_idx as nat, Info(Empty, Free), slot_idx' as nat, Info(next_entry, Free)),
      multiset{},
      multiset{ Stub(rid, output) }
    );

    var step := RemoveDoneStep(slot_idx as nat);
    r := easy_transform_step(r, r', step);

    linear var rmutex;
    ghost var left := R(
      oneRowTable(slot_idx' as nat, Info(next_entry, Free)),
      multiset{},
      multiset{ Stub(rid, output) });
    ghost var right := oneRowResource(slot_idx as nat, Info(Empty, Free));

    r, rmutex := ARS.split(r, left, right);
    release(mt[slot_idx], Value(Empty, rmutex));

    r, rmutex := ARS.split(r, 
      ARS.output_stub(rid, output), 
      oneRowResource(slot_idx' as nat, Info(next_entry, Free)));
    release(mt[slot_idx'], Value(next_entry, rmutex));

    out_r := r;
  }

  method doRemove(mt: MutexTable, input: Ifc.Input, rid: int, /*ghost*/ linear in_r: ARS.R)
    returns (output: Ifc.Output, linear out_r: ARS.R)
    requires Inv(mt)
    requires input.RemoveInput?
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

    var slot_idx': uint32 ;

    ghost var r' := oneRowResource(hash_idx as nat, Info(entry, Removing(rid, key)));
    var step : Step := ProcessRemoveTicketStep(query_ticket);
    r := easy_transform_step(r, r', step);

    while true 
      invariant Inv(mt);
      invariant 0 <= slot_idx < FixedSizeImpl();
      invariant r == oneRowResource(slot_idx as nat, Info(entry, Removing(rid, key)))
      invariant step.RemoveNotFoundStep? ==> 
        (entry.Full? && shouldHashGoBefore(hash_idx, hash(entry.kv.key), slot_idx))
      invariant step.RemoveTidyStep? ==> (
        && TidyEnabled(r, slot_idx as nat)
        && KnowRowIsFree(r, NextPos(slot_idx as nat)))
      decreases DistanceToSlot(slot_idx, hash_idx)
    {
      match entry {
        case Empty => {
          step := RemoveNotFoundStep(slot_idx as nat);
        }
        case Full(KV(entry_key, value)) => {
          if entry_key == key {
            step := RemoveFoundItStep(slot_idx as nat);
          } else {
            var should_go_before := shouldHashGoBefore(hash_idx, hash(entry_key), slot_idx);

            if !should_go_before {
              step := RemoveSkipStep(slot_idx as nat);
            } else {
              step := RemoveNotFoundStep(slot_idx as nat);
            }
          }
        }
      }

      if step.RemoveNotFoundStep? {
        break;
      }

      var slot_idx' := getNextIndex(slot_idx);
      linear var next_row: HTMutex.ValueType := HTMutex.acquire(mt[slot_idx']);
      linear var Value(next_entry, next_row_r) := next_row;
      r := ARS.join(r, next_row_r);

      if step.RemoveFoundItStep? {
        r' := twoRowsResource(slot_idx as nat, Info(Empty, RemoveTidying(rid, key)), slot_idx' as nat, Info(next_entry, Free));
        r := easy_transform_step(r, r', step);
        output, r := doRemoveTidy(mt, rid, slot_idx, hash_idx, key, entry, next_entry, r);
        break;
      } else {
        r' := twoRowsResource(slot_idx as nat, Info(entry, Free), slot_idx' as nat, Info(next_entry, Removing(rid, key)));
        r := easy_transform_step(r, r', step);

        linear var rmutex;
        ghost var left := oneRowResource(slot_idx' as nat, Info(next_entry, Removing(rid, key)));
        ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));
        r, rmutex := ARS.split(r, left, right);
        release(mt[slot_idx], Value(entry, rmutex));

        slot_idx := slot_idx';
        entry := next_entry;
      }

      if slot_idx == hash_idx {
        assume false; // TODO: add unreachable step in the sharded state machine
        break;
      }
    }

    if step.RemoveNotFoundStep? {
      output := MapIfc.RemoveOutput(false);
      r' := R(oneRowTable(slot_idx as nat, Info(entry, Free)), multiset{}, multiset{Stub(rid, output)}); 
      r := easy_transform_step(r, r', step);

      linear var rmutex;
      ghost var left := ARS.output_stub(rid, output);
      ghost var right := oneRowResource(slot_idx as nat, Info(entry, Free));
      r, rmutex := ARS.split(r, left, right);
      release(mt[slot_idx], Value(entry, rmutex));
    }

    out_r := r;
  }

  method call(o: MutexTable, input: Ifc.Input,
      rid: int, linear in_r: ARS.R)
    returns (output: Ifc.Output, linear out_r: ARS.R)
  // requires Inv(o)
  // requires ticket == ARS.input_ticket(rid, key)
    ensures out_r == ARS.output_stub(rid, output)
  {
    // Find the ticket.
    assert |in_r.tickets| == 1;
    var the_ticket :| the_ticket in in_r.tickets;

    if the_ticket.input.QueryInput? {
      output, out_r := doQuery(o, input, rid, in_r);
    } else if the_ticket.input.InsertInput? {
      output, out_r := doInsert(o, input, rid, in_r);
    } else if the_ticket.input.RemoveInput? {
      output, out_r := doRemove(o, input, rid, in_r);
    } else {
      out_r := in_r;
      assert false;
    }
  }
}

