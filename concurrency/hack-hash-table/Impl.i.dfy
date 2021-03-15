include "../hack-cookies/Mutex.s.dfy"
include "HTResource.i.dfy"
include "Main.s.dfy"

module HTMutex refines AbstractMutex {
  import HTResource

  type ConstType = int  // the row in the hash table protected by this mutex

  linear datatype ValueType = Value(
      entry: HTResource.Entry,
      /* ghost */ linear resource: HTResource.R)

  predicate Inv(k: ConstType, v: ValueType) {
    && v.resource.R?
    && 0 <= k < |v.resource.table|
    && v.resource.table[k].value.entry == v.entry
    && v.resource.table[k].value.state.Free?
  }
}

module Impl refines Main {
  import opened Options
  import opened NativeTypes
  import opened HTMutex
  import opened HTResource

  type Object = seq<HTMutex.Mutex>
  predicate Inv(o: Object) {
    |o| == HTResource.FixedSize()
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
  returns (o: Object)
  //requires ARS.Init(i)
  ensures Inv(o)
  {
    var remaining_r := in_r;
    o := [];
    var i:uint32 := 0;
    while i < FixedSizeImpl()
      invariant forall j:nat | j<i as int :: && o[j].constant() as int == j
    {
      ghost var splitted := Split(remaining_r, i as int);
      var remaining_r', ri := ARS.split(remaining_r, splitted.r', splitted.ri);
      remaining_r := remaining_r';
      var m := new_mutex(i as int, Value(Empty, ri));
      o := o + [m];
      i := i + 1;
    }
  }

  method call_Insert(o: Object, input: Ifc.Input, rid: int, /*ghost*/ linear insert_ticket: ARS.R)
  returns (output: Ifc.Output, linear out_r: ARS.R)
    requires forall i:nat | i < |insert_ticket.table| :: insert_ticket.table[i].None?
    requires insert_ticket.tickets == multiset { Ticket(rid, input) }
    requires insert_ticket.stubs == multiset { }
  {
  }

  method call(o: Object, input: Ifc.Input,
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
      //call_Query(o, input, rid, in_r);
    } else if the_ticket.input.InsertInput? {
      output, out_r := call_Insert(o, input, rid, in_r);
    } else if the_ticket.input.RemoveInput? {
      // call_Remove(o, input, rid, in_r);
    } else {
      assert false;
    }

    match the_ticket.input {
      case QueryInput(key) => {
        var h := hash(key);
        linear var row: HTMutex.ValueType := HTMutex.acquire(o[h]);
        linear var Value(entry_r, row_r) := row;
        linear var r := ARS.join(in_r, row_r);

      }
      case InsertInput(key, value) => { assume false; }
      case RemoveInput(key) => assume false; { }
    }

//    linear var Value(sugar, butter, pantry_object) := p;
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
//        ticket, pantry_object, CookieResource.Ticket(rid, input), num_batches);
//
//    stub := cookies;
//
//    CookieMutex.release(o, CookieMutex.Value(sugar, butter, new_pantry));
  }
}

