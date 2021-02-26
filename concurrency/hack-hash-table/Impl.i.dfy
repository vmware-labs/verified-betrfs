include "../hack-cookies/Mutex.s.dfy"
include "HTResource.i.dfy"
include "Main.s.dfy"

module HTMutex refines AbstractMutex {
  import HTResource

  type ConstType = int  // the row in the hash table protected by this mutex

  linear datatype ValueType = Value(
      entry: HTResource.Entry,
      linear resource: HTResource.R)

  predicate Inv(k: ConstType, v: ValueType) {
    && v.resource.R?
    && 0 <= k < |v.resource.table|
    && v.resource.table[k].value.entry == v.entry
    && v.resource.table[k].value.state.Free?
  }
}

module Impl refines Main {
  import HTMutex
  import HTResource

  type Object = seq<HTMutex.Mutex>
  predicate Inv(o: Object) {
    |o| == HTResource.FixedSize()
  }

  predicate Init(s: R) {
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
    o := []
    var i:uint32 := 0;
    while i < FixedSize()
      invariant forall j | 0<=j<i :: && o[j].constant() == j
    {
      ghost var splitted := Split(remaining_r, i);
      var remaining_r', ri := ARS.split(remaining_r, splitted.r', splitted.ri);
      remaining_r := remaining_r';
      var m := new_mutex(i, Value(Free, ri));
      o := o + [m];
      i := i + 1;
    }
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

    match the_ticket.input {
      case QueryInput(key) => {
        var h := hash(something);
        linear var row: HTMutex.ValueType := HTMutex.acquire(o[h]);
        linear var ValueType(entry_r, row_r) := row;
        linear var r := ARS.join(in_r, row_r);

      }
      case InsertInput(key) => { assume false; }
      case RemoveInput(key) => assume false; { }
    }

    HTResource.(


    linear var Value(sugar, butter, pantry_object) := p;

    sugar := sugar + input.sugar;
    butter := butter + input.butter;

    var num_batches := if sugar < butter then sugar else butter;

    sugar := sugar - num_batches;
    butter := butter - num_batches;

    output := Ifc.Output(num_batches * 6);

    linear var cookies, new_pantry := CookieResource.do_tr( // ghost
        ticket, pantry_object, CookieResource.Ticket(rid, input), num_batches);

    stub := cookies;

    CookieMutex.release(o, CookieMutex.Value(sugar, butter, new_pantry));
  }
  
}

