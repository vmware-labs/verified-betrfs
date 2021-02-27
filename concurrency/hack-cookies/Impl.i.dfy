// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "Mutex.s.dfy"
include "CookieResource.i.dfy"
include "Main.s.dfy"

module CookieMutex refines AbstractMutex {
  import CookieResource

  type ConstType = int // ignored

  linear datatype ValueType = Value(
      sugar: nat,
      butter: nat,
      linear pantry_object: CookieResource.R)

  predicate Inv(k: ConstType, v: ValueType) {
    && v.pantry_object.butter == v.butter
    && v.pantry_object.sugar == v.sugar
  }
}

module Impl refines Main {
  import CookieMutex
  import CookieResource

  type Object = CookieMutex.Mutex
  predicate Inv(o: Object) {
    true
  }

  method init(linear i: ARS.R)
  returns (o: Object)
  //requires ARS.Init(i)
  ensures Inv(o)
  {
    o := CookieMutex.new_mutex(0, CookieMutex.Value(0, 0, i));
  }

  method call(o: Object, input: Ifc.Input,
      rid: int, linear ticket: ARS.R)
  returns (output: Ifc.Output, linear stub: ARS.R)
  //requires Inv(o)
  //requires ticket == ARS.input_ticket(rid, key)
  ensures stub == ARS.output_stub(rid, output)
  {
    linear var p: CookieMutex.ValueType := CookieMutex.acquire(o);

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
