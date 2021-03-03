// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

module CookieMutex refines AbstractMutex {
  import CookieResources

  datatype ConstType = int // ignored

  linear datatype ValueType = Value(
      sugar: nat,
      butter: nat,
      ghost linear pantry_object: CookieResources.R)

  predicate Inv(k: ConstType, v: ValueType) {
    && v.pantry_object == CookieResources.Pantry(v.sugar, v.butter)
  }
}

module Impl refines Main(CookieResources) {
  import CookieMutex

  type Object = CookieMutex.Mutex
  predicate Inv(o: Object) {
    true
  }

  method init(ghost linear i: ARS.R)
  returns (o: Object)
  requires ARS.Init(multiset{i})
  ensures Inv(o)
  {
    assert i == Pantry(0, 0);
    o := new_mutex(0, CookieMutex.Value(0, 0, i));
  }

  method call(o: Object, input: Input,
      ghost rid: int, ghost linear ticket: ARS.R)
  returns (output: Output, ghost linear stub: ARS.R)
  requires Inv(o)
  requires ticket == ARS.input_ticket(rid, key)
  ensures stub == ARS.output_stub(rid, stub)
  {
    var p := CookieMutex.acquire(o);

    linear var Value(sugar, butter, pantry_object) := p;

    sugar := sugar + input.sugar;
    butter := butter + input.butter;

    var num_batches := min(sugar, butter);

    sugar := sugar - num_batches;
    butter := butter - num_batches;

    output := Output(num_batches * 6);

    linear var cookies, new_pantry := do_transform( // ghost
        [ ticket, pantry ],
        [ Cookies(rid, num_batches * 6), Pantry(sugar, butter) ]);

    stub := cookies;

    CookieMutex.release(Value(sugar, butter, new_pantry));
  }
  
}
