// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Mutex.dfy"

module StateObjects {
  datatype StateObject =
    | Ticket
    | Stub(n: int)
    | IncTicket
    | IncStub
    | CurValue(n: int)

  // Allowed transforms:
  //
  // Ticket -> IncTicket, IncTicket, CurValue(0)
  // IncTicket, CurValue(n) -> IncStub, CurValue(n+1)
  // IncStub, IncStub, CurValue(n) -> Stub(n)

  method transform_init(linear t: StateObject)
  returns (linear u: StateObject, linear v: StateObject, linear w: StateObject)
  requires t == Ticket
  ensures u == IncTicket
  ensures v == IncTicket
  ensures w == CurValue(0)

  method transform_inc(linear t: StateObject, linear u: StateObject)
  returns (linear v: StateObject, linear w: StateObject)
  requires t == IncTicket
  requires u.CurValue?
  ensures v == IncStub
  ensures w == CurValue(u.n + 1)

  method transform_end(linear t: StateObject, linear u: StateObject, linear v: StateObject)
  returns (linear w: StateObject)
  requires t == IncStub
  requires u == IncStub
  requires v.CurValue?
  ensures w == Stub(v.n)
}

module NumMutex refines AbstractMutex {
  import opened StateObjects

  type ConstType = int

  linear datatype V = V(num: int, linear r: StateObject)

  type ValueType = V

  predicate Inv(k: ConstType, v: ValueType)
  {
    v.r == CurValue(v.num)
  }
}

module Impl {
  import opened StateObjects
  import opened NumMutex

  method inc(m: NumMutex.Mutex, linear ticket: StateObject)
  returns (linear stub: StateObject)
  requires ticket == IncTicket
  ensures stub == IncStub
  {
    linear var entry := NumMutex.acquire(m);
    linear var V(num, r) := entry;

    num := num + 1;
    linear var r';
    stub, r' := transform_inc(ticket, r);

    linear var entry' := V(num, r');
    NumMutex.release(m, entry');
  }


  // Dafny doesn't have fork/join built-ins but if it did, this is what
  // `fork inc` and `join inc` would look like...

  type ForkHandle

  method fork_inc(m: NumMutex.Mutex, linear ticket: StateObject)
  returns (linear fh: ForkHandle)
  requires ticket == IncTicket

  method join_inc(linear fh: ForkHandle)
  returns (linear stub: StateObject)
  ensures stub == IncStub

  // end fork/join spec

  method main(linear ticket: StateObject)
  returns (n: int, linear stub: StateObject)
  requires ticket == Ticket
  ensures stub == Stub(n)     // BP: So this proves that we return a Stub for _some_ value n, and the StateMachine proves n == 2?
  {
    linear var inc_ticket1, inc_ticket2, curv := transform_init(ticket);

    var m := NumMutex.new_mutex(0, V(0, curv));

    linear var fh1 := fork_inc(m, inc_ticket1);
    linear var fh2 := fork_inc(m, inc_ticket2);

    linear var inc_stub1 := join_inc(fh1);
    linear var inc_stub2 := join_inc(fh2);

    linear var entry := NumMutex.acquire(m);      // BP: Need to release?

    linear var V(num, r) := entry;

    stub := transform_end(inc_stub1, inc_stub2, r);

    n := num;
  }
}
