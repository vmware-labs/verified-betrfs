// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Base/Option.s.dfy"

module PseudoCivl {
  import opened Options

  linear datatype Tid = Tid // TODO make opaque

  linear datatype Phase = Phase(x: int) // TODO make opaque
  {
    predicate is_rising()
    predicate is_falling() { !is_rising() }
  }

  class Mutex<V> {
    function {:axiom} lock() : Option<Tid>
    reads this

    function {:axiom} value() : V
    reads this

    // right-mover
    method {:axiom} Acq(shared tid:Tid, linear p:Phase)
    returns (linear p': Phase)
    modifies this
    requires p.is_rising()
    ensures p'.is_rising()
    ensures old(lock()) == None
    ensures lock() == Some(tid)
    ensures value() == old(value())

    // left-mover
    method {:axiom} Rel(shared tid:Tid, linear p:Phase)
    returns (linear p' : Phase)
    modifies this
    requires lock() == Some(tid)
    ensures lock() == None
    ensures value() == old(value())

    method {:axiom} Read(shared tid:Tid) returns (v: V)
    requires lock() == Some(tid)
    ensures v == value()

    method {:axiom} Write(shared tid:Tid, v: V)
    modifies this
    requires lock() == Some(tid)
    ensures v == value()
  }

  function arbitrary_objects(): set<object>

  method do_yield(linear p:Phase)
  returns (linear p':Phase)
  modifies arbitrary_objects()
  ensures p'.is_rising()
  //modifies all Mutex objects / all objects? // ?
  //modifies *


  datatype Source<G, L> = Source(x: int) // TODO make opaque
  {
    function global() : G
    function local() : L
  }
}
