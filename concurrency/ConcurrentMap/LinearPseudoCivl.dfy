// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "../../lib/Base/Option.s.dfy"

module LinearPseudoCivl {
  import opened Options

  linear datatype Phase = Phase(x: int) // TODO make opaque
  {
    predicate is_open()
  }

  linear datatype Block = Block(x: int) // TODO make opaque

  linear datatype Tid = Tid(x: int) // TODO make opaque

  linear datatype Mutex<V> = Mutex(x: int) // TODO make opaque
  {
    function {:axiom} lock(b: Block) : Option<Tid>

    function {:axiom} value(b: Block) : V

    // right-mover
    linear method {:axiom} Acq(shared b: Block, shared tid:Tid, linear p:Phase)
    returns (linear m' : Mutex, linear p' : Phase)
    requires p.is_open()
    ensures p'.is_open()
    ensures lock(b) == None
    ensures m'.lock(b) == Some(tid)

    // left-mover
    method {:axiom} Rel(linear b: Block, shared tid:Tid, linear p:Phase)
    returns (m' : Mutex<V>, p' : Phase)
    requires lock(b) == Some(tid)
    ensures m'.lock(b) == None
    ensures !p'.is_open()

    method {:axiom} Read(shared b: Block, shared tid:Tid) returns (v: V)
    requires lock(b) == Some(tid)
    ensures v == value(b)

    method {:axiom} Write(linear b: Block, shared tid:Tid, v: V)
    returns (m' : Mutex<V>)
    requires lock(b) == Some(tid)
    ensures v == m'.value(b)
  }

  // TODO acquired locks need to be preserved
  method do_yield(linear b: Block, linear p: Phase)
  returns (linear b': Block, linear p': Phase)
}
